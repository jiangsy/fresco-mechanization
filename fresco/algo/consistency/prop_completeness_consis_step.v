Require Import src.fresco.prop_atom_sets.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.
Require Import src.fresco.notations.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_ln.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo_decl.prop_stability.
Require Import src.fresco.algo_decl.prop_refinement.
Require Import src.fresco.algo.basic.prop_metasubst_composition.
Require Import src.fresco.algo.basic.prop_context_normalization.
Require Import src.fresco.algo.basic.prop_metasubst.
Require Import src.fresco.algo_decl.prop_precision.
Require Import src.fresco.algo.consistency.prop_consis_monotype_equiv.
Require Import src.fresco.algo.consistency.prop_soundness_consis.
Require Import src.fresco.algo.basic.prop_inc_strengthen.
Require Import src.fresco.algo.consistency.prop_precision_recovery.
Require Import src.fresco.algo.consistency.prop_consis_rename.

Set Implicit Arguments.

Require Export src.fresco.algo.consistency.prop_consis_solution.
Require Export src.fresco.algo.consistency.prop_completeness_unify.
Require Export src.fresco.algo.consistency.prop_completeness_assign.

Lemma a_flex_tvar_dec : forall Θ (β1 : atom),
  a_flex_tvar Θ β1 \/ ~ a_flex_tvar Θ β1.
Proof.
  induction Θ as [ | [x b] Θ' IHΘ ]; intros β1.
  - right. intros [Hb | [τ Hb]]; inversion Hb.
  - destruct (IHΘ β1) as [Hyes | Hno].
    { left. destruct Hyes as [Hb | [τ Hb]];
        [ left | right; exists τ ]; unfold binds in *; simpl; right; exact Hb. }
    destruct b as [ | A | Q | | τd ];
      try (destruct (β1 == x) as [-> | Hne];
           [ | right; intros [Hb | [τ Hb]];
               apply binds_cons_1 in Hb as [[Heq Hbe] | Hb];
               solve [ exfalso; auto | discriminate Hbe
                     | apply Hno; solve [ left; exact Hb
                                        | right; exists τ; exact Hb ] ] ]).
    +
      right. intros [Hb | [τ Hb]];
        apply binds_cons_1 in Hb as [[Heq Hbe] | Hb];
        solve [ discriminate Hbe
              | apply Hno; solve [ left; exact Hb
                                 | right; exists τ; exact Hb ] ].
    +
      right. intros [Hb | [τ Hb]];
        apply binds_cons_1 in Hb as [[Heq Hbe] | Hb];
        solve [ discriminate Hbe
              | apply Hno; solve [ left; exact Hb
                                 | right; exists τ; exact Hb ] ].
    +
      right. intros [Hb | [τ Hb]];
        apply binds_cons_1 in Hb as [[Heq Hbe] | Hb];
        solve [ discriminate Hbe
              | apply Hno; solve [ left; exact Hb
                                 | right; exists τ; exact Hb ] ].
    +
      left. left. left. reflexivity.
    +
      left. right. exists τd. left. reflexivity.
Qed.

Lemma a_flex_shape_dec : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  (exists β, P = pskl_var_f β /\ a_flex_tvar Θ β) \/ a_non_flex Θ P.
Proof.
  intros Θ Δ P HwfP.
  pose proof (a_wf_pskl_lc HwfP) as Hlc.
  destruct P as [ | n | β1 | Pa Pb | Pb | | Pt ];
    try (right; split; [ exact Hlc | intro Hfl; solve [ inversion Hfl ] ]).
  destruct (a_flex_tvar_dec Θ β1) as [Hf | Hnf'].
  - left. exists β1. split; [ reflexivity | exact Hf ].
  - right. split; [ exact Hlc | ].
    intro Hfl. apply Hnf'.
    inversion Hfl; subst; [ left | right; eexists ]; eassumption.
Qed.

Lemma consis_complete_close_optimal : forall Θ0 Θ1 Θ κ P1 Q α Δ Δr,
  {{ ⊢ Θ }}a ->
  α `notin` dom Θ `union` dom Θ1 `union` ftvar_in_bskl Q ->
  Δr [=] add α Δ ->
  (forall κ1, is_id_msubst κ1 ->
    κ1 ∷ ((α ~ abind_tvar) ++ Θ0) ⊑ ((α ~ abind_tvar) ++ Θ1) ->
    exists ζ, ζ ∷ ((α ~ abind_tvar) ++ Θ1) ⊑ ((α ~ abind_tvar) ++ Θ) /\
      a_inc_equiv ((α ~ abind_tvar) ++ Θ0) κ (msubst_compose ζ κ1)
        ((α ~ abind_tvar) ++ Θ) /\
      {{ ((α ~ abind_tvar) ++ Θ) ⨟ Δr ⊢ₚᵣ
        (msubst_bskl ζ (pskl_to_bskl_syn P1))
        ⊑ (bskl_to_pskl (open_bskl_wrt_bskl Q (bskl_var_f α))) }}ad) ->
  forall κ1, is_id_msubst κ1 -> κ1 ∷ Θ0 ⊑ Θ1 ->
    exists ζ, ζ ∷ Θ1 ⊑ Θ /\
      a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ /\
      {{ Θ ⨟ Δ ⊢ₚᵣ
        (msubst_bskl ζ (pskl_to_bskl_syn (pskl_all_syn (close_pskl_wrt_pskl α P1))))
        ⊑ (pskl_all_syn (bskl_to_pskl Q)) }}ad.
Proof.
  intros Θ0 Θ1 Θ κ P1 Q α Δ Δr Hwfth Hfr HΔ Hopt'.
  assert (HαΘ : α `notin` dom Θ) by (clear - Hfr; fsetdec).
  assert (HαΘ1 : α `notin` dom Θ1) by (clear - Hfr; fsetdec).
  intros κ1 Hid Hinc1.
  assert (Hinc1' : κ1 ∷ ((α ~ abind_tvar) ++ Θ0) ⊑
                     ((α ~ abind_tvar) ++ Θ1)).
  { apply (a_inc__tvar (Ξ:=nil) α Hinc1).
    apply a_decls_suffix. apply a_decls__nil. }
  destruct (Hopt' κ1 Hid Hinc1') as [ζ [Hζ [Hie Hprec]]].
  exists ζ.

  assert (Hζ' : ζ ∷ Θ1 ⊑ Θ).
  { eapply a_inc_tvar_head_inv; exact Hζ. }
  assert (Hie' : a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ).
  { eapply a_inc_equiv_tvar_head_inv; exact Hie. }
  split; [ exact Hζ' | ]. split; [ exact Hie' | ].

  assert (Hlcζ : msubst_lc ζ) by (eapply a_inc_msubst_lc; exact Hζ').
  assert (Hαζ : α `notin` dom ζ).
  { intro Hin.
    destruct (a_inc_dom_flex Hζ' Hin) as [Hb | [τ Hb]];
      apply binds_In in Hb; clear - Hb HαΘ1; fsetdec. }
  assert (Himg : forall α1 τ, In (α1, τ) ζ -> α `notin` ftvar_in_ptyp τ).
  { intros α1 τ Hin.
    pose proof (a_inc_images_ftv_dom Hζ' _ _ Hin) as Hsc.
    clear - Hsc HαΘ. fsetdec. }
  unfold ad_precise in Hprec |- *.
  rewrite bskl_to_pskl_msubst_bskl in Hprec |- *.
  rewrite bskl_to_pskl_pskl_to_bskl_syn in Hprec |- *.
  change ({{ Θ ⨟ Δ ⊢ᵣ (bskl_all_inh (pskl_to_bskl_inh
       (msubst_pskl ζ (close_pskl_wrt_pskl α P1)))) ⊳ (bskl_all_inh (pskl_to_bskl_inh (bskl_to_pskl Q))) }}ad).
  replace (pskl_to_bskl_inh (bskl_to_pskl Q)) with
    (close_bskl_wrt_bskl α (open_bskl_wrt_bskl
      (pskl_to_bskl_inh (bskl_to_pskl Q)) (bskl_var_f α))).
  2: { rewrite close_bskl_wrt_bskl_open_bskl_wrt_bskl; [reflexivity |].
       rewrite ftvar_in_bskl_inh, ftvar_bskl_to_pskl.
       clear - Hfr; fsetdec. }
  apply ad_refine_syn_close_all; [exact Hwfth | exact HαΘ | |].
  - apply msubst_pskl_ftv_avoid.
    + intros [β τ] Hin; apply (Himg β τ Hin).
    + rewrite ftvar_in_pskl_close_pskl_wrt_pskl. clear; fsetdec.
  - rewrite <- !pskl_to_bskl_inh_open.
    rewrite <- (msubst_pskl_open_lc (close_pskl_wrt_pskl α P1) Hlcζ Hαζ).
    rewrite open_pskl_wrt_pskl_close_pskl_wrt_pskl.
    rewrite <- bskl_to_pskl_open.
    eapply ad_refine_syn_delta_mono; [exact Hprec | clear - HΔ; fsetdec].
Qed.

Lemma a_inc_lookup_rigid : forall Θ0 κ Θ Δ β,
  κ ∷ Θ0 ⊑ Θ ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ Δ ⊢ₚₛ (pskl_var_f β) }}a ->
  a_non_flex Θ0 (pskl_var_f β) ->
  msubst_lookup κ β = ptyp_var_f β.
Proof.
  intros Θ0 κ Θ Δ β Hinc Hwf0 HwfP HnfP.
  apply msubst_lookup_notin.
  eapply a_inc_tvar_notin_dom;
    [ exact Hinc | exact Hwf0 | exact (a_wf_pskl_var_non_flex_tvar HwfP HnfP) ].
Qed.

Lemma a_inc_rigid_refine_inv : forall Θ0 κ Θ Δ Δ' β Q,
  κ ∷ Θ0 ⊑ Θ ->
  {{ ⊢ Θ0 }}a ->
  {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ Δ' ⊢ₚₛ (pskl_var_f β) }}a ->
  a_non_flex Θ0 (pskl_var_f β) ->
  {{ Θ ⨟ Δ ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f β))) ⊳ Q }}ad ->
  exists α, Q = bskl_var_f α.
Proof.
  intros Θ0 κ Θ Δ Δ' β Q Hinc Hwf0 Hwfth HwfP HnfP Hrs.
  simpl in Hrs. rewrite (a_inc_lookup_rigid Hinc Hwf0 HwfP HnfP) in Hrs.
  simpl in Hrs.
  assert (HbtΘ : binds β abind_tvar Θ)
    by (eapply a_inc_binds_tvar;
        [ exact Hinc | exact (a_wf_pskl_var_non_flex_tvar HwfP HnfP) ]).
  inversion Hrs; subst.
  - exists β. reflexivity.
  - match goal with
    | Hbr : binds β (abind_flex_mono_def _) Θ |- _ =>
        pose proof (binds_unique _ _ _ _ _ HbtΘ Hbr (a_wf_aenv_uniq Hwfth))
          as Hcon; discriminate
    end.
  - eexists. reflexivity.
Qed.

Lemma consis_complete_open_ctx : forall Δ Δ' α Θ0 κ Θ,
  Δ' [<=] add α Δ ->
  {{ ⊢ Θ0 }}a -> α `notin` dom Θ0 ->
  (forall β, β `in` Δ -> binds β abind_tvar Θ0) ->
  no_flex_dep Δ Θ0 -> flex_above_free Δ Θ0 ->
  κ ∷ Θ0 ⊑ Θ -> {{ ⊢ Θ }}a -> α `notin` dom Θ -> no_flex_dep Δ Θ ->
  {{ ⊢ ((α ~ abind_tvar) ++ Θ0) }}a /\
  (forall β, β `in` Δ' -> binds β abind_tvar ((α ~ abind_tvar) ++ Θ0)) /\
  no_flex_dep Δ' ((α ~ abind_tvar) ++ Θ0) /\
  flex_above_free Δ' ((α ~ abind_tvar) ++ Θ0) /\
  κ ∷ ((α ~ abind_tvar) ++ Θ0) ⊑ ((α ~ abind_tvar) ++ Θ) /\
  {{ ⊢ ((α ~ abind_tvar) ++ Θ) }}a /\
  no_flex_dep Δ' ((α ~ abind_tvar) ++ Θ).
Proof.
  intros Δ Δ' α Θ0 κ Θ HΔ' Hwf0 HαΘ0 Hrig Hnfd0 Hfaf Hinc Hwfth HαΘ Hnfdth.
  destruct (delta_inv_open_tvar Hwf0 HαΘ0 HΔ' Hrig Hnfd0 Hfaf)
    as (Hrig' & Hnfd0' & Hfaf').
  split; [ apply a_wf_aenv__tvar; [ exact HαΘ0 | exact Hwf0 ] | ].
  split; [ exact Hrig' | ]. split; [ exact Hnfd0' | ].
  split; [ exact Hfaf' | ].
  split.
  { apply (a_inc__tvar (Ξ:=nil) α Hinc).
    apply a_decls_suffix. apply a_decls__nil. }
  split; [ apply a_wf_aenv__tvar; [ exact HαΘ | exact Hwfth ] | ].
  intros β τ Hb.
  pose proof (no_flex_dep_open_tvar Hwfth Hnfdth HαΘ Hb) as Hd.
  clear - Hd HΔ'. fsetdec.
Qed.

Lemma consis_complete_core : forall Ψ Θ R' Qb,
  {{ Ψ ⨟ Θ ⊢ˢ R' ∼ Qb }}ad ->
  forall (N : atoms) Δ1 Δ2 Θ0 P0 P κ,
    (forall m', mu_lt m' (mu_consis Θ κ P0 P Θ0) -> complete_at m') ->
    {{ ⊢ Θ0 }}a ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
    (forall α, α `in` (Δ1 `union` Δ2) -> binds α abind_tvar Θ0) ->
    no_flex_dep (Δ1 `union` Δ2) Θ0 ->
    flex_above_free (Δ1 `union` Δ2) Θ0 ->
    κ ∷ Θ0 ⊑ Θ ->
    {{ ⊢ Θ }}a ->
    no_flex_dep (Δ1 `union` Δ2) Θ ->
    Ψ [=] empty ->
    R' = pskl_to_uskl (msubst_pskl κ P) ->
    a_non_flex Θ0 P ->
    a_non_flex Θ0 P0 ->
    P0 <> pskl_ghost ->
    (forall P0', P0 = pskl_univ_ghost P0' -> ~ guarded_pskl P) ->
    {{ Θ ⨟ Δ1 ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Qb }}ad ->
    {{ Θ ⨟ Δ2 ⊢ᵣₚ (msubst_pskl κ P) ⊳ (bskl_to_pskl Qb) }}ad ->
    {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Qb) }}a ->
    exists P1 Θ1,
      a_consis Δ1 Δ2 Θ0 P0 P P1 Θ1 /\
      (forall γ, γ `in` dom Θ1 -> γ `in` dom Θ0 \/ γ `notin` N) /\
      (forall κ1, is_id_msubst κ1 -> κ1 ∷ Θ0 ⊑ Θ1 ->
         exists ζ,
           ζ ∷ Θ1 ⊑ Θ /\
           a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ /\
           {{ Θ ⨟ (Δ1 `union` Δ2) ⊢ₚᵣ (msubst_bskl ζ (pskl_to_bskl_syn P1)) ⊑ (bskl_to_pskl Qb) }}ad).
Proof.
  intros Ψ Θ R' Qb Hj.
  induction Hj; intros N Δ1 Δ2 Θ0 PP0 PP κ
    IH Hwf0 HwfP0 HwfP Hrig Hnfd0 Hfaf Hinc Hwfth Hnfdth
    HΨ HeqS HnfP HnfP0 HneP0ghost Hnthg Hrs Hrp HwfQb.

  -
    destruct PP as [ | n | β1 | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    2:{
      exfalso.
      rewrite (a_inc_lookup_rigid Hinc Hwf0 HwfP HnfP) in HeqS.
      simpl in HeqS. discriminate. }

    destruct PP0 as [ | n0 | β10 | Pa0 Pb0 | Pb0 | | Pt0 ]; simpl in Hrs.
    2:{ inversion Hrs. }
    2:{
      exfalso.
      destruct (a_inc_rigid_refine_inv Hinc Hwf0 Hwfth HwfP0 HnfP0 Hrs)
        as [? HQ].
      discriminate HQ. }
    2:{ inversion Hrs. }
    2:{ inversion Hrs. }
    2:{ exfalso; apply HneP0ghost; reflexivity. }
    2:{ exfalso; apply (Hnthg Pt0 eq_refl); apply guarded_pskl__unit. }

    exists pskl_unit, Θ0. split.
    { apply a_consis__unit. }
    split; [ intros γ Hγ; left; exact Hγ | ].
    intros κ1 Hid Hinc1. exists κ.
    destruct (opt_axiom_factor Hwf0 Hid Hinc1 Hinc) as [Hout Hfact].
    split; [ exact Hout | ]. split; [ exact Hfact | ].
    cbn [pskl_to_bskl_syn msubst_bskl bskl_to_pskl].
    unfold ad_precise.
    apply consis_precise_mono_join with (A := ptyp_unit) (Qb := bskl_unit);
      [ exact Hwfth | apply mono_ptyp__unit
      | intros α0 Hα0; simpl in Hα0; clear - Hα0; fsetdec
      | apply ad_pat_consis__unit; clear; fsetdec ].

  -
    destruct PP as [ | n | β1 | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    pose proof (a_wf_pskl_var_non_flex_tvar HwfP HnfP) as Hbtδ.
    assert (Hβ1κ : β1 `notin` dom κ)
      by (eapply a_inc_tvar_notin_dom; eauto).
    rewrite (msubst_lookup_notin κ Hβ1κ) in HeqS.
    simpl in HeqS. inversion HeqS; subst α. clear HeqS.
    assert (HbtΘ : binds β1 abind_tvar Θ)
      by (eapply a_inc_binds_tvar; eauto).

    destruct PP0 as [ | n0 | β10 | Pa0 Pb0 | Pb0 | | Pt0 ]; simpl in Hrs.
    1:{ exfalso.
        inversion Hrs; subst.
        match goal with
        | Hbr : binds β1 (abind_flex_mono_def _) Θ |- _ =>
            pose proof (binds_unique _ _ _ _ _ HbtΘ Hbr (a_wf_aenv_uniq Hwfth))
              as Hcon; discriminate
        end. }
    1:{ exfalso. inversion Hrs; subst.
        match goal with
        | Hbr : binds β1 (abind_flex_mono_def _) Θ |- _ =>
            pose proof (binds_unique _ _ _ _ _ HbtΘ Hbr (a_wf_aenv_uniq Hwfth))
              as Hcon; discriminate
        end. }
    2:{ exfalso. inversion Hrs; subst.
        match goal with
        | Hbr : binds β1 (abind_flex_mono_def _) Θ |- _ =>
            pose proof (binds_unique _ _ _ _ _ HbtΘ Hbr (a_wf_aenv_uniq Hwfth))
              as Hcon; discriminate
        end. }
    2:{ exfalso. inversion Hrs; subst.
        match goal with
        | Hbr : binds β1 (abind_flex_mono_def _) Θ |- _ =>
            pose proof (binds_unique _ _ _ _ _ HbtΘ Hbr (a_wf_aenv_uniq Hwfth))
              as Hcon; discriminate
        end. }
    2:{ exfalso; apply HneP0ghost; reflexivity. }
    2:{ exfalso; apply (Hnthg Pt0 eq_refl); apply guarded_pskl__var. }

    pose proof (a_wf_pskl_var_non_flex_tvar HwfP0 HnfP0) as Hbtδ0.
    assert (Hβ1κ0 : β10 `notin` dom κ)
      by (eapply a_inc_tvar_notin_dom; eauto).
    rewrite (msubst_lookup_notin κ Hβ1κ0) in Hrs.
    simpl in Hrs.
    assert (Heqδ : β10 = β1).
    { inversion Hrs; subst.
      - reflexivity.
      - exfalso.
        match goal with
        | Hbr : binds β10 (abind_flex_mono_def _) Θ |- _ =>
            assert (HbtΘ0' : binds β10 abind_tvar Θ)
              by (eapply a_inc_binds_tvar; eauto);
            pose proof (binds_unique _ _ _ _ _ HbtΘ0' Hbr
                          (a_wf_aenv_uniq Hwfth)) as Hcon; discriminate
        end.
      - exfalso.
        match goal with
        | Hbr : binds β1 (abind_flex_mono_def _) Θ |- _ =>
            pose proof (binds_unique _ _ _ _ _ HbtΘ Hbr
                          (a_wf_aenv_uniq Hwfth)) as Hcon; discriminate
        end. }
    subst β10.
    exists (pskl_var_f β1), Θ0. split.
    { apply a_consis__rigid. exact Hbtδ. }
    split; [ intros γ Hγ; left; exact Hγ | ].
    intros κ1 Hid Hinc1. exists κ.
    destruct (opt_axiom_factor Hwf0 Hid Hinc1 Hinc) as [Hout Hfact].
    split; [ exact Hout | ]. split; [ exact Hfact | ].
    unfold ad_precise.
    cbn [pskl_to_bskl_syn msubst_bskl].
    rewrite bskl_to_pskl_pskl_to_bskl_syn.
    rewrite (msubst_lookup_notin κ Hβ1κ).
    apply consis_precise_mono_join with (A := ptyp_var_f β1)
                                        (Qb := bskl_var_f β1);
      [ exact Hwfth | apply mono_ptyp__var
      | intros α0 Hα0; simpl in Hα0;
        assert (Hα0δ : α0 = β1) by (clear - Hα0; fsetdec); subst α0;
        left; exact HbtΘ
      | apply ad_pat_consis__var; [ clear; fsetdec | left; exact HbtΘ ] ].

  -
    match goal with
    | Hpm : {{ ?x ⨟ _ ⊢ˢ R1 ∼ _ }}ad |- _ => rename Hpm into Hj1
    end.
    match goal with
    | Hpm : {{ ?x ⨟ _ ⊢ˢ R2 ∼ _ }}ad |- _ => rename Hpm into Hj2
    end.
    match goal with
    | Hpe : Ψ [=] union _ _ |- _ => rename Hpe into HΨu
    end.
    assert (HΨ1e : Ψ1 [=] empty) by (clear - HΨ HΨu; fsetdec).
    assert (HΨ2e : Ψ2 [=] empty) by (clear - HΨ HΨu; fsetdec).

    destruct PP as [ | n | β1 | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    {
      exfalso.
      rewrite (a_inc_lookup_rigid Hinc Hwf0 HwfP HnfP) in HeqS.
      simpl in HeqS. discriminate. }
    inversion HeqS; subst R1 R2. clear HeqS.
    assert (HwfPPa : {{ Θ0 ⨟ empty ⊢ₚₛ PPa }}a) by (inversion HwfP; assumption).
    assert (HwfPPb : {{ Θ0 ⨟ empty ⊢ₚₛ PPb }}a) by (inversion HwfP; assumption).
    assert (HlcP : lc_pskl (pskl_arrow PPa PPb))
      by (eapply a_wf_pskl_lc; exact HwfP).

    destruct PP0 as [ | n0 | β10 | P0a P0b | Pb0 | | Pt0 ]; simpl in Hrs.
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso; inversion Hrs. }
    1:{
      exfalso.
      destruct (a_inc_rigid_refine_inv Hinc Hwf0 Hwfth HwfP0 HnfP0 Hrs)
        as [? HQ].
      discriminate HQ. }
    2:{ exfalso; inversion Hrs. }
    2:{ exfalso; apply HneP0ghost; reflexivity. }
    2:{
      exfalso. apply (Hnthg Pt0 eq_refl).
      inversion HlcP; subst.
      apply guarded_pskl__arrow; assumption. }

    assert (HwfP0a : {{ Θ0 ⨟ empty ⊢ₚₛ P0a }}a) by (inversion HwfP0; assumption).
    assert (HwfP0b : {{ Θ0 ⨟ empty ⊢ₚₛ P0b }}a) by (inversion HwfP0; assumption).
    inversion Hrs; subst.
    match goal with
    | Ha : {{ Θ ⨟ Δ1 ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0a)) ⊳ Q1 }}ad,
      Hb : {{ Θ ⨟ Δ1 ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0b)) ⊳ Q2 }}ad |- _ =>
        rename Ha into Hrs1; rename Hb into Hrs2
    end.
    change ({{ Θ ⨟ Δ2 ⊢ᵣₚ (pskl_arrow (msubst_pskl κ PPa) (msubst_pskl κ PPb)) ⊳ (pskl_arrow (bskl_to_pskl Q1) (bskl_to_pskl Q2)) }}ad) in Hrp.
    inversion Hrp; subst.
    match goal with
    | Ha : {{ Θ ⨟ Δ2 ⊢ᵣₚ (msubst_pskl κ PPa) ⊳ (bskl_to_pskl Q1) }}ad,
      Hb : {{ Θ ⨟ Δ2 ⊢ᵣₚ (msubst_pskl κ PPb) ⊳ (bskl_to_pskl Q2) }}ad
      |- _ =>
        rename Ha into Hrp1; rename Hb into Hrp2
    end.

    assert (HwfQ1 : {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Q1) }}a)
      by (simpl in HwfQb; inversion HwfQb; assumption).
    assert (HwfQ2 : {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Q2) }}a)
      by (simpl in HwfQb; inversion HwfQb; assumption).

    assert (Hlt1 : mu_lt (mu_consis Θ κ P0a PPa Θ0)
                         (mu_consis Θ κ (pskl_arrow P0a P0b)
                                        (pskl_arrow PPa PPb) Θ0)).
    { unfold mu_consis. apply mu_lt_intro. left. unfold V_consis.
      pose proof (Vpskl_arrow_lt1 Θ κ PPa PPb).
      pose proof (Vpskl_arrow_lt1 Θ κ P0a P0b). lia. }
    destruct (IH _ Hlt1) as [HcIH1 _].
    destruct (HcIH1 N Δ1 Δ2 Θ0 P0a PPa κ Θ Ψ1 Q1 eq_refl Hwf0 HwfP0a HwfPPa
                    Hrig Hnfd0 Hfaf Hinc Hwfth Hnfdth HΨ1e Hj1 Hrs1 Hrp1 HwfQ1)
      as [PA1 [Θ1 [Hc1 [Hnew1 Hopt1]]]].

    destruct (proj2 (proj2 a_assign_unify_consis_sound) _ _ _ _ _ _ _ Hc1
                Hwf0 HwfP0a HwfPPa Hrig Hnfd0 Hfaf)
      as [Hle1 [Hwf1 [Hdom1 [Hinv1 [Hsol1 _]]]]].
    destruct Hle1 as [[w1 [Hidw1 Hincw1]] Hdefs1].
    destruct (Hopt1 w1 Hidw1 Hincw1) as [ζ1 [Hζ1 [Hie1 Hprec1]]].
    assert (HΔdom : (Δ1 `union` Δ2) ∩ dom Θ1 [<=] dom Θ0).
    { intros α0 Hα0.
      assert (Hα0' : α0 `in` (Δ1 `union` Δ2)) by (clear - Hα0; fsetdec).
      pose proof (Hrig α0 Hα0') as Hb. apply binds_In in Hb. exact Hb. }
    destruct (Hinv1 (Δ1 `union` Δ2) Hnfd0 Hfaf HΔdom
                ltac:(intros α0 Hα0 HnX; exfalso; pose proof (Hrig α0 Hα0) as Hb;
                      apply binds_In in Hb; exact (HnX Hb)))
      as [Hnfd1 [Hfaf1 _]].
    assert (HrigΘ1 : forall α0, α0 `in` (Δ1 `union` Δ2) ->
              binds α0 abind_tvar Θ1)
      by (intros α0 Hα0; eapply a_inc_binds_tvar;
          [ exact Hincw1 | apply Hrig; exact Hα0 ]).
    assert (HwfP0b1 : {{ Θ1 ⨟ empty ⊢ₚₛ P0b }}a).
    { eapply a_wf_pskl_isub; [ exact HwfP0b | ].
      split; [ exists w1; split; assumption | exact Hdefs1 ]. }
    assert (HwfPPb1 : {{ Θ1 ⨟ empty ⊢ₚₛ PPb }}a).
    { eapply a_wf_pskl_isub; [ exact HwfPPb | ].
      split; [ exists w1; split; assumption | exact Hdefs1 ]. }

    assert (HawfPPb : a_scope_pskl Θ0 PPb).
    { exact (a_scope_pskl_of_wf HwfPPb). }
    assert (HawfP0b : a_scope_pskl Θ0 P0b).
    { exact (a_scope_pskl_of_wf HwfP0b). }
    assert (Hlcκ : msubst_lc κ) by (eapply a_inc_msubst_lc; exact Hinc).
    assert (Hlcζ1 : msubst_lc ζ1) by (eapply a_inc_msubst_lc; exact Hζ1).
    assert (Hlcc1 : msubst_lc (msubst_compose ζ1 w1))
      by (apply msubst_lc_compose;
          [ exact Hlcζ1 | eapply is_id_msubst_values_lc; exact Hidw1 ]).
    assert (Heqb : {{ Θ ⊢ (msubst_pskl κ PPb) ≡ˢ (msubst_pskl ζ1 PPb) }}a).
    { replace (msubst_pskl ζ1 PPb)
        with (msubst_pskl (msubst_compose ζ1 w1) PPb)
        by (eapply msubst_compose_id_pskl;
            [ exact Hwf0 | exact Hwf1 | exact Hidw1 | exact Hincw1
            | exact Hζ1 | exact (a_scope_pskl_of_wf HwfPPb) ]).
      eapply a_inc_equiv_msubst_pskl;
        [ exact HawfPPb | exact Hie1 | exact Hwf0
        | exact Hlcκ | exact Hlcc1 ]. }
    assert (Heqb0 : {{ Θ ⊢ (msubst_pskl κ P0b) ≡ˢ (msubst_pskl ζ1 P0b) }}a).
    { replace (msubst_pskl ζ1 P0b)
        with (msubst_pskl (msubst_compose ζ1 w1) P0b)
        by (eapply msubst_compose_id_pskl;
            [ exact Hwf0 | exact Hwf1 | exact Hidw1 | exact Hincw1
            | exact Hζ1 | exact (a_scope_pskl_of_wf HwfP0b) ]).
      eapply a_inc_equiv_msubst_pskl;
        [ exact HawfP0b | exact Hie1 | exact Hwf0
        | exact Hlcκ | exact Hlcc1 ]. }
    destruct (skl_tyequiv_consis_transport Heqb Hwfth
                (fun x b Hb => Hb)) as [Hjt _].
    assert (Hj2' : {{ Ψ2 ⨟ Θ ⊢ˢ (pskl_to_uskl (msubst_pskl ζ1 PPb)) ∼ Q2 }}ad)
      by (apply Hjt; exact Hj2).
    destruct (skl_tyequiv_refine_syn_transport Heqb0 Hwfth
                (fun x b Hb => Hb)) as [Hrst _].
    pose proof (Hrst _ _ Hrs2) as Hrs2'.
    destruct (skl_tyequiv_refine_pskl_transport Heqb Hwfth
                (fun x b Hb => Hb)) as [Hrpt _].
    pose proof (Hrpt _ _ Hrp2) as Hrp2'.

    assert (HVb : Vpskl Θ ζ1 PPb = Vpskl Θ κ PPb).
    { transitivity (Vpskl Θ (msubst_compose ζ1 w1) PPb).
      - unfold Vpskl.
        erewrite (msubst_compose_id_pskl (P := PPb));
          [ reflexivity | exact Hwf0 | exact Hwf1 | exact Hidw1
          | exact Hincw1 | exact Hζ1 | exact (a_scope_pskl_of_wf HwfPPb) ].
      - symmetry.
        eapply Vpskl_inc_equiv;
          [ exact Hie1 | exact Hwf0 | exact Hwfth | exact HawfPPb ]. }
    assert (HVb0 : Vpskl Θ ζ1 P0b = Vpskl Θ κ P0b).
    { transitivity (Vpskl Θ (msubst_compose ζ1 w1) P0b).
      - unfold Vpskl.
        erewrite (msubst_compose_id_pskl (P := P0b));
          [ reflexivity | exact Hwf0 | exact Hwf1 | exact Hidw1
          | exact Hincw1 | exact Hζ1 | exact (a_scope_pskl_of_wf HwfP0b) ].
      - symmetry.
        eapply Vpskl_inc_equiv;
          [ exact Hie1 | exact Hwf0 | exact Hwfth | exact HawfP0b ]. }
    assert (Hlt2 : mu_lt (mu_consis Θ ζ1 P0b PPb Θ1)
                         (mu_consis Θ κ (pskl_arrow P0a P0b)
                                        (pskl_arrow PPa PPb) Θ0)).
    { unfold mu_consis. apply mu_lt_intro. left. unfold V_consis.
      rewrite HVb. rewrite HVb0.
      pose proof (Vpskl_arrow_lt2 Θ κ PPa PPb).
      pose proof (Vpskl_arrow_lt2 Θ κ P0a P0b). lia. }
    destruct (IH _ Hlt2) as [HcIH2 _].
    destruct (HcIH2 N Δ1 Δ2 Θ1 P0b PPb ζ1 Θ Ψ2 Q2 eq_refl Hwf1 HwfP0b1
                    HwfPPb1 HrigΘ1 Hnfd1 Hfaf1 Hζ1 Hwfth Hnfdth HΨ2e
                    Hj2' Hrs2' Hrp2' HwfQ2)
      as [PA2 [Θ2 [Hc2 [Hnew2 Hopt2]]]].

    exists (pskl_arrow PA1 PA2), Θ2. split.
    { eapply a_consis__arrow; [ exact Hc1 | exact Hc2 ]. }
    split; [ eapply avoid_compose; [ exact Hnew1 | exact Hnew2 ] | ].
    intros κf Hidf Hincf.

    destruct (proj2 (proj2 a_assign_unify_consis_sound) _ _ _ _ _ _ _ Hc2
                Hwf1 HwfP0b1 HwfPPb1 HrigΘ1 Hnfd1 Hfaf1)
      as [Hle2 [Hwf2 [Hdom2 [Hinv2 [Hsol2 _]]]]].
    destruct Hle2 as [[w2 [Hidw2 Hincw2]] Hdefs2].
    destruct (Hopt2 w2 Hidw2 Hincw2) as [ζ2 [Hζ2 [Hie2 Hprec2]]].

    assert (Heqw : w1 = κf) by (eapply is_id_inc_unique; eauto).
    subst κf.
    exists ζ2. split; [ exact Hζ2 | ]. split.
    {
      eapply a_inc_equiv_glue with
        (Θmid := Θ1) (Θfin := Θ2) (κ1b := w2) (ζ1 := ζ1);
        [ exact Hwf0 | exact Hwf1 | exact Hwf2 | exact Hwfth
        | exact Hidw1 | exact Hidw2
        |
          intros α Hα;
          pose proof (a_inc_dom_flex Hincw1 Hα) as Hfα0';
          eapply a_inc_flex_dom; [ exact Hincw2 | exact Hwf1 | ];
          eapply (proj2 (proj2 a_assign_unify_consis_flex_preserve));
            [ exact Hc1 | exact Hfα0' ]
        | exact Hincw1 | exact Hincw2 | exact Hζ1 | exact Hζ2
        | exact Hie1 | exact Hie2 ]. }

    assert (HawfPA1 : a_scope_pskl Θ1 PA1)
      by (eapply a_consis_output_scope; eassumption).
    assert (Hlcζ2 : msubst_lc ζ2) by (eapply a_inc_msubst_lc; exact Hζ2).
    assert (Hlcc2 : msubst_lc (msubst_compose ζ2 w2))
      by (apply msubst_lc_compose;
          [ exact Hlcζ2 | eapply is_id_msubst_values_lc; exact Hidw2 ]).
    assert (Heqζ : {{ Θ ⊢ (msubst_pskl ζ1 PA1) ≡ˢ (msubst_pskl ζ2 PA1) }}a).
    { replace (msubst_pskl ζ2 PA1)
        with (msubst_pskl (msubst_compose ζ2 w2) PA1)
        by (eapply msubst_compose_id_pskl;
            [ exact Hwf1 | exact Hwf2 | exact Hidw2 | exact Hincw2
            | exact Hζ2 | exact HawfPA1 ]).
      eapply a_inc_equiv_msubst_pskl;
        [ exact HawfPA1 | exact Hie2 | exact Hwf1
        | exact Hlcζ1 | exact Hlcc2 ]. }
    unfold ad_precise in Hprec1, Hprec2 |- *.
    rewrite !bskl_to_pskl_msubst_bskl in Hprec1, Hprec2.
    rewrite !bskl_to_pskl_pskl_to_bskl_syn in Hprec1, Hprec2.
    change ({{ Θ ⨟ (Δ1 `union` Δ2) ⊢ᵣ (bskl_arrow
         (pskl_to_bskl_inh
            (bskl_to_pskl (msubst_bskl ζ2 (pskl_to_bskl_syn PA1))))
         (pskl_to_bskl_inh
            (bskl_to_pskl (msubst_bskl ζ2 (pskl_to_bskl_syn PA2))))) ⊳ (bskl_arrow (pskl_to_bskl_inh (bskl_to_pskl Q1))
                  (pskl_to_bskl_inh (bskl_to_pskl Q2))) }}ad).
    apply ad_refine_syn_arrow_intro.
    +
      rewrite bskl_to_pskl_msubst_bskl.
      rewrite bskl_to_pskl_pskl_to_bskl_syn.
      destruct (skl_tyequiv_refine_syn_transport Heqζ Hwfth
                  (fun x b Hb => Hb)) as [Hpt _].
      apply Hpt. exact Hprec1.
    +
      rewrite bskl_to_pskl_msubst_bskl.
      rewrite bskl_to_pskl_pskl_to_bskl_syn.
      exact Hprec2.

  - destruct (msubst_pskl κ PP); simpl in HeqS; discriminate.

  -
    match goal with
    | Hpm : forall α, α `notin` _ -> {{ _ ⨟ _ ⊢ˢ _ ∼ _ }}ad |- _ =>
        rename Hpm into Hjoin
    end.

    destruct PP as [ | n | β1 | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    {
      exfalso.
      rewrite (a_inc_lookup_rigid Hinc Hwf0 HwfP HnfP) in HeqS.
      simpl in HeqS. discriminate. }
    inversion HeqS. subst R. clear HeqS.

    destruct PP0 as [ | n0 | β10 | P0a P0b | P0b | | Pt0 ]; simpl in Hrs.
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso; inversion Hrs. }
    1:{
      exfalso.
      destruct (a_inc_rigid_refine_inv Hinc Hwf0 Hwfth HwfP0 HnfP0 Hrs)
        as [? HQ].
      discriminate HQ. }
    1:{ exfalso; inversion Hrs. }
    2:{ exfalso; apply HneP0ghost; reflexivity. }
    2:{
      exfalso.
      assert (Hg0 : guarded_pskl Pt0) by (inversion HwfP0; assumption).
      assert (Hgκ0 : guarded_pskl (msubst_pskl κ Pt0))
        by (eapply guarded_pskl_msubst_inc; eauto).
      inversion Hrs; subst.
      eapply ad_refine_syn_guarded_src_all_inh_absurd;
        [ exact Hwfth | eassumption
        | apply guarded_pskl_to_bskl_inh; exact Hgκ0 ]. }

    inversion Hrs; subst.
    match goal with
    | Hn : forall α, α `notin` ?LA ->
             ad_refine_syn _ _ _ _ |- _ => rename Hn into Hrs1
    end.
    change ({{ Θ ⨟ Δ2 ⊢ᵣₚ (pskl_all_syn (msubst_pskl κ PPb)) ⊳ (pskl_all_syn (bskl_to_pskl Q)) }}ad) in Hrp.
    inversion Hrp; subst.
    match goal with
    | Hn : forall α, α `notin` ?LB ->
             ad_refine_pskl _ _ _ _ |- _ => rename Hn into Hrp1
    end.
    assert (Hwfb0 : exists Lw0, forall α, α `notin` Lw0 ->
              {{ ((α ~ abind_tvar) ++ Θ0) ⨟ (add α empty) ⊢ₚₛ
                (open_pskl_wrt_pskl P0b (pskl_var_f α)) }}a).
    { inversion HwfP0; subst. eexists. eassumption. }
    destruct Hwfb0 as [Lw0 Hwfb0].
    assert (Hwfb : exists Lw, forall α, α `notin` Lw ->
              {{ ((α ~ abind_tvar) ++ Θ0) ⨟ (add α empty) ⊢ₚₛ
                (open_pskl_wrt_pskl PPb (pskl_var_f α)) }}a).
    { inversion HwfP; subst. eexists. eassumption. }
    destruct Hwfb as [Lw Hwfb].

    match type of Hrs1 with
    | forall _, _ `notin` ?LA -> _ =>
    match type of Hrp1 with
    | forall _, _ `notin` ?LB -> _ =>
      pick fresh α for (L `union` LA `union` LB `union` Lw0 `union` Lw
                        `union` dom Θ0 `union` ftvar_in_aenv Θ0
                        `union` dom Θ `union` dom κ
                        `union` Δ1 `union` Δ2
                        `union` ftvar_in_pskl P0b `union` ftvar_in_pskl PPb
                        `union` ftvar_in_bskl Q)
    end end.
    assert (Hlcκ : msubst_lc κ) by (eapply a_inc_msubst_lc; exact Hinc).
    assert (Hακ : α `notin` dom κ) by (clear - Fr; solve_notin_auto).
    assert (HαΘ : α `notin` dom Θ) by (clear - Fr; solve_notin_auto).
    assert (HαΘ0 : α `notin` dom Θ0) by (clear - Fr; solve_notin_auto).

    assert (HVeq : forall Pz, Vpskl ((α ~ abind_tvar) ++ Θ) κ Pz
                            = Vpskl Θ κ Pz)
      by (intro Pz; unfold Vpskl; rewrite aenv_msubst_tvar; reflexivity).
    assert (Hlt : mu_lt
        (mu_consis ((α ~ abind_tvar) ++ Θ) κ
           (open_pskl_wrt_pskl P0b (pskl_var_f α))
           (open_pskl_wrt_pskl PPb (pskl_var_f α))
           ((α ~ abind_tvar) ++ Θ0))
        (mu_consis Θ κ (pskl_all_syn P0b) (pskl_all_syn PPb) Θ0)).
    { unfold mu_consis. apply mu_lt_intro. left. unfold V_consis.
      rewrite !HVeq.
      rewrite (Vpskl_open P0b Hwfth Hlcκ Hακ HαΘ).
      rewrite (Vpskl_open PPb Hwfth Hlcκ Hακ HαΘ).
      pose proof (Vpskl_all_syn_lt Θ κ P0b).
      pose proof (Vpskl_all_syn_lt Θ κ PPb). lia. }
    destruct (IH _ Hlt) as [HcIH _].

    assert (HwfP0α : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ
                       (open_pskl_wrt_pskl P0b (pskl_var_f α)) }}a).
    { eapply a_wf_pskl_delta_mono;
        [ apply Hwfb0; clear - Fr; solve_notin_auto
        | intros ? ? Hc; exfalso; clear - Hc; fsetdec ]. }
    assert (HwfPα : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ
                      (open_pskl_wrt_pskl PPb (pskl_var_f α)) }}a).
    { eapply a_wf_pskl_delta_mono;
        [ apply Hwfb; clear - Fr; solve_notin_auto
        | intros ? ? Hc; exfalso; clear - Hc; fsetdec ]. }
    assert (HΔ' : add α Δ1 `union` add α Δ2 [<=] add α (Δ1 `union` Δ2))
      by (clear; fsetdec).
    destruct (consis_complete_open_ctx HΔ' Hwf0 HαΘ0 Hrig Hnfd0 Hfaf Hinc
                Hwfth HαΘ Hnfdth)
      as (Hwf0' & Hrig' & Hnfd0' & Hfaf' & Hinc' & Hwfth' & Hnfdth').
    assert (Hjα : {{ Ψ ⨟ ((α ~ abind_tvar) ++ Θ) ⊢ˢ
              (pskl_to_uskl (msubst_pskl κ
                 (open_pskl_wrt_pskl PPb (pskl_var_f α))))
              ∼ (open_bskl_wrt_bskl Q (bskl_var_f α)) }}ad).
    { pose proof (Hjoin α ltac:(clear - Fr; solve_notin_auto)) as Hj0.
      rewrite (msubst_pskl_open_lc PPb Hlcκ Hακ).
      rewrite pskl_to_uskl_open_var.
      exact Hj0. }
    assert (Hrsα : {{ ((α ~ abind_tvar) ++ Θ) ⨟ (add α Δ1) ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ
                 (open_pskl_wrt_pskl P0b (pskl_var_f α)))) ⊳ (open_bskl_wrt_bskl Q (bskl_var_f α)) }}ad).
    { rewrite (msubst_pskl_open_lc P0b Hlcκ Hακ).
      rewrite pskl_to_bskl_inh_open.
      apply Hrs1; clear - Fr; solve_notin_auto. }
    assert (Hrpα : {{ ((α ~ abind_tvar) ++ Θ) ⨟ (add α Δ2) ⊢ᵣₚ (msubst_pskl κ (open_pskl_wrt_pskl PPb (pskl_var_f α))) ⊳ (bskl_to_pskl (open_bskl_wrt_bskl Q (bskl_var_f α))) }}ad).
    { rewrite (msubst_pskl_open_lc PPb Hlcκ Hακ).
      rewrite bskl_to_pskl_open.
      apply Hrp1; clear - Fr; solve_notin_auto. }
    assert (HwfQα : {{ ((α ~ abind_tvar) ++ Θ) ⨟ empty ⊢ₚₛ
                       (bskl_to_pskl (open_bskl_wrt_bskl Q (bskl_var_f α))) }}a).
    { rewrite bskl_to_pskl_open.
      eapply a_wf_pskl_delta_mono;
        [ apply a_wf_pskl_all_inv_at;
            [ exact HwfQb
            | rewrite ftvar_bskl_to_pskl; clear - Fr; solve_notin_auto ]
        | intros ? ? Hc; exfalso; clear - Hc; fsetdec ]. }
    destruct (HcIH N (add α Δ1) (add α Δ2) ((α ~ abind_tvar) ++ Θ0)
                (open_pskl_wrt_pskl P0b (pskl_var_f α))
                (open_pskl_wrt_pskl PPb (pskl_var_f α)) κ
                ((α ~ abind_tvar) ++ Θ) Ψ
                (open_bskl_wrt_bskl Q (bskl_var_f α))
                eq_refl Hwf0' HwfP0α HwfPα Hrig' Hnfd0' Hfaf' Hinc'
                Hwfth' Hnfdth' HΨ Hjα Hrsα Hrpα HwfQα)
      as [P1 [Θ1' [Hc [Hnew Hopt']]]].

    destruct (proj2 (proj2 a_assign_unify_consis_tvar_prefix) _ _ _ _ _ _ _ Hc ((α, abind_tvar) :: nil) Θ0 eq_refl
                (tvar_prefix_cons tvar_prefix_nil)) as [Θ1 HeqΘ1'].
    simpl in HeqΘ1'. subst Θ1'.

    assert (Huq0 : uniq ((α ~ abind_tvar) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf0').
    assert (HαΔ1 : α `notin` Δ1) by (clear - Fr; solve_notin_auto).
    assert (HαΔ2 : α `notin` Δ2) by (clear - Fr; solve_notin_auto).
    exists (pskl_all_syn (close_pskl_wrt_pskl α P1)), Θ1.
    split.
    {
      apply a_consis__forall_inh with (α := α);
        [ clear - Fr; solve_notin_auto | exact Hc ]. }
    split.
    { eapply avoid_truncate_cons; [ exact Hnew | ].
      pose proof (auc_uniq_consis Hc Huq0) as Hu1. clear - Hu1. solve_uniq. }

    eapply consis_complete_close_optimal with (α := α) (Q := Q)
      (Δr := add α Δ1 `union` add α Δ2);
      [exact Hwfth | | clear; fsetdec | exact Hopt'].
    pose proof (auc_uniq_consis Hc Huq0) as Hu1.
    assert (HαΘ1 : α `notin` dom Θ1) by (clear - Hu1; solve_uniq).
    clear - Fr HαΘ1; solve_notin_auto.

  - destruct (msubst_pskl κ PP); simpl in HeqS; discriminate.

  -
    match goal with
    | Hpm : forall α, α `notin` _ -> {{ _ ⨟ _ ⊢ˢ _ ∼ _ }}ad |- _ =>
        rename Hpm into Hjoin
    end.

    destruct PP as [ | n | β1 | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    { exfalso.
      rewrite (a_inc_lookup_rigid Hinc Hwf0 HwfP HnfP) in HeqS.
      simpl in HeqS. discriminate. }
    inversion HeqS. subst R. clear HeqS.

    destruct PP0 as [ | n0 | β10 | P0a P0b | P0b | | Pt0 ]; simpl in Hrs.
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso.
      destruct (a_inc_rigid_refine_inv Hinc Hwf0 Hwfth HwfP0 HnfP0 Hrs)
        as [? HQ].
      discriminate HQ. }
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso; apply HneP0ghost; reflexivity. }

    assert (Hg0 : guarded_pskl Pt0) by (inversion HwfP0; assumption).
    assert (Hwft0 : {{ Θ0 ⨟ empty ⊢ₚₛ Pt0 }}a)
      by (exact (proj2 (a_wf_pskl_univ_ghost_inv HwfP0))).
    inversion Hrs; subst.
    1:{
      exfalso.
      assert (Hgκ0 : guarded_pskl (msubst_pskl κ Pt0))
        by (eapply guarded_pskl_msubst_inc; eauto).
      eapply ad_refine_syn_guarded_src_all_syn_absurd;
        [ exact Hwfth | eassumption
        | apply guarded_pskl_to_bskl_inh; exact Hgκ0 ]. }
    match goal with
    | Hn : forall α, α `notin` ?LA ->
             ad_refine_syn _ _ _ _ |- _ => rename Hn into Hrs1
    end.
    change ({{ Θ ⨟ Δ2 ⊢ᵣₚ (pskl_all_syn (msubst_pskl κ PPb)) ⊳ (pskl_all_syn (bskl_to_pskl Q)) }}ad) in Hrp.
    inversion Hrp; subst.
    match goal with
    | Hn : forall α, α `notin` ?LB ->
             ad_refine_pskl _ _ _ _ |- _ => rename Hn into Hrp1
    end.
    assert (Hwfb : exists Lw, forall α, α `notin` Lw ->
              {{ ((α ~ abind_tvar) ++ Θ0) ⨟ (add α empty) ⊢ₚₛ
                (open_pskl_wrt_pskl PPb (pskl_var_f α)) }}a).
    { inversion HwfP; subst. eexists. eassumption. }
    destruct Hwfb as [Lw Hwfb].

    match type of Hrs1 with
    | forall _, _ `notin` ?LA -> _ =>
    match type of Hrp1 with
    | forall _, _ `notin` ?LB -> _ =>
      pick fresh α for (L `union` LA `union` LB `union` Lw
                        `union` dom Θ0 `union` ftvar_in_aenv Θ0
                        `union` dom Θ `union` dom κ
                        `union` Δ1 `union` Δ2
                        `union` ftvar_in_pskl Pt0 `union` ftvar_in_pskl PPb
                        `union` ftvar_in_bskl Q)
    end end.
    assert (Hlcκ : msubst_lc κ) by (eapply a_inc_msubst_lc; exact Hinc).
    assert (Hακ : α `notin` dom κ) by (clear - Fr; solve_notin_auto).
    assert (HαΘ : α `notin` dom Θ) by (clear - Fr; solve_notin_auto).
    assert (HαΘ0 : α `notin` dom Θ0) by (clear - Fr; solve_notin_auto).
    assert (HVeq : forall Pz, Vpskl ((α ~ abind_tvar) ++ Θ) κ Pz
                            = Vpskl Θ κ Pz)
      by (intro Pz; unfold Vpskl; rewrite aenv_msubst_tvar; reflexivity).
    assert (Hlt : mu_lt
        (mu_consis ((α ~ abind_tvar) ++ Θ) κ
           (pskl_univ_ghost Pt0)
           (open_pskl_wrt_pskl PPb (pskl_var_f α))
           ((α ~ abind_tvar) ++ Θ0))
        (mu_consis Θ κ (pskl_univ_ghost Pt0) (pskl_all_syn PPb) Θ0)).
    { unfold mu_consis. apply mu_lt_intro. left. unfold V_consis.
      rewrite !HVeq.
      rewrite (Vpskl_open PPb Hwfth Hlcκ Hακ HαΘ).
      pose proof (Vpskl_all_syn_lt Θ κ PPb). lia. }
    destruct (IH _ Hlt) as [HcIH _].
    assert (HwfP0α : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ
                       (pskl_univ_ghost Pt0) }}a).
    { eapply a_wf_pskl_weaken; [ | exact HwfP0 ].
      intros x b Hb. apply binds_cons_3. exact Hb. }
    assert (HwfPα : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ
                      (open_pskl_wrt_pskl PPb (pskl_var_f α)) }}a).
    { eapply a_wf_pskl_delta_mono;
        [ apply Hwfb; clear - Fr; solve_notin_auto
        | intros ? ? Hc; exfalso; clear - Hc; fsetdec ]. }
    assert (HΔ' : Δ1 `union` add α Δ2 [<=] add α (Δ1 `union` Δ2))
      by (clear; fsetdec).
    destruct (consis_complete_open_ctx HΔ' Hwf0 HαΘ0 Hrig Hnfd0 Hfaf Hinc
                Hwfth HαΘ Hnfdth)
      as (Hwf0' & Hrig' & Hnfd0' & Hfaf' & Hinc' & Hwfth' & Hnfdth').
    assert (Hjα : {{ Ψ ⨟ ((α ~ abind_tvar) ++ Θ) ⊢ˢ
              (pskl_to_uskl (msubst_pskl κ
                 (open_pskl_wrt_pskl PPb (pskl_var_f α))))
              ∼ (open_bskl_wrt_bskl Q (bskl_var_f α)) }}ad).
    { pose proof (Hjoin α ltac:(clear - Fr; solve_notin_auto)) as Hj0.
      rewrite (msubst_pskl_open_lc PPb Hlcκ Hακ).
      rewrite pskl_to_uskl_open_var.
      exact Hj0. }
    assert (Hrsα : {{ ((α ~ abind_tvar) ++ Θ) ⨟ Δ1 ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ (pskl_univ_ghost Pt0))) ⊳ (open_bskl_wrt_bskl Q (bskl_var_f α)) }}ad).
    { simpl. apply Hrs1. clear - Fr. fsetdec. }
    assert (Hrpα : {{ ((α ~ abind_tvar) ++ Θ) ⨟ (add α Δ2) ⊢ᵣₚ (msubst_pskl κ (open_pskl_wrt_pskl PPb (pskl_var_f α))) ⊳ (bskl_to_pskl (open_bskl_wrt_bskl Q (bskl_var_f α))) }}ad).
    { rewrite (msubst_pskl_open_lc PPb Hlcκ Hακ).
      rewrite bskl_to_pskl_open.
      apply Hrp1; clear - Fr; solve_notin_auto. }
    assert (HwfQα : {{ ((α ~ abind_tvar) ++ Θ) ⨟ empty ⊢ₚₛ
                       (bskl_to_pskl (open_bskl_wrt_bskl Q (bskl_var_f α))) }}a).
    { rewrite bskl_to_pskl_open.
      eapply a_wf_pskl_delta_mono;
        [ apply a_wf_pskl_all_inv_at;
            [ exact HwfQb
            | rewrite ftvar_bskl_to_pskl; clear - Fr; solve_notin_auto ]
        | intros ? ? Hc; exfalso; clear - Hc; fsetdec ]. }
    destruct (HcIH N Δ1 (add α Δ2) ((α ~ abind_tvar) ++ Θ0)
                (pskl_univ_ghost Pt0)
                (open_pskl_wrt_pskl PPb (pskl_var_f α)) κ
                ((α ~ abind_tvar) ++ Θ) Ψ
                (open_bskl_wrt_bskl Q (bskl_var_f α))
                eq_refl Hwf0' HwfP0α HwfPα Hrig' Hnfd0' Hfaf' Hinc'
                Hwfth' Hnfdth' HΨ Hjα Hrsα Hrpα HwfQα)
      as [P1 [Θ1' [Hc [Hnew Hopt']]]].
    destruct (proj2 (proj2 a_assign_unify_consis_tvar_prefix) _ _ _ _ _ _ _ Hc ((α, abind_tvar) :: nil) Θ0 eq_refl
                (tvar_prefix_cons tvar_prefix_nil)) as [Θ1 HeqΘ1'].
    simpl in HeqΘ1'. subst Θ1'.

    assert (Huq0 : uniq ((α ~ abind_tvar) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf0').
    assert (HαΔ1 : α `notin` Δ1) by (clear - Fr; solve_notin_auto).
    assert (HαΔ2 : α `notin` Δ2) by (clear - Fr; solve_notin_auto).
    exists (pskl_all_syn (close_pskl_wrt_pskl α P1)), Θ1.
    split.
    {
      apply a_consis__forall_syn with (α := α);
        [ clear - Fr; solve_notin_auto | exact Hc ]. }
    split.
    { eapply avoid_truncate_cons; [ exact Hnew | ].
      pose proof (auc_uniq_consis Hc Huq0) as Hu1. clear - Hu1. solve_uniq. }

    eapply consis_complete_close_optimal with (α := α) (Q := Q)
      (Δr := Δ1 `union` add α Δ2);
      [exact Hwfth | | clear; fsetdec | exact Hopt'].
    pose proof (auc_uniq_consis Hc Huq0) as Hu1.
    assert (HαΘ1 : α `notin` dom Θ1) by (clear - Hu1; solve_uniq).
    clear - Fr HαΘ1; solve_notin_auto.

  - destruct (msubst_pskl κ PP); simpl in HeqS; discriminate.

  - destruct (msubst_pskl κ PP); simpl in HeqS; discriminate.

  -
    rename H into HΨfill.

    destruct PP as [ | n | β1 | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    {
      exfalso.
      rewrite (a_inc_lookup_rigid Hinc Hwf0 HwfP HnfP) in HeqS.
      simpl in HeqS. discriminate. }

    change ({{ Θ ⨟ Δ2 ⊢ᵣₚ pskl_ghost ⊳ (bskl_to_pskl (pskl_to_bskl_inh P)) }}ad) in Hrp.
    rewrite bskl_to_pskl_pskl_to_bskl_inh in Hrp.

    assert (Hside : forall α, α `in` Δ2 -> α `notin` ftvar_in_pskl PP0).
    { intros α HinΔ2 HinP0.
      assert (HbX0 : binds α abind_tvar Θ0)
        by (apply Hrig; clear - HinΔ2; fsetdec).
      assert (HbX : binds α abind_tvar Θ)
        by (eapply a_inc_binds_tvar; eauto).
      assert (HXnd : α `notin` dom κ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      assert (Hdefs : forall β τ, binds β (abind_flex_mono_def τ) Θ ->
                                  α `notin` ftvar_in_ptyp τ).
      { intros β τ Hb. pose proof (Hnfdth _ _ Hb) as Hd.
        clear - Hd HinΔ2. fsetdec. }
      assert (HninP : α `notin` ftvar_in_pskl P).
      { inversion Hrp; subst.
        -
          match goal with
          | Hint : Δ2 ∩ ftvar_in_pskl P [=] empty |- _ =>
              clear - Hint HinΔ2; fsetdec
          end.
        -
          simpl.
          match goal with
          | Hbr : binds ?α0 (abind_flex_mono_def _) Θ |- _ =>
              assert (Hne : α <> α0)
                by (intro Heq; subst;
                    pose proof (binds_unique _ _ _ _ _ HbX Hbr
                                  (a_wf_aenv_uniq Hwfth)) as Hcon;
                    discriminate)
          end.
          clear - Hne; fsetdec. }
      assert (HinκP0 : α `in` ftvar_in_pskl (msubst_pskl κ PP0))
        by (apply msubst_pskl_ftv_keep; assumption).
      assert (HninSrc : α `notin`
                ftvar_in_bskl (pskl_to_bskl_inh (msubst_pskl κ PP0))).
      { eapply ad_refine_syn_rigid_ftv_rev;
          [ exact Hwfth | exact HbX | exact Hdefs | exact Hrs | ].
        pose proof (ftvar_in_bskl_inh P) as Hfe.
        clear - HninP Hfe. fsetdec. }
      pose proof (ftvar_in_bskl_inh (msubst_pskl κ PP0)) as Hfe2.
      clear - HninSrc HinκP0 Hfe2. fsetdec. }
    exists PP0, Θ0. split.
    { apply a_consis__ghost.
      apply inter_empty_pointwise. exact Hside. }
    split; [ intros γ Hγ; left; exact Hγ | ].
    intros κ1 Hid Hinc1. exists κ.
    destruct (opt_axiom_factor Hwf0 Hid Hinc1 Hinc) as [Hout Hfact].
    split; [ exact Hout | ]. split; [ exact Hfact | ].
    unfold ad_precise.
    rewrite bskl_to_pskl_msubst_bskl.
    rewrite bskl_to_pskl_pskl_to_bskl_syn.
    rewrite bskl_to_pskl_pskl_to_bskl_inh.
    eapply ad_refine_syn_extend_ftv; [ exact Hrs | ].
    intros α1 Hα1.
    destruct (AtomSetProperties.In_dec α1 Δ1) as [Hα1Δ1 | Hα1Δ1];
      [ left; exact Hα1Δ1 | right ].
    assert (Hα1Δ2 : α1 `in` Δ2) by (clear - Hα1 Hα1Δ1; fsetdec).
    assert (Hbγ : binds α1 abind_tvar Θ)
      by (eapply a_inc_binds_tvar; [ exact Hinc | ];
          apply Hrig; clear - Hα1Δ2; fsetdec).
    split.
    + assert (Hnq : α1 `notin` ftvar_in_pskl P)
        by (eapply ad_refine_pskl_ghost_src_target_ftv;
            [ exact Hrp | exact Hwfth
            | clear - Hα1Δ2; fsetdec | exact Hbγ ]).
      pose proof (ftvar_in_bskl_inh P) as Hfe.
      clear - Hnq Hfe. fsetdec.
    + intros β τ Hb.
      pose proof (Hnfdth β τ Hb) as Hi.
      clear - Hi Hα1Δ2. fsetdec.

  -
    match goal with
    | Hpm : {{ _ ⨟ _ ⊢ˢ _ ∼ _ }}ad |- _ => rename Hpm into Hj
    end.

    destruct PP as [ | n | β1 | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    {
      exfalso.
      rewrite (a_inc_lookup_rigid Hinc Hwf0 HwfP HnfP) in HeqS.
      simpl in HeqS. discriminate. }
    inversion HeqS; subst R. clear HeqS.
    assert (HgPPt : guarded_pskl PPt) by (inversion HwfP; assumption).
    assert (HwfPPt : {{ Θ0 ⨟ empty ⊢ₚₛ PPt }}a)
      by (exact (proj2 (a_wf_pskl_univ_ghost_inv HwfP))).
    assert (HgκP : guarded_pskl (msubst_pskl κ PPt))
      by (eapply guarded_pskl_msubst_inc; eauto).

    assert (HwfQ : {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a)
      by (exact (proj2 (a_wf_pskl_univ_ghost_inv HwfQb))).
    assert (HlcQ : lc_bskl Q)
      by (apply lc_bskl_of_bskl_to_pskl; exact (a_wf_pskl_lc HwfQ)).
    assert (HgQ : guarded_bskl Q).
    { eapply ad_pat_consis_guarded_r;
        [ exact Hj | exact Hwfth | reflexivity | exact HgκP | exact HlcQ ]. }

    destruct PP0 as [ | n0 | β10 | Pa0 Pb0 | Pb0 | | Pt0 ]; simpl in Hrs.
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso; inversion Hrs. }
    1:{
      exfalso.
      destruct (a_inc_rigid_refine_inv Hinc Hwf0 Hwfth HwfP0 HnfP0 Hrs)
        as [? HQ].
      discriminate HQ. }
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso; apply HneP0ghost; reflexivity. }

    assert (Hg0t : guarded_pskl Pt0) by (inversion HwfP0; assumption).
    assert (HwfP0t : {{ Θ0 ⨟ empty ⊢ₚₛ Pt0 }}a)
      by (exact (proj2 (a_wf_pskl_univ_ghost_inv HwfP0))).
    assert (Hgκ0 : guarded_pskl (msubst_pskl κ Pt0))
      by (eapply guarded_pskl_msubst_inc; eauto).
    assert (Hrs' : {{ Θ ⨟ Δ1 ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ Pt0)) ⊳ Q }}ad).
    { eapply ad_refine_syn_univ_ghost_keep_inv;
        [ exact Hwfth | | exact Hrs ].
      apply guarded_pskl_to_bskl_inh. exact Hgκ0. }
    change ({{ Θ ⨟ Δ2 ⊢ᵣₚ (pskl_univ_ghost (msubst_pskl κ PPt)) ⊳ (pskl_univ_ghost (bskl_to_pskl Q)) }}ad) in Hrp.
    assert (Hrp' : {{ Θ ⨟ Δ2 ⊢ᵣₚ (msubst_pskl κ PPt) ⊳ (bskl_to_pskl Q) }}ad)
      by (eapply ad_refine_pskl_univ_ghost_keep_inv;
            [ exact Hwfth | exact HgκP | exact Hrp ]).
    assert (Hlt : mu_lt (mu_consis Θ κ Pt0 PPt Θ0)
                        (mu_consis Θ κ (pskl_univ_ghost Pt0)
                                       (pskl_univ_ghost PPt) Θ0)).
    { unfold mu_consis. apply mu_lt_intro. left. unfold V_consis.
      pose proof (Vpskl_univ_ghost_lt Θ κ Pt0).
      pose proof (Vpskl_univ_ghost_lt Θ κ PPt). lia. }
    destruct (IH _ Hlt) as [HcIH _].
    destruct (HcIH N Δ1 Δ2 Θ0 Pt0 PPt κ Θ Ψ Q eq_refl Hwf0 HwfP0t HwfPPt
                   Hrig Hnfd0 Hfaf Hinc Hwfth Hnfdth HΨ Hj Hrs' Hrp' HwfQ)
      as [P1 [Θ1 [Hc [Hnew Hopt']]]].
    exists (pskl_univ_ghost P1), Θ1. split.
    { apply a_consis__univ_ghost. exact Hc. }
    split; [ exact Hnew | ].
    intros κ1 Hid Hinc1.
    destruct (Hopt' κ1 Hid Hinc1) as [ζ [Hζ [Hie Hprec]]].
    exists ζ. split; [ exact Hζ | ]. split; [ exact Hie | ].
    unfold ad_precise in *. simpl.
    apply ad_refine_syn_univ_ghost_keep_intro. exact Hprec.

  -
    match goal with
    | Hpm : forall α, α `notin` _ -> {{ _ ⨟ _ ⊢ˢ _ ∼ _ }}ad |- _ =>
        rename Hpm into Hjoin
    end.

    destruct PP as [ | n | β1 | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    { exfalso.
      rewrite (a_inc_lookup_rigid Hinc Hwf0 HwfP HnfP) in HeqS.
      simpl in HeqS. discriminate. }
    inversion HeqS. subst R. clear HeqS.

    destruct PP0 as [ | n0 | β10 | P0a P0b | P0b | | Pt0 ]; simpl in Hrs.
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso.
      destruct (a_inc_rigid_refine_inv Hinc Hwf0 Hwfth HwfP0 HnfP0 Hrs)
        as [? HQ].
      discriminate HQ. }
    1:{ exfalso; inversion Hrs. }
    2:{ exfalso; apply HneP0ghost; reflexivity. }
    2:{ exfalso.
      assert (Hg0 : guarded_pskl Pt0) by (inversion HwfP0; assumption).
      assert (Hgκ0 : guarded_pskl (msubst_pskl κ Pt0))
        by (eapply guarded_pskl_msubst_inc; eauto).
      inversion Hrs; subst.
      eapply ad_refine_syn_guarded_src_all_inh_absurd;
        [ exact Hwfth | eassumption
        | apply guarded_pskl_to_bskl_inh; exact Hgκ0 ]. }

    assert (HgP : guarded_pskl PPt) by (inversion HwfP; assumption).
    assert (HwfPt : {{ Θ0 ⨟ empty ⊢ₚₛ PPt }}a)
      by (exact (proj2 (a_wf_pskl_univ_ghost_inv HwfP))).
    inversion Hrs; subst.
    match goal with
    | Hn : forall α, α `notin` ?LA ->
             ad_refine_syn _ _ _ _ |- _ => rename Hn into Hrs1
    end.
    change ({{ Θ ⨟ Δ2 ⊢ᵣₚ (pskl_univ_ghost (msubst_pskl κ PPt)) ⊳ (pskl_all_syn (bskl_to_pskl Q)) }}ad) in Hrp.
    inversion Hrp; subst.
    1:{
      exfalso.
      assert (HgκP : guarded_pskl (msubst_pskl κ PPt))
        by (eapply guarded_pskl_msubst_inc; eauto).
      eapply ad_refine_pskl_guarded_src_all_syn_absurd;
        [ exact Hwfth | eassumption | exact HgκP ]. }
    match goal with
    | Hn : forall α, α `notin` ?LB ->
             ad_refine_pskl _ _ _ _ |- _ => rename Hn into Hrp1
    end.
    assert (Hwfb0 : exists Lw0, forall α, α `notin` Lw0 ->
              {{ ((α ~ abind_tvar) ++ Θ0) ⨟ (add α empty) ⊢ₚₛ
                (open_pskl_wrt_pskl P0b (pskl_var_f α)) }}a).
    { inversion HwfP0; subst. eexists. eassumption. }
    destruct Hwfb0 as [Lw0 Hwfb0].

    match type of Hrs1 with
    | forall _, _ `notin` ?LA -> _ =>
    match type of Hrp1 with
    | forall _, _ `notin` ?LB -> _ =>
      pick fresh α for (L `union` LA `union` LB `union` Lw0
                        `union` dom Θ0 `union` ftvar_in_aenv Θ0
                        `union` dom Θ `union` dom κ
                        `union` Δ1 `union` Δ2
                        `union` ftvar_in_pskl P0b `union` ftvar_in_pskl PPt
                        `union` ftvar_in_bskl Q)
    end end.
    assert (Hlcκ : msubst_lc κ) by (eapply a_inc_msubst_lc; exact Hinc).
    assert (Hακ : α `notin` dom κ) by (clear - Fr; solve_notin_auto).
    assert (HαΘ : α `notin` dom Θ) by (clear - Fr; solve_notin_auto).
    assert (HαΘ0 : α `notin` dom Θ0) by (clear - Fr; solve_notin_auto).
    assert (HVeq : forall Pz, Vpskl ((α ~ abind_tvar) ++ Θ) κ Pz
                            = Vpskl Θ κ Pz)
      by (intro Pz; unfold Vpskl; rewrite aenv_msubst_tvar; reflexivity).
    assert (Hlt : mu_lt
        (mu_consis ((α ~ abind_tvar) ++ Θ) κ
           (open_pskl_wrt_pskl P0b (pskl_var_f α))
           (pskl_univ_ghost PPt)
           ((α ~ abind_tvar) ++ Θ0))
        (mu_consis Θ κ (pskl_all_syn P0b) (pskl_univ_ghost PPt) Θ0)).
    { unfold mu_consis. apply mu_lt_intro. left. unfold V_consis.
      rewrite !HVeq.
      rewrite (Vpskl_open P0b Hwfth Hlcκ Hακ HαΘ).
      pose proof (Vpskl_all_syn_lt Θ κ P0b). lia. }
    destruct (IH _ Hlt) as [HcIH _].
    assert (HwfP0α : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ
                       (open_pskl_wrt_pskl P0b (pskl_var_f α)) }}a).
    { eapply a_wf_pskl_delta_mono;
        [ apply Hwfb0; clear - Fr; solve_notin_auto
        | intros ? ? Hc; exfalso; clear - Hc; fsetdec ]. }
    assert (HwfPα : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ
                      (pskl_univ_ghost PPt) }}a).
    { eapply a_wf_pskl_weaken; [ | exact HwfP ].
      intros x b Hb. apply binds_cons_3. exact Hb. }
    assert (HΔ' : add α Δ1 `union` Δ2 [<=] add α (Δ1 `union` Δ2))
      by (clear; fsetdec).
    destruct (consis_complete_open_ctx HΔ' Hwf0 HαΘ0 Hrig Hnfd0 Hfaf Hinc
                Hwfth HαΘ Hnfdth)
      as (Hwf0' & Hrig' & Hnfd0' & Hfaf' & Hinc' & Hwfth' & Hnfdth').
    assert (Hjα : {{ Ψ ⨟ ((α ~ abind_tvar) ++ Θ) ⊢ˢ
              (pskl_to_uskl (msubst_pskl κ (pskl_univ_ghost PPt)))
              ∼ (open_bskl_wrt_bskl Q (bskl_var_f α)) }}ad).
    { simpl. apply Hjoin. clear - Fr. fsetdec. }
    assert (Hrsα : {{ ((α ~ abind_tvar) ++ Θ) ⨟ (add α Δ1) ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ
                 (open_pskl_wrt_pskl P0b (pskl_var_f α)))) ⊳ (open_bskl_wrt_bskl Q (bskl_var_f α)) }}ad).
    { rewrite (msubst_pskl_open_lc P0b Hlcκ Hακ).
      rewrite pskl_to_bskl_inh_open.
      apply Hrs1; clear - Fr; solve_notin_auto. }
    assert (Hrpα : {{ ((α ~ abind_tvar) ++ Θ) ⨟ Δ2 ⊢ᵣₚ (msubst_pskl κ (pskl_univ_ghost PPt)) ⊳ (bskl_to_pskl (open_bskl_wrt_bskl Q (bskl_var_f α))) }}ad).
    { simpl. rewrite bskl_to_pskl_open. apply Hrp1.
      clear - Fr. fsetdec. }
    assert (HwfQα : {{ ((α ~ abind_tvar) ++ Θ) ⨟ empty ⊢ₚₛ
                       (bskl_to_pskl (open_bskl_wrt_bskl Q (bskl_var_f α))) }}a).
    { rewrite bskl_to_pskl_open.
      eapply a_wf_pskl_delta_mono;
        [ apply a_wf_pskl_all_inv_at;
            [ exact HwfQb
            | rewrite ftvar_bskl_to_pskl; clear - Fr; solve_notin_auto ]
        | intros ? ? Hc; exfalso; clear - Hc; fsetdec ]. }
    destruct (HcIH N (add α Δ1) Δ2 ((α ~ abind_tvar) ++ Θ0)
                (open_pskl_wrt_pskl P0b (pskl_var_f α))
                (pskl_univ_ghost PPt) κ
                ((α ~ abind_tvar) ++ Θ) Ψ
                (open_bskl_wrt_bskl Q (bskl_var_f α))
                eq_refl Hwf0' HwfP0α HwfPα Hrig' Hnfd0' Hfaf' Hinc'
                Hwfth' Hnfdth' HΨ Hjα Hrsα Hrpα HwfQα)
      as [P1 [Θ1' [Hc [Hnew Hopt']]]].
    destruct (proj2 (proj2 a_assign_unify_consis_tvar_prefix) _ _ _ _ _ _ _ Hc ((α, abind_tvar) :: nil) Θ0 eq_refl
                (tvar_prefix_cons tvar_prefix_nil)) as [Θ1 HeqΘ1'].
    simpl in HeqΘ1'. subst Θ1'.

    assert (Huq0 : uniq ((α ~ abind_tvar) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf0').
    assert (HαΔ1 : α `notin` Δ1) by (clear - Fr; solve_notin_auto).
    assert (HαΔ2 : α `notin` Δ2) by (clear - Fr; solve_notin_auto).
    exists (pskl_all_syn (close_pskl_wrt_pskl α P1)), Θ1.
    split.
    {
      apply a_consis__univ_ghost1 with (α := α);
        [ clear - Fr; solve_notin_auto | exact Hc ]. }
    split.
    { eapply avoid_truncate_cons; [ exact Hnew | ].
      pose proof (auc_uniq_consis Hc Huq0) as Hu1. clear - Hu1. solve_uniq. }

    eapply consis_complete_close_optimal with (α := α) (Q := Q)
      (Δr := add α Δ1 `union` Δ2);
      [exact Hwfth | | clear; fsetdec | exact Hopt'].
    pose proof (auc_uniq_consis Hc Huq0) as Hu1.
    assert (HαΘ1 : α `notin` dom Θ1) by (clear - Hu1; solve_uniq).
    clear - Fr HαΘ1; solve_notin_auto.

  -
    match goal with
    | Hpm : {{ _ ⨟ _ ⊢ˢ _ ∼ _ }}ad |- _ => rename Hpm into Hj
    end.

    destruct PP as [ | n | β1 | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    {
      exfalso.
      rewrite (a_inc_lookup_rigid Hinc Hwf0 HwfP HnfP) in HeqS.
      simpl in HeqS. discriminate. }
    inversion HeqS; subst R. clear HeqS.
    assert (HgPPt : guarded_pskl PPt) by (inversion HwfP; assumption).
    assert (HwfPPt : {{ Θ0 ⨟ empty ⊢ₚₛ PPt }}a)
      by (exact (proj2 (a_wf_pskl_univ_ghost_inv HwfP))).
    assert (HgκP : guarded_pskl (msubst_pskl κ PPt))
      by (eapply guarded_pskl_msubst_inc; eauto).
    pose proof HwfQb as HwfQ.
    assert (HlcQ : lc_bskl Q)
      by (apply lc_bskl_of_bskl_to_pskl; exact (a_wf_pskl_lc HwfQ)).
    assert (HgQ : guarded_bskl Q).
    { eapply ad_pat_consis_guarded_r;
        [ exact Hj | exact Hwfth | reflexivity | exact HgκP | exact HlcQ ]. }

    change ({{ Θ ⨟ Δ2 ⊢ᵣₚ (pskl_univ_ghost (msubst_pskl κ PPt)) ⊳ (bskl_to_pskl Q) }}ad) in Hrp.
    assert (Hrp' : {{ Θ ⨟ Δ2 ⊢ᵣₚ (msubst_pskl κ PPt) ⊳ (bskl_to_pskl Q) }}ad).
    { eapply ad_refine_pskl_univ_ghost_guarded_inv;
        [ exact Hwfth | exact Hrp | ].
      apply guarded_bskl_to_pskl. exact HgQ. }

    assert (Hthdec : (exists P0t, PP0 = pskl_univ_ghost P0t) \/
                     (forall P0t, PP0 <> pskl_univ_ghost P0t)).
    { destruct PP0; try (right; intros ? Hc0; discriminate).
      left; eexists; reflexivity. }
    destruct Hthdec as [[P0t ->] | Hnth0].
    +
      assert (Hg0t : guarded_pskl P0t) by (inversion HwfP0; assumption).
      assert (HwfP0t : {{ Θ0 ⨟ empty ⊢ₚₛ P0t }}a)
      by (exact (proj2 (a_wf_pskl_univ_ghost_inv HwfP0))).
      change ({{ Θ ⨟ Δ1 ⊢ᵣ (bskl_univ_ghost (pskl_to_bskl_inh (msubst_pskl κ P0t))) ⊳ Q }}ad)
        in Hrs.
      assert (Hrs' : {{ Θ ⨟ Δ1 ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0t)) ⊳ Q }}ad)
        by (eapply ad_refine_syn_univ_ghost_guarded_inv; eauto).
      assert (Hlt : mu_lt (mu_consis Θ κ P0t PPt Θ0)
                          (mu_consis Θ κ (pskl_univ_ghost P0t)
                                         (pskl_univ_ghost PPt) Θ0)).
      { unfold mu_consis. apply mu_lt_intro. left. unfold V_consis.
        pose proof (Vpskl_univ_ghost_lt Θ κ P0t).
        pose proof (Vpskl_univ_ghost_lt Θ κ PPt). lia. }
      destruct (IH _ Hlt) as [HcIH _].
      destruct (HcIH N Δ1 Δ2 Θ0 P0t PPt κ Θ Ψ Q eq_refl Hwf0 HwfP0t HwfPPt
                     Hrig Hnfd0 Hfaf Hinc Hwfth Hnfdth HΨ Hj Hrs' Hrp' HwfQ)
        as [P1 [Θ1 [Hc [Hnew Hopt']]]].
      exists (pskl_univ_ghost P1), Θ1. split.
      { apply a_consis__univ_ghost. exact Hc. }
      split; [ exact Hnew | ].
      intros κ1 Hid Hinc1.
      destruct (Hopt' κ1 Hid Hinc1) as [ζ [Hζ [Hie Hprec]]].
      exists ζ. split; [ exact Hζ | ]. split; [ exact Hie | ].
      unfold ad_precise in *. simpl.
      apply ad_refine_syn_univ_ghost_remove_intro. exact Hprec.
    +
      assert (Hg0 : guarded_pskl PP0).
      { destruct PP0 as [ | n0 | β10 | Pa0 Pb0 | Pb0 | | Pt0 ].
        - auto with fresco.
        - inversion HwfP0.
        - auto with fresco.
        - pose proof (a_wf_pskl_lc HwfP0) as Hlc0; inversion Hlc0; subst.
          apply guarded_pskl__arrow; assumption.
        -
          exfalso. simpl in Hrs.
          eapply ad_refine_syn_all_inh_guarded_absurd;
            [ exact Hwfth | exact Hrs | exact HgQ ].
        - exfalso; apply HneP0ghost; reflexivity.
        - exfalso; eapply Hnth0; reflexivity. }
      assert (Hlt : mu_lt (mu_consis Θ κ PP0 PPt Θ0)
                          (mu_consis Θ κ PP0 (pskl_univ_ghost PPt) Θ0)).
      { unfold mu_consis. apply mu_lt_intro. left. unfold V_consis.
        pose proof (Vpskl_univ_ghost_lt Θ κ PPt). lia. }
      destruct (IH _ Hlt) as [HcIH _].
      destruct (HcIH N Δ1 Δ2 Θ0 PP0 PPt κ Θ Ψ Q eq_refl Hwf0 HwfP0 HwfPPt
                     Hrig Hnfd0 Hfaf Hinc Hwfth Hnfdth HΨ Hj Hrs Hrp' HwfQb)
        as [P1 [Θ1 [Hc [Hnew Hopt']]]].
      exists P1, Θ1. split.
      { apply a_consis__univ_ghost2;
          [ exact Hg0 | exact HnfP0 | exact Hc ]. }
      split; [ exact Hnew | exact Hopt' ].

  -
    exfalso.
    destruct PP as [ | n | β1 | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    pose proof (a_wf_pskl_var_non_flex_tvar HwfP HnfP) as Hbtδ.
    assert (Hβ1κ : β1 `notin` dom κ)
      by (eapply a_inc_tvar_notin_dom; eauto).
    rewrite (msubst_lookup_notin κ Hβ1κ) in HeqS.
    simpl in HeqS. inversion HeqS; subst α.
    assert (HbtΘ : binds β1 abind_tvar Θ)
      by (eapply a_inc_binds_tvar; eauto).
    pose proof (binds_unique _ _ _ _ _ HbtΘ H (a_wf_aenv_uniq Hwfth))
      as Hcon; discriminate.

  -
    match goal with
    | Hb : binds _ (abind_flex_mono_def _) _ |- _ => rename Hb into Hbα
    end.
    assert (Hmτ : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; eauto).
    assert (Hdisj : (Δ1 `union` Δ2) ∩ ftvar_in_ptyp τ
                      [=] empty)
      by (apply (Hnfdth _ _ Hbα)).
    assert (HΔbt : forall α, α `in` (Δ1 `union` Δ2) ->
                             binds α abind_tvar Θ).
    { intros α0 Hα0. eapply a_inc_binds_tvar; [ exact Hinc | ].
      apply Hrig. exact Hα0. }

    assert (Hrs' : {{ Θ ⨟ Δ1 ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ PP0)) ⊳ (ptyp_to_bskl_syn τ) }}ad).
    { eapply ad_refine_syn_flex_target_unfold;
        [ exact Hwfth | exact Hbα
        | intros α0 Hα0; apply HΔbt; clear - Hα0; fsetdec
        | clear - Hdisj; fsetdec
        | exact Hrs ]. }
    assert (Hrp' : {{ Θ ⨟ Δ2 ⊢ᵣₚ (msubst_pskl κ PP) ⊳ (bskl_to_pskl (ptyp_to_bskl_syn τ)) }}ad).
    { rewrite bskl_to_pskl_ptyp_to_bskl_syn.
      eapply ad_refine_pskl_flex_target_unfold;
        [ exact Hwfth | exact Hbα
        | intros α0 Hα0; apply HΔbt; clear - Hα0; fsetdec
        | clear - Hdisj; fsetdec
        | exact Hrp ]. }

    destruct (IHHj N Δ1 Δ2 Θ0 PP0 PP κ IH Hwf0 HwfP0 HwfP Hrig Hnfd0 Hfaf
                   Hinc Hwfth Hnfdth HΨ HeqS HnfP HnfP0 HneP0ghost Hnthg
                   Hrs' Hrp'
                   ltac:(rewrite bskl_to_pskl_ptyp_to_bskl_syn;
                         apply a_wf_ptyp_to_wf_pskl;
                         eapply a_wf_aenv_binds_def_wf; eassumption))
      as [P1 [Θ1 [Hc [Hnew Hopt']]]].
    exists P1, Θ1. split; [ exact Hc | ].
    split; [ exact Hnew | ].
    intros κ1 Hid Hinc1.
    destruct (Hopt' κ1 Hid Hinc1) as [ζ [Hζ [Hie Hprec]]].
    exists ζ. split; [ exact Hζ | ]. split; [ exact Hie | ].

    unfold ad_precise in *. simpl.
    eapply ad_refine_syn__flex_r; [ exact Hbα | ].
    rewrite (bskl_to_pskl_ptyp_to_bskl_syn τ) in Hprec.
    rewrite (ptyp_to_bskl_inh_syn_eq Hmτ) in Hprec.
    exact Hprec.
Qed.

Lemma consis_complete_step : forall m,
  (forall m', mu_lt m' m -> complete_at m') ->
  consis_complete_at m.
Proof.
  intros m IH. unfold consis_complete_at.
  intros N Δ1 Δ2 Θ0 P0 P κ Θ Ψ Qb Hm Hwf0 HwfP0 HwfP Hrig Hnfd0 Hfaf
    Hinc Hwfth Hnfdth HΨ Hjoin Hrs Hrp HwfQb.
  subst m.

  destruct (pskl_eq_dec P0 pskl_ghost) as [-> | HneP0ghost].
  {
    assert (Hjoin' : {{ empty ⨟ Θ ⊢ˢ (pskl_to_uskl (msubst_pskl κ P)) ∼ Qb }}ad)
      by (eapply ad_pat_consis_psi_cong; [ exact Hjoin | exact HΨ ]).
    change ({{ Θ ⨟ Δ1 ⊢ᵣ bskl_ghost ⊳ Qb }}ad) in Hrs.

    assert (HQb : pskl_to_bskl_syn (bskl_to_pskl Qb) = Qb).
    { inversion Hrs; subst.
      - rewrite bskl_to_pskl_pskl_to_bskl_syn. reflexivity.
      - simpl. reflexivity. }

    assert (Hside : forall α, α `in` Δ1 -> α `notin` ftvar_in_pskl P).
    { intros α HinΔ1 HinP.
      assert (HbX0 : binds α abind_tvar Θ0)
        by (apply Hrig; clear - HinΔ1; fsetdec).
      assert (HbX : binds α abind_tvar Θ)
        by (eapply a_inc_binds_tvar; eauto).
      assert (HXnd : α `notin` dom κ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      assert (Hdefs : forall β τ, binds β (abind_flex_mono_def τ) Θ ->
                                  α `notin` ftvar_in_ptyp τ).
      { intros β τ Hb. pose proof (Hnfdth _ _ Hb) as Hd.
        clear - Hd HinΔ1. fsetdec. }
      assert (HninQb : α `notin` ftvar_in_bskl Qb).
      { inversion Hrs; subst.
        -
          match goal with
          | Hint : Δ1 ∩ (ftvar_in_pskl ?Pf) [=] empty |- _ =>
              pose proof (ftvar_in_bskl_syn Pf) as Hfe;
              clear - Hint HinΔ1 Hfe; fsetdec
          end.
        -
          simpl.
          match goal with
          | Hbr : binds ?α0 (abind_flex_mono_def _) Θ |- _ =>
              assert (Hne : α <> α0)
                by (intro Heq; subst;
                    pose proof (binds_unique _ _ _ _ _ HbX Hbr
                                  (a_wf_aenv_uniq Hwfth)) as Hcon;
                    discriminate)
          end.
          clear - Hne; fsetdec. }
      assert (HinκP : α `in` ftvar_in_pskl (msubst_pskl κ P))
        by (apply msubst_pskl_ftv_keep; assumption).
      assert (HninS : α `notin`
                ftvar_in_uskl (pskl_to_uskl (msubst_pskl κ P))).
      { eapply ad_pat_consis_rigid_ftv_rev;
          [ exact Hwfth | exact HbX | exact Hdefs | exact Hjoin'
          | exact HninQb ]. }
      pose proof (ftvar_in_uskl_pskl (msubst_pskl κ P)) as Hfe2.
      clear - HninS HinκP Hfe2. fsetdec. }
    exists P, Θ0. split.
    { apply a_consis__ghost_r.
      apply inter_empty_pointwise. exact Hside. }
    split; [ intros γ Hγ; left; exact Hγ | ].
    intros κ1 Hid Hinc1. exists κ.
    destruct (opt_axiom_factor Hwf0 Hid Hinc1 Hinc) as [Hout Hfact].
    split; [ exact Hout | ]. split; [ exact Hfact | ].
    assert (HwfκP : {{ Θ ⨟ empty ⊢ₚₛ (msubst_pskl κ P) }}a).
    { eapply a_wf_pskl_msubst_inc;
        [ exact Hinc | exact Hwf0 | exact HwfP
        | intros α Hα; exfalso; clear - Hα; fsetdec
        | intros β γ _ _ _; clear; fsetdec ]. }
    unfold ad_precise.
    rewrite bskl_to_pskl_msubst_bskl.
    rewrite bskl_to_pskl_pskl_to_bskl_syn.
    eapply ad_refine_syn_extend_ftv;
      [ eapply refine_join_reinherit with (Θj := Θ);
          [ exact Hrp | exact Hwfth | exact Hwfth
          | intros x b Hb; exact Hb
          | exact HwfκP
          | rewrite HQb; exact Hjoin' ]
      | ].
    intros α1 Hα1.
    destruct (AtomSetProperties.In_dec α1 Δ2) as [Hα1Δ2 | Hα1Δ2];
      [ left; exact Hα1Δ2 | right ].
    assert (Hα1Δ1 : α1 `in` Δ1) by (clear - Hα1 Hα1Δ2; fsetdec).
    assert (Hbγ : binds α1 abind_tvar Θ)
      by (eapply a_inc_binds_tvar; [ exact Hinc | ];
          apply Hrig; clear - Hα1Δ1; fsetdec).
    split.
    + assert (Hnq : α1 `notin` ftvar_in_bskl Qb)
        by (eapply ad_refine_syn_ghost_src_target_ftv;
            [ exact Hrs | exact Hwfth
            | clear - Hα1Δ1; fsetdec | exact Hbγ ]).
      pose proof (ftvar_in_bskl_inh (bskl_to_pskl Qb)) as Hfe.
      pose proof (ftvar_bskl_to_pskl Qb) as Hfe2.
      clear - Hnq Hfe Hfe2. fsetdec.
    + intros β τ Hb.
      pose proof (Hnfdth β τ Hb) as Hi.
      clear - Hi Hα1Δ1. fsetdec. }

  destruct (a_flex_shape_dec HwfP) as [[β [-> Hfβ]] | HnfP].
  { destruct (a_flex_shape_dec HwfP0) as [[β10 [-> Hfδ0]] | HnfP0].
    -
      assert (Hjoin' : {{ empty ⨟ Θ ⊢ˢ
                (pskl_to_uskl (msubst_pskl κ (pskl_var_f β))) ∼ Qb }}ad)
        by (eapply ad_pat_consis_psi_cong; [ exact Hjoin | exact HΨ ]).
      assert (Hjoin'' : {{ empty ⨟ Θ ⊢ˢ
                (ptyp_to_uskl_syn (msubst_lookup κ β)) ∼ Qb }}ad).
      { replace (msubst_pskl κ (pskl_var_f β))
          with (ptyp_to_pskl (msubst_lookup κ β)) in Hjoin' by reflexivity.
        rewrite pskl_to_uskl_ptyp in Hjoin'. exact Hjoin'. }
      assert (Hmβ : mono_ptyp (msubst_lookup κ β))
        by (eapply a_inc_lookup_mono; exact Hinc).
      assert (Hmδ0 : mono_ptyp (msubst_lookup κ β10))
        by (eapply a_inc_lookup_mono; exact Hinc).
      replace (msubst_pskl κ (pskl_var_f β10))
        with (ptyp_to_pskl (msubst_lookup κ β10)) in Hrs by reflexivity.
      rewrite (ptyp_to_bskl_inh_syn_eq Hmδ0) in Hrs.
      destruct (refine_mono_join Hrs Hwfth (A := msubst_lookup κ β10)
                  eq_refl Hmδ0) as [C [HmC [HeqQb HeqδC]]].
      subst Qb.
      destruct (consis_mono_join Hjoin'' Hwfth (A := msubst_lookup κ β)
                  eq_refl Hmβ) as [C' [HmC' [HeqQb' HeqβC']]].
      assert (HCC : C = C')
        by (apply ptyp_to_bskl_syn_inj; auto).
      subst C'.
      assert (Heqββ1 : {{ Θ ⊢ (msubst_lookup κ β) ≡ᵗ (msubst_lookup κ β10) }}a).
      { eapply a_tyequiv__trans; [ exact HeqβC' | ].
        apply a_tyequiv__sym; exact HeqδC. }
      assert (Hlt : mu_lt (mu_unify Θ κ β β10 Θ0)
                          (mu_consis Θ κ (pskl_var_f β10) (pskl_var_f β) Θ0)).
      { unfold mu_unify, mu_consis. apply mu_lt_intro. right.
        split; [ symmetry; apply V_flex | ].
        right. split; [ reflexivity | left; lia ]. }
      destruct (IH _ Hlt) as [_ [HuIH _]].
      destruct (HuIH N Θ0 β β10 κ Θ eq_refl Hwf0 Hfβ Hfδ0 Hinc Hwfth Heqββ1)
        as [Θ1 [Hu [Hnew Hopt']]].
      exists (pskl_var_f β), Θ1. split.
      { apply a_consis__flex. exact Hu. }
      split; [ exact Hnew | ].
      intros κ1 Hid Hinc1.
      destruct (Hopt' κ1 Hid Hinc1) as [ζ [Hζ Hie]].
      exists ζ. split; [ exact Hζ | ]. split; [ exact Hie | ].

      assert (Hbtβ0 : a_binds_tvar β Θ0) by (right; exact Hfβ).
      assert (Hwfvβ : a_wf_ptyp Θ1 (msubst_lookup κ1 β))
        by (eapply a_inc_lookup_wf; [ exact Hinc1 | exact Hwf0 | exact Hbtβ0 ]).
      rewrite (msubst_lookup_id β Hid) in Hwfvβ.
      assert (HbtβΘ1 : a_binds_tvar β Θ1) by (inversion Hwfvβ; assumption).
      destruct (a_unify_sound Hu Hwf0) as [_ [Hwf1 _]].
      try unfold ad_precise.
      eapply consis_precise_via_join with (Θ0 := Θ0) (κ1 := κ1);
        [ exact Hwfth | exact Hfβ | exact Hinc | exact HbtβΘ1
        | exact Hζ | exact Hwf1 | exact Hie
        | eapply a_inc_flex_dom; [ exact Hinc1 | exact Hwf0 | exact Hfβ ]
        | apply (msubst_lookup_id β Hid)
        | exact Hjoin' ].
    -
      assert (Hjoin' : {{ empty ⨟ Θ ⊢ˢ
                (pskl_to_uskl (msubst_pskl κ (pskl_var_f β))) ∼ Qb }}ad)
        by (eapply ad_pat_consis_psi_cong; [ exact Hjoin | exact HΨ ]).
      assert (Hjoin'' : {{ empty ⨟ Θ ⊢ˢ
                (ptyp_to_uskl_syn (msubst_lookup κ β)) ∼ Qb }}ad).
      { replace (msubst_pskl κ (pskl_var_f β))
          with (ptyp_to_pskl (msubst_lookup κ β)) in Hjoin' by reflexivity.
        rewrite pskl_to_uskl_ptyp in Hjoin'. exact Hjoin'. }
      assert (Hmβ : mono_ptyp (msubst_lookup κ β))
        by (eapply a_inc_lookup_mono; exact Hinc).

      destruct (consis_mono_join Hjoin'' Hwfth (A := msubst_lookup κ β)
                  eq_refl Hmβ) as [C [HmC [HeqQb HeqβC]]].
      subst Qb.

      assert (Hbr : {{ empty ⨟ Θ ⊢ˢ (pskl_to_uskl (msubst_pskl κ P0))
                      ∼ (ptyp_to_bskl_syn C) }}ad).
      { eapply refine_inh_mono_consis;
          [ exact Hrs | exact Hwfth
          | apply mono_ptyp_to_bskl_syn; exact HmC
          | reflexivity
          | eapply ad_pat_consis_target_binds;
              [ exact Hjoin'' | apply uskl_no_ghost_ptyp ] ]. }

      assert (Hvβ : forall α, α `in` ftvar_in_ptyp (msubst_lookup κ β) ->
                              a_binds_tvar α Θ).
      { intros α Hα. eapply a_wf_ptyp_ftv_tvarish; [ | exact Hα ].
        eapply a_inc_lookup_wf;
          [ exact Hinc | exact Hwf0 | right; exact Hfβ ]. }
      destruct (tyequiv_mono_consis_transport_q HeqβC Hwfth Hmβ Hvβ)
        as [Htq _].
      assert (Hjoin3 : {{ empty ⨟ Θ ⊢ˢ (pskl_to_uskl (msubst_pskl κ P0))
                        ∼ (ptyp_to_bskl_syn (msubst_lookup κ β)) }}ad)
        by (apply Htq; exact Hbr).

      assert (Hlt : mu_lt (mu_assign Θ κ β P0 nil Θ0)
                          (mu_consis Θ κ P0 (pskl_var_f β) Θ0)).
      { unfold mu_assign, mu_consis. apply mu_lt_intro. right.
        split; [ symmetry; apply V_flexL | ].
        right. split; [ reflexivity | left; lia ]. }
      assert (Hdom : dom (nil : aenv) [<=] ftvar_in_pskl P0)
        by (simpl; clear; fsetdec).
      destruct (IH _ Hlt) as [_ [_ HaIH]].
      destruct (HaIH N Θ0 nil β P0 κ Θ eq_refl a_decls__nil Hwf0 Hfβ
                     HwfP0 HnfP0 Hdom Hinc Hwfth Hjoin3)
        as [Θ1 [Ha [Hnew Hopt']]].
      exists (pskl_var_f β), Θ1. split.
      { apply a_consis__flex_l; [ exact HnfP0 | exact HneP0ghost | exact Ha ]. }
      split;
        [ intros γ Hγ; destruct (Hnew γ Hγ) as [Hin | Hni];
          [ left; simpl_env in Hin; exact Hin | right; exact Hni ] | ].
      intros κ1 Hid Hinc1.
      destruct (Hopt' κ1 Hid Hinc1) as [ζ [Hζ Hie]].
      exists ζ. split; [ exact Hζ | ]. split; [ exact Hie | ].

      assert (Hbtβ0 : a_binds_tvar β Θ0) by (right; exact Hfβ).
      assert (Hwfvβ : a_wf_ptyp Θ1 (msubst_lookup κ1 β))
        by (eapply a_inc_lookup_wf; [ exact Hinc1 | exact Hwf0 | exact Hbtβ0 ]).
      rewrite (msubst_lookup_id β Hid) in Hwfvβ.
      assert (HbtβΘ1 : a_binds_tvar β Θ1) by (inversion Hwfvβ; assumption).
      assert (Hwf1 : {{ ⊢ Θ1 }}a)
        by (eapply a_assign_preserves_wf;
              [ exact Ha | apply a_decls__nil | exact Hwf0 | exact HwfP0 ]).
      try unfold ad_precise.
      eapply consis_precise_via_join with (Θ0 := Θ0) (κ1 := κ1);
        [ exact Hwfth | exact Hfβ | exact Hinc | exact HbtβΘ1
        | exact Hζ | exact Hwf1 | exact Hie
        | eapply a_inc_flex_dom; [ exact Hinc1 | exact Hwf0 | exact Hfβ ]
        | apply (msubst_lookup_id β Hid)
        | exact Hjoin' ]. }

  destruct (a_flex_shape_dec HwfP0) as [[β10 [-> Hfδ0]] | HnfP0].
  {
    destruct (pskl_eq_dec P pskl_ghost) as [-> | HnePhole].
    { exists (pskl_var_f β10), Θ0. split.
      { apply a_consis__ghost.
        assert (Hβ2 : β10 `notin` Δ2).
        { intros Hin.
          assert (Hbt : binds β10 abind_tvar Θ0)
            by (apply Hrig; clear - Hin; fsetdec).
          destruct Hfδ0 as [Hb | [τ Hb]];
            pose proof (binds_unique _ _ _ _ _ Hbt Hb (a_wf_aenv_uniq Hwf0))
              as Hcon; discriminate. }
        simpl. clear - Hβ2. fsetdec. }
      split; [ intros γ Hγ; left; exact Hγ | ].
      intros κ1 Hid Hinc1. exists κ.
      destruct (opt_axiom_factor Hwf0 Hid Hinc1 Hinc) as [Hout Hfact].
      split; [ exact Hout | ]. split; [ exact Hfact | ].
      assert (HbtδΘ0 : a_binds_tvar β10 Θ0) by (right; exact Hfδ0).
      unfold ad_precise.
      eapply consis_precise_via_refine with (Θ0 := Θ0) (κ1 := κ1);
        [ exact Hwfth | exact Hfδ0 | exact Hinc | exact HbtδΘ0
        | exact Hinc | exact Hwf0 | exact Hfact
        | eapply a_inc_flex_dom; [ exact Hinc1 | exact Hwf0 | exact Hfδ0 ]
        | apply (msubst_lookup_id β10 Hid)
        | exact Hrs ]. }
    assert (Hjoin' : {{ empty ⨟ Θ ⊢ˢ
              (pskl_to_uskl (msubst_pskl κ P)) ∼ Qb }}ad)
      by (eapply ad_pat_consis_psi_cong; [ exact Hjoin | exact HΨ ]).
    assert (Hmδ0 : mono_ptyp (msubst_lookup κ β10))
      by (eapply a_inc_lookup_mono; exact Hinc).

    pose proof Hrs as Hrs2.
    replace (msubst_pskl κ (pskl_var_f β10))
      with (ptyp_to_pskl (msubst_lookup κ β10)) in Hrs2 by reflexivity.
    rewrite (ptyp_to_bskl_inh_syn_eq Hmδ0) in Hrs2.
    destruct (refine_mono_join Hrs2 Hwfth (A := msubst_lookup κ β10)
                eq_refl Hmδ0) as [C [HmC [HeqQb HeqδC]]].

    assert (Hvδ : forall α, α `in` ftvar_in_ptyp (msubst_lookup κ β10) ->
                            a_binds_tvar α Θ).
    { intros α Hα. eapply a_wf_ptyp_ftv_tvarish; [ | exact Hα ].
      eapply a_inc_lookup_wf;
        [ exact Hinc | exact Hwf0 | right; exact Hfδ0 ]. }
    destruct (tyequiv_mono_consis_transport_q HeqδC Hwfth Hmδ0 Hvδ)
      as [Htq _].
    assert (Hjoin3 : {{ empty ⨟ Θ ⊢ˢ (pskl_to_uskl (msubst_pskl κ P))
                      ∼ (ptyp_to_bskl_syn (msubst_lookup κ β10)) }}ad).
    { apply Htq. rewrite <- HeqQb. exact Hjoin'. }

    assert (Hlt : mu_lt (mu_assign Θ κ β10 P nil Θ0)
                        (mu_consis Θ κ (pskl_var_f β10) P Θ0)).
    { unfold mu_assign, mu_consis. apply mu_lt_intro. right.
      split; [ symmetry; apply V_flexR | ].
      right. split; [ reflexivity | left; lia ]. }
    assert (Hdom : dom (nil : aenv) [<=] ftvar_in_pskl P)
      by (simpl; clear; fsetdec).
    destruct (IH _ Hlt) as [_ [_ HaIH]].
    destruct (HaIH N Θ0 nil β10 P κ Θ eq_refl a_decls__nil Hwf0 Hfδ0
                   HwfP HnfP Hdom Hinc Hwfth Hjoin3)
      as [Θ1 [Ha [Hnew Hopt']]].
    exists (pskl_var_f β10), Θ1. split.
    { apply a_consis__flex_r; [ exact HnfP | exact HnePhole | exact Ha ]. }
    split;
      [ intros γ Hγ; destruct (Hnew γ Hγ) as [Hin | Hni];
        [ left; simpl_env in Hin; exact Hin | right; exact Hni ] | ].
    intros κ1 Hid Hinc1.
    destruct (Hopt' κ1 Hid Hinc1) as [ζ [Hζ Hie]].
    exists ζ. split; [ exact Hζ | ]. split; [ exact Hie | ].

    assert (Hbtδ00 : a_binds_tvar β10 Θ0) by (right; exact Hfδ0).
    assert (Hwfvδ : a_wf_ptyp Θ1 (msubst_lookup κ1 β10))
      by (eapply a_inc_lookup_wf; [ exact Hinc1 | exact Hwf0 | exact Hbtδ00 ]).
    rewrite (msubst_lookup_id β10 Hid) in Hwfvδ.
    assert (HbtδΘ1 : a_binds_tvar β10 Θ1) by (inversion Hwfvδ; assumption).
    assert (Hwf1 : {{ ⊢ Θ1 }}a)
      by (eapply a_assign_preserves_wf;
            [ exact Ha | apply a_decls__nil | exact Hwf0 | exact HwfP ]).
    try unfold ad_precise.
    eapply consis_precise_via_refine with (Θ0 := Θ0) (κ1 := κ1);
      [ exact Hwfth | exact Hfδ0 | exact Hinc | exact HbtδΘ1
      | exact Hζ | exact Hwf1 | exact Hie
      | eapply a_inc_flex_dom; [ exact Hinc1 | exact Hwf0 | exact Hfδ0 ]
      | apply (msubst_lookup_id β10 Hid)
      | exact Hrs ]. }

  assert (Hthdec : (exists P0', P0 = pskl_univ_ghost P0') \/
                   (forall P0', P0 <> pskl_univ_ghost P0')).
  { destruct P0; try (right; intros ? Hc; discriminate).
    left. eexists. reflexivity. }
  destruct Hthdec as [[P0' ->] | Hnth].
  { pose proof (a_wf_pskl_lc HwfP) as HlcP.
    assert (Hgdec : guarded_pskl P \/ ~ guarded_pskl P).
    { destruct P; try (right; intro Hg; inversion Hg; fail).
      - left; apply guarded_pskl__unit.
      - left; apply guarded_pskl__var.
      - left; inversion HlcP; apply guarded_pskl__arrow; assumption. }
    destruct Hgdec as [HgP | HngP].
    -
      assert (HwfP0' : {{ Θ0 ⨟ empty ⊢ₚₛ P0' }}a)
        by (exact (proj2 (a_wf_pskl_univ_ghost_inv HwfP0))).
      assert (Hgκ : guarded_pskl (msubst_pskl κ P))
        by (eapply guarded_pskl_msubst_inc; eauto).
      assert (HlcQb : lc_bskl Qb)
        by (apply lc_bskl_of_bskl_to_pskl; exact (a_wf_pskl_lc HwfQb)).
      assert (HgQb : guarded_bskl Qb)
        by (eapply ad_pat_consis_guarded_r; eauto).
      change ({{ Θ ⨟ Δ1 ⊢ᵣ (bskl_univ_ghost (pskl_to_bskl_inh (msubst_pskl κ P0'))) ⊳ Qb }}ad)
        in Hrs.
      assert (Hrs' : {{ Θ ⨟ Δ1 ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0')) ⊳ Qb }}ad)
        by (eapply ad_refine_syn_univ_ghost_guarded_inv; eauto).
      assert (Hlt : mu_lt (mu_consis Θ κ P0' P Θ0)
                          (mu_consis Θ κ (pskl_univ_ghost P0') P Θ0)).
      { unfold mu_consis. apply mu_lt_intro. left.
        unfold V_consis.
        pose proof (Vpskl_univ_ghost_lt Θ κ P0'). lia. }
      destruct (IH _ Hlt) as [HcIH _].
      destruct (HcIH N Δ1 Δ2 Θ0 P0' P κ Θ Ψ Qb eq_refl Hwf0 HwfP0' HwfP
                     Hrig Hnfd0 Hfaf Hinc Hwfth Hnfdth HΨ Hjoin Hrs' Hrp HwfQb)
        as [P1 [Θ1 [Hc [Hnew Hopt']]]].
      exists P1, Θ1. split.
      { apply a_consis__univ_ghost_r;
          [ exact HgP | exact HnfP | exact Hc ]. }
      split; [ exact Hnew | exact Hopt' ].
    -
      eapply (consis_complete_core Hjoin);
        try eassumption; try reflexivity.
      intros P0'' Heq0 Hg. inversion Heq0; subst P0''. exact (HngP Hg). }

  eapply (consis_complete_core Hjoin);
    try eassumption; try reflexivity.
  intros P0'' Heq0 Hg. exact (Hnth P0'' Heq0).
Qed.
