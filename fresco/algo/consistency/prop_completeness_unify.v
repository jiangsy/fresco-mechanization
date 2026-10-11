(** Unification completeness step. *)

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

(* ===================================================================== *)
(*  §3  The three induction steps (one per part of the paper's proof)     *)
(* ===================================================================== *)

(** Removing a skipped binding preserves the two solution images and
    decreases the context component of the unification measure. *)
Local Lemma unify_skip_strengthen :
  forall Θ0' Ξ α1 bd bd' Θ2 κ α β,
  {{ ⊢ Θ0' }}a -> {{ ⊢ (Ξ ++ (α1 ~ bd') ++ Θ2) }}a ->
  κ ∷ Θ0' ⊑ Θ2 -> a_flex_tvar Θ0' α -> a_flex_tvar Θ0' β ->
  {{ (Ξ ++ (α1 ~ bd') ++ Θ2) ⊢
      (msubst_lookup κ α) ≡ᵗ (msubst_lookup κ β) }}a ->
  {{ ⊢ Θ2 }}a /\
  {{ Θ2 ⊢ (msubst_lookup κ α) ≡ᵗ (msubst_lookup κ β) }}a /\
  mu_lt (mu_unify Θ2 κ α β Θ0')
        (mu_unify (Ξ ++ (α1 ~ bd') ++ Θ2) κ α β ((α1 ~ bd) ++ Θ0')).
Proof.
  intros Θ0' Ξ α1 bd bd' Θ2 κ α β Hwf0 Hwfth Hinc' Hfα0 Hfβ0 Heq.
  assert (Hwfth2 : {{ ⊢ Θ2 }}a).
  { rewrite <- app_assoc in Hwfth.
    apply a_wf_aenv_strip_prefix in Hwfth. exact Hwfth. }
  assert (Hwflα : a_wf_ptyp Θ2 (msubst_lookup κ α)).
  { eapply a_inc_lookup_wf; [exact Hinc' | exact Hwf0 | right; exact Hfα0]. }
  assert (Hwflβ : a_wf_ptyp Θ2 (msubst_lookup κ β)).
  { eapply a_inc_lookup_wf; [exact Hinc' | exact Hwf0 | right; exact Hfβ0]. }
  split; [exact Hwfth2 | ]. split.
  - eapply a_tyequiv_strengthen_mono_mid;
      [ exact Hwfth | exact Hwflα
      | eapply a_inc_lookup_mono; exact Hinc'
      | exact Hwflβ
      | eapply a_inc_lookup_mono; exact Hinc'
      | exact Heq ].
  - assert (Huniq : uniq (Ξ ++ (α1 ~ bd') ++ Θ2))
      by (apply a_wf_aenv_uniq; exact Hwfth).
    unfold mu_unify. apply mu_lt_intro. right. split.
    + unfold V_unify.
      rewrite (@Vvar_strengthen_mid Ξ α1 bd' Θ2 κ α Huniq Hwflα).
      rewrite (@Vvar_strengthen_mid Ξ α1 bd' Θ2 κ β Huniq Hwflβ).
      reflexivity.
    + left. simpl. lia.
Qed.

(** Part 2 of the paper's proof (:2260-2401): unification of flexible
    variables, by a walk of the context [Θ0] (n strictly decreases on the
    walk edges; the Flex-Flex-Assign back-edge re-enters part 1 with [V]
    exactly constant and [n] one smaller). *)
Lemma unify_complete_step : forall m,
  (forall m', mu_lt m' m -> complete_at m') ->
  unify_complete_at m.
Proof.
  intros m IH. unfold unify_complete_at.
  intros N Θ0 α β κ Θ Hm Hwf Hfα Hfβ Hinc Hwfth Heq. subst m.
  destruct (α == β) as [-> | Hne].
  { (* Flex-Flex-Id : axiom, Θ1 = Θ0; ζ := κ. *)
    exists Θ0. split; [ apply a_unify__flex_id; exact Hfα | ].
    split; [ intros γ Hγ; left; exact Hγ | ].
    intros κ1 Hid Hinc1. exists κ.
    exact (opt_axiom_factor Hwf Hid Hinc1 Hinc). }
  assert (Hβα : β <> α) by auto.
  destruct Θ0 as [ | [α1 b] Θ0' ].
  { exfalso. destruct Hfα as [Hb | [τ Hb]]; inversion Hb. }
  destruct b as [ | A | Q | | τdef ].
  - (* head [α1 ~ tvar] : Flex-Flex-Skip' (rigid). *)
    inversion Hwf as [ | | | | | γh Θh Hnd Hwf0 ]; subst.
    assert (Hnonflex : abind_nonflex abind_tvar)
      by (unfold abind_nonflex; split; intros; discriminate).
    assert (Hfα0 : a_flex_tvar Θ0' α).
    { apply a_flex_tvar_cons_nonflex in Hfα; assumption. }
    assert (Hfβ0 : a_flex_tvar Θ0' β).
    { apply a_flex_tvar_cons_nonflex in Hfβ; assumption. }
    apply a_inc_tvar_inv in Hinc as [Ξ [Θ2 [-> [HΞ Hinc']]]].
    destruct (@unify_skip_strengthen Θ0' Ξ α1 abind_tvar abind_tvar Θ2 κ α β
                Hwf0 Hwfth Hinc' Hfα0 Hfβ0 Heq)
      as (Hwfth2 & Heq2 & Hlt).
    destruct (IH _ Hlt) as [_ [HuIH _]].
    destruct (HuIH (add α1 N) Θ0' α β κ Θ2 eq_refl Hwf0 Hfα0 Hfβ0
                   Hinc' Hwfth2 Heq2) as [Θ1' [Hu [Hnew Hopt']]].
    exists ((α1 ~ abind_tvar) ++ Θ1'). split.
    { apply a_unify__skip_other;
        [ left; reflexivity | (* the popped head misses the sub-run's output: the
             relayed avoid set [add α1 N] says so *)
          eapply avoid_head_miss; [ exact Hnew | exact Hnd ] | exact Hu ]. }
    split; [ eapply avoid_relay_cons; exact Hnew | ].
    intros κ1 Hid Hinc1.
    assert (Hinc1' : κ1 ∷ Θ0' ⊑ Θ1')
      by (eapply a_inc_id_mid_strip; [ left; reflexivity | exact Hinc1 ]).
    destruct (Hopt' κ1 Hid Hinc1') as [ζ' [Hζ' Hie']].
    exists ζ'. split.
    + apply a_inc__tvar; [ exact Hζ' | exact HΞ ].
    + apply a_inc_equiv__tvar; [ exact Hie' | exact HΞ ].
  - (* head [x ~ var_typ A] : Flex-Flex-Skip' (semantic type middle). *)
    destruct (a_wf_aenv_var_typ_inv Hwf) as [Hnd [HwfA Hwf0]].
    assert (Hnonflex : abind_nonflex (abind_var_typ A))
      by (apply abind_is_tm_nonflex; simpl; exact I).
    assert (Hfα0 : a_flex_tvar Θ0' α).
    { apply a_flex_tvar_cons_nonflex in Hfα; assumption. }
    assert (Hfβ0 : a_flex_tvar Θ0' β).
    { apply a_flex_tvar_cons_nonflex in Hfβ; assumption. }
    apply a_inc_var_inv in Hinc as [Ξ [A' [Θ2 [-> [HA'eq [HΞ Hinc']]]]]].
    destruct (@unify_skip_strengthen Θ0' Ξ α1 (abind_var_typ A) (abind_var_typ A') Θ2 κ α β
                Hwf0 Hwfth Hinc' Hfα0 Hfβ0 Heq)
      as (Hwfth2 & Heq2 & Hlt).
    destruct (IH _ Hlt) as [_ [HuIH _]].
    destruct (HuIH (add α1 N) Θ0' α β κ Θ2 eq_refl Hwf0 Hfα0 Hfβ0
                   Hinc' Hwfth2 Heq2) as [Θ1' [Hu [Hnew Hopt']]].
    exists ((α1 ~ abind_var_typ A) ++ Θ1'). split.
    { apply a_unify__skip_other;
        [ right; left; exists A; reflexivity | (* the popped head misses the sub-run's output: the
             relayed avoid set [add α1 N] says so *)
          eapply avoid_head_miss; [ exact Hnew | exact Hnd ] | exact Hu ]. }
    split; [ eapply avoid_relay_cons; exact Hnew | ].
    intros κ1 Hid Hinc1.
    assert (Hinc1' : κ1 ∷ Θ0' ⊑ Θ1')
      by (eapply a_inc_id_mid_strip;
          [ right; left; exists A; reflexivity | exact Hinc1 ]).
    destruct (Hopt' κ1 Hid Hinc1') as [ζ' [Hζ' Hie']].
    destruct (a_unify_sound Hu Hwf0)
      as [[[w [Hidw Hincw]] _] [Hwf1' _]].
    assert (Hbridge : {{ Θ2 ⊢ A' ≡ᵗ (msubst_ptyp ζ' A) }}a).
    { eapply a_tyequiv__trans; [ exact HA'eq | ].
      rewrite <- (msubst_compose_id_ptyp Hwf0 Hwf1' Hid Hinc1' Hζ' HwfA).
      eapply a_inc_equiv_msubst_ptyp;
        [ exact HwfA | exact Hie' | exact Hwf0
        | eapply a_inc_msubst_lc; exact Hinc'
        | eapply msubst_lc_compose;
            [ eapply a_inc_msubst_lc; exact Hζ'
            | eapply is_id_msubst_values_lc; exact Hid ] ]. }
    exists ζ'. split.
    + apply a_inc__var; [ exact Hζ' | exact Hbridge | exact HΞ ].
    + apply a_inc_equiv__var; [ exact Hie' | exact HA'eq | exact HΞ ].
  - (* head [x ~ var_skl Q] : Flex-Flex-Skip' (semantic skeleton middle). *)
    destruct (a_wf_aenv_var_skl_inv Hwf) as [Hnd [HwfQ Hwf0]].
    assert (Hnonflex : abind_nonflex (abind_var_skl Q))
      by (apply abind_is_tm_nonflex; simpl; exact I).
    assert (Hfα0 : a_flex_tvar Θ0' α).
    { apply a_flex_tvar_cons_nonflex in Hfα; assumption. }
    assert (Hfβ0 : a_flex_tvar Θ0' β).
    { apply a_flex_tvar_cons_nonflex in Hfβ; assumption. }
    apply a_inc_var_skl_inv in Hinc as [Ξ [P' [Θ2 [-> [HP'eq [HΞ Hinc']]]]]].
    destruct (@unify_skip_strengthen Θ0' Ξ α1 (abind_var_skl Q) (abind_var_skl P') Θ2 κ α β
                Hwf0 Hwfth Hinc' Hfα0 Hfβ0 Heq)
      as (Hwfth2 & Heq2 & Hlt).
    destruct (IH _ Hlt) as [_ [HuIH _]].
    destruct (HuIH (add α1 N) Θ0' α β κ Θ2 eq_refl Hwf0 Hfα0 Hfβ0
                   Hinc' Hwfth2 Heq2) as [Θ1' [Hu [Hnew Hopt']]].
    exists ((α1 ~ abind_var_skl Q) ++ Θ1'). split.
    { apply a_unify__skip_other;
        [ right; right; exists Q; reflexivity | (* the popped head misses the sub-run's output: the
             relayed avoid set [add α1 N] says so *)
          eapply avoid_head_miss; [ exact Hnew | exact Hnd ] | exact Hu ]. }
    split; [ eapply avoid_relay_cons; exact Hnew | ].
    intros κ1 Hid Hinc1.
    assert (Hinc1' : κ1 ∷ Θ0' ⊑ Θ1')
      by (eapply a_inc_id_mid_strip;
          [ right; right; exists Q; reflexivity | exact Hinc1 ]).
    destruct (Hopt' κ1 Hid Hinc1') as [ζ' [Hζ' Hie']].
    destruct (a_unify_sound Hu Hwf0)
      as [[[w [Hidw Hincw]] _] [Hwf1' _]].
    assert (Hbridge : {{ Θ2 ⊢ P' ≡ˢ (msubst_pskl ζ' Q) }}a).
    { eapply a_pskl_tyequiv__trans; [ exact HP'eq | ].
      rewrite <- (msubst_compose_id_pskl Hwf0 Hwf1' Hid Hinc1' Hζ'
                    (a_scope_pskl_of_wf HwfQ)).
      eapply a_inc_equiv_msubst_pskl;
        [ exact (a_scope_pskl_of_wf HwfQ) | exact Hie' | exact Hwf0
        | eapply a_inc_msubst_lc; exact Hinc'
        | eapply msubst_lc_compose;
            [ eapply a_inc_msubst_lc; exact Hζ'
            | eapply is_id_msubst_values_lc; exact Hid ] ]. }
    exists ζ'. split.
    + apply a_inc__var_skl; [ exact Hζ' | exact Hbridge | exact HΞ ].
    + apply a_inc_equiv__var_skl; [ exact Hie' | exact HP'eq | exact HΞ ].
  - (* head [α1̂] undefined flexible : Flex-Flex-L / Flex-Flex-R / Skip. *)
    inversion Hwf as [ | γh Θh Hnd Hwf0 | | | | ]; subst.
    destruct (α1 == α) as [-> | Hα1α].
    + (* Flex-Flex-L : α̂ ≔ β̂; axiom, ζ := κ. *)
      inversion Hinc as [ | Θs κs Θt αs τ Hinc' Hwfτ Hmτ [Heqα Heqκ] Heqt
                        | | | | ]; subst.
      assert (Hfβ0 : a_flex_tvar Θ0' β)
        by (eapply (proj1 (a_flex_tvar_cons_other _ _ Hβα)); exact Hfβ).
      exists ((α ~ abind_flex_mono_def (ptyp_var_f β)) ++ Θ0'). split.
      { apply a_unify__flex_l; [ exact Hne | exact Hfβ0 ]. }
      split; [ apply avoid_same_dom | ].
      intros κ1 Hid Hinc1. exists ((α, τ) :: κs). split.
      * apply a_inc__flex_def; auto.
        rewrite msubst_lookup_cons_eq in Heq.
        rewrite (msubst_lookup_cons_neq τ κs Hβα) in Heq.
        exact Heq.
      * rewrite (msubst_compose_is_id_r Hwf Hid Hinc1 Hinc).
        apply a_inc_equiv_refl; exact Hinc.
    + destruct (α1 == β) as [-> | Hα1β].
      * (* Flex-Flex-R : β̂ ≔ α̂; axiom, ζ := κ. *)
        inversion Hinc as [ | Θs κs Θt βs τ Hinc' Hwfτ Hmτ [Heqβ Heqκ] Heqt
                          | | | | ]; subst.
        assert (Hα1α' : α <> β) by exact Hne.
        assert (Hfα0 : a_flex_tvar Θ0' α)
          by (eapply (proj1 (a_flex_tvar_cons_other _ _ Hne)); exact Hfα).
        exists ((β ~ abind_flex_mono_def (ptyp_var_f α)) ++ Θ0'). split.
        { apply a_unify__flex_r; [ exact Hne | exact Hfα0 ]. }
        split; [ apply avoid_same_dom | ].
        intros κ1 Hid Hinc1. exists ((β, τ) :: κs). split.
        -- apply a_inc__flex_def; auto.
           rewrite msubst_lookup_cons_eq in Heq.
           rewrite (msubst_lookup_cons_neq τ κs Hα1α') in Heq.
           apply a_tyequiv__sym; exact Heq.
        -- rewrite (msubst_compose_is_id_r Hwf Hid Hinc1 Hinc).
           apply a_inc_equiv_refl; exact Hinc.
      * (* Flex-Flex-Skip : α1̂ ∉ {α̂, β̂} walked past. *)
        inversion Hinc as [ | Θs κs Θt α1s τα1 Hincs Hwfτ Hmτ [Heqγ Heqκ] Heqt
                          | | | | ]; subst.
        assert (Hαα1 : α <> α1) by auto.
        assert (Hβα1 : β <> α1) by auto.
        assert (Hfα0 : a_flex_tvar Θ0' α)
          by (eapply (proj1 (a_flex_tvar_cons_other _ _ Hαα1)); exact Hfα).
        assert (Hfβ0 : a_flex_tvar Θ0' β)
          by (eapply (proj1 (a_flex_tvar_cons_other _ _ Hβα1)); exact Hfβ).
        rewrite (msubst_lookup_cons_neq τα1 κs Hαα1) in Heq.
        rewrite (msubst_lookup_cons_neq τα1 κs Hβα1) in Heq.
        assert (Hlt : mu_lt (mu_unify Θ κs α β Θ0')
                            (mu_unify Θ ((α1, τα1) :: κs) α β
                                      ((α1 ~ abind_flex_mono) ++ Θ0'))).
        { unfold mu_unify. apply mu_lt_intro. right. split.
          - unfold V_unify, Vvar.
            rewrite (msubst_lookup_cons_neq τα1 κs Hαα1).
            rewrite (msubst_lookup_cons_neq τα1 κs Hβα1).
            reflexivity.
          - left. simpl. lia. }
        destruct (IH _ Hlt) as [_ [HuIH _]].
        destruct (HuIH (add α1 N) Θ0' α β κs Θ eq_refl Hwf0 Hfα0 Hfβ0
                       Hincs Hwfth Heq) as [Θ1' [Hu [Hnew Hopt']]].
        exists ((α1 ~ abind_flex_mono) ++ Θ1'). split.
        { apply a_unify__flex_skip;
            [ auto | auto | (* the popped head misses the sub-run's output: the
             relayed avoid set [add α1 N] says so *)
          eapply avoid_head_miss; [ exact Hnew | exact Hnd ] | exact Hu ]. }
        split; [ eapply avoid_relay_cons; exact Hnew | ].
        intros κ1 Hid Hinc1.
        inversion Hinc1 as [ | Θp κp Θq α1p τp Hincp Hwfp Hmp [Heqγ1 Heqκ1] Heqt1
                           | | | | ]; subst.
        apply is_id_msubst_inv in Hid as [Heqτp Hid']; subst τp.
        destruct (a_unify_sound Hu Hwf0)
          as [[[w [Hidw Hincw]] _] _].
        assert (Hw : κp = w)
          by (eapply is_id_inc_unique; eauto).
        subst w.
        assert (Hγw : α1 `notin` dom κp)
          by (pose proof (a_inc_dom_sub Hincw) as Hs; clear - Hs Hnd; fsetdec).
        destruct (Hopt' κp Hid' Hincw) as [ζ' [Hζ' Hie']].
        exists ((α1, τα1) :: ζ'). split.
        -- apply a_inc__flex; auto.
        -- assert (Heqc : msubst_compose ((α1, τα1) :: ζ') ((α1, ptyp_var_f α1) :: κp)
                         = (α1, τα1) :: msubst_compose ζ' κp).
           { change (msubst_compose ((α1, τα1) :: ζ') ((α1, ptyp_var_f α1) :: κp))
               with ((α1, msubst_ptyp ((α1, τα1) :: ζ') (ptyp_var_f α1))
                     :: msubst_compose ((α1, τα1) :: ζ') κp).
             rewrite (msubst_compose_cons_l_id τα1 ζ' Hid' Hγw).
             change (msubst_ptyp ((α1, τα1) :: ζ') (ptyp_var_f α1))
               with (msubst_lookup ((α1, τα1) :: ζ') α1).
             rewrite msubst_lookup_cons_eq. reflexivity. }
           rewrite Heqc.
           apply a_inc_equiv__flex; [ exact Hie' | ].
           apply a_tyequiv__refl; apply mono_ptyp_lc; exact Hmτ.
  - (* head [α1̂ ≔ τdef] : Flex-Flex-Assign, the back-edge into part 1. *)
    inversion Hwf as [ | | γh τh Θh Hnd Hwfτd Hmτd Hwf0 | | | ]; subst.
    inversion Hinc as [ | | Θs κs Θt α1s τd τα1 Hinc' Hwfτα1 Hmτα1 Heqd
                          [Heqγ Heqκ] Heqt | | | ]; subst.
    (* the substituted subjects and their facts, uniformly in the variable *)
    assert (Hgen : forall β1,
        a_flex_tvar ((α1 ~ abind_flex_mono_def τdef) ++ Θ0') β1 ->
        a_wf_ptyp Θ0' (subst_ptyp_in_ptyp τdef α1 (ptyp_var_f β1)) /\
        mono_ptyp (subst_ptyp_in_ptyp τdef α1 (ptyp_var_f β1)) /\
        {{ Θ ⊢ (msubst_ptyp κs (subst_ptyp_in_ptyp τdef α1 (ptyp_var_f β1)))
          ≡ᵗ (msubst_lookup ((α1, τα1) :: κs) β1) }}a).
    { intros β1 Hfδ. cbn [subst_ptyp_in_ptyp].
      destruct_if as [-> | Hβ1α1].
      - repeat split;
          [ exact Hwfτd | exact Hmτd
          | rewrite msubst_lookup_cons_eq;
            apply a_tyequiv__sym; exact Heqd ].
      - assert (Hfδ' : a_flex_tvar Θ0' β1)
          by (eapply (proj1 (a_flex_tvar_cons_other _ _ Hβ1α1)); exact Hfδ).
        repeat split.
        + apply a_wf_ptyp__var. right. exact Hfδ'.
        + apply mono_ptyp__var.
        + rewrite (msubst_lookup_cons_neq τα1 κs Hβ1α1).
          cbn [msubst_ptyp].
          apply a_tyequiv__refl. apply mono_ptyp_lc.
          eapply a_inc_lookup_mono; exact Hinc'. }
    destruct (Hgen α Hfα) as [HwfAσ [HmAσ HeqAκ]].
    destruct (Hgen β Hfβ) as [HwfBσ [HmBσ HeqBκ]].
    clear Hgen.
    set (Aσ := subst_ptyp_in_ptyp τdef α1 (ptyp_var_f α)) in *.
    set (Bσ := subst_ptyp_in_ptyp τdef α1 (ptyp_var_f β)) in *.
    (* the sub-node's solution facts *)
    assert (HmA' : mono_ptyp (msubst_ptyp κs Aσ))
      by (eapply mono_ptyp_msubst; [ exact Hinc' | exact HmAσ ]).
    assert (HmB' : mono_ptyp (msubst_ptyp κs Bσ))
      by (eapply mono_ptyp_msubst; [ exact Hinc' | exact HmBσ ]).
    assert (HwfA' : a_wf_ptyp Θ (msubst_ptyp κs Aσ))
      by (eapply a_wf_ptyp_msubst; [ exact HwfAσ | exact Hwf0 | exact Hinc' ]).
    assert (HwfB' : a_wf_ptyp Θ (msubst_ptyp κs Bσ))
      by (eapply a_wf_ptyp_msubst; [ exact HwfBσ | exact Hwf0 | exact Hinc' ]).
    assert (HeqAB : {{ Θ ⊢ (msubst_ptyp κs Aσ) ≡ᵗ (msubst_ptyp κs Bσ) }}a).
    { eapply a_tyequiv__trans; [ exact HeqAκ | ].
      eapply a_tyequiv__trans; [ exact Heq | ].
      apply a_tyequiv__sym; exact HeqBκ. }
    assert (Hjoin0 : {{ empty ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn (msubst_ptyp κs Aσ))
                       ∼ (ptyp_to_bskl_syn (msubst_ptyp κs Bσ)) }}ad).
    { apply tyequiv_mono_consis;
        [ exact HeqAB | exact Hwfth | exact HmA'
        | intros α0 Hα0; eapply a_wf_ptyp_ftv_tvarish;
            [ exact HwfA' | exact Hα0 ] ]. }
    assert (Hjoin' : {{ empty ⨟ Θ ⊢ˢ
              (pskl_to_uskl (msubst_pskl κs (ptyp_to_pskl Aσ)))
              ∼ (ptyp_to_bskl_syn (msubst_ptyp κs Bσ)) }}ad)
      by (rewrite msubst_pskl_embed_ptyp, pskl_to_uskl_ptyp; exact Hjoin0).
    assert (Hrs' : {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κs (ptyp_to_pskl Bσ))) ⊳ (ptyp_to_bskl_syn (msubst_ptyp κs Bσ)) }}ad).
    { rewrite msubst_pskl_embed_ptyp.
      replace (pskl_to_bskl_inh (ptyp_to_pskl (msubst_ptyp κs Bσ)))
        with (pskl_to_bskl_inh (uskl_to_pskl (ptyp_to_uskl_syn (msubst_ptyp κs Bσ))))
        by (rewrite uskl_to_pskl_ptyp; reflexivity).
      eapply ad_pat_consis_refine_syn_mono;
        [ apply consis_mono_refl;
            [ exact HmB'
            | intros α0 Hα0; eapply a_wf_ptyp_ftv_tvarish;
                [ exact HwfB' | exact Hα0 ] ]
        | exact Hwfth
        | apply mono_ptyp_to_bskl_syn; exact HmB'
        | clear; fsetdec
        | intros β0 τ0 Hb0; clear; fsetdec ]. }
    assert (Hrp' : {{ Θ ⨟ empty ⊢ᵣₚ (msubst_pskl κs (ptyp_to_pskl Aσ)) ⊳ (bskl_to_pskl (ptyp_to_bskl_syn (msubst_ptyp κs Bσ))) }}ad).
    { rewrite msubst_pskl_embed_ptyp.
      replace (ptyp_to_pskl (msubst_ptyp κs Aσ))
        with (uskl_to_pskl (ptyp_to_uskl_syn (msubst_ptyp κs Aσ)))
        by (apply uskl_to_pskl_ptyp).
      eapply ad_pat_consis_refine_pskl_mono;
        [ exact Hjoin0 | exact Hwfth
        | apply mono_ptyp_to_bskl_syn; exact HmB'
        | clear; fsetdec
        | intros β0 τ0 Hb0; clear; fsetdec ]. }
    assert (Hpsi : (empty : atoms) [=] empty) by fsetdec.
    assert (HwfPA : {{ Θ0' ⨟ empty ⊢ₚₛ (ptyp_to_pskl Aσ) }}a)
      by (apply a_wf_ptyp_to_wf_pskl; exact HwfAσ).
    assert (HwfPB : {{ Θ0' ⨟ empty ⊢ₚₛ (ptyp_to_pskl Bσ) }}a)
      by (apply a_wf_ptyp_to_wf_pskl; exact HwfBσ).
    (* the measure: V constant (the back-edge unfolds a definition the
       solution had already unfolded), n one smaller. *)
    assert (Hlt : mu_lt
        (mu_consis Θ κs (ptyp_to_pskl Bσ) (ptyp_to_pskl Aσ) Θ0')
        (mu_unify Θ ((α1, τα1) :: κs) α β
                  ((α1 ~ abind_flex_mono_def τdef) ++ Θ0'))).
    { unfold mu_consis, mu_unify. apply mu_lt_intro. right. split.
      - unfold V_consis, V_unify.
        rewrite (Vpskl_ptyp_to_pskl Θ κs Aσ).
        rewrite (Vpskl_ptyp_to_pskl Θ κs Bσ).
        unfold Aσ, Bσ.
        rewrite (@Vvar_backedge Θ κs α1 τdef τα1 α Hwfth Heqd).
        rewrite (@Vvar_backedge Θ κs α1 τdef τα1 β Hwfth Heqd).
        unfold Vvar, Vptyp; cbn [msubst_ptyp]; reflexivity.
      - left. simpl. lia. }
    destruct (IH _ Hlt) as [HcIH _].
    destruct (HcIH (add α1 N) empty empty Θ0' (ptyp_to_pskl Bσ)
                   (ptyp_to_pskl Aσ) κs Θ empty
                   (ptyp_to_bskl_syn (msubst_ptyp κs Bσ))
                   eq_refl Hwf0 HwfPB HwfPA
                   ltac:(intros α0 Hα0; exfalso; clear - Hα0; solve_notin_auto)
                   ltac:(repeat intro; solve_notin_auto)
                   ltac:(repeat intro; solve_notin_auto)
                   Hinc' Hwfth
                   ltac:(repeat intro; solve_notin_auto)
                   Hpsi Hjoin' Hrs' Hrp'
                   ltac:(unfold ptyp_to_bskl_syn;
                         rewrite bskl_to_pskl_pskl_to_bskl_syn;
                         apply a_wf_ptyp_to_wf_pskl; exact HwfB'))
      as [P1 [Θ1' [Hcons [Hnew Hopt']]]].
    exists ((α1 ~ abind_flex_mono_def τdef) ++ Θ1'). split.
    { eapply a_unify__flex_assign;
        [ exact Hfα | exact Hfβ | | exact Hcons ].
      (* the walked definition is in the relayed avoid set [add α1 N] and
         fresh for the input, so it misses the output *)
      eapply avoid_head_miss; [ exact Hnew | exact Hnd ]. }
    split; [ eapply avoid_relay_cons; exact Hnew | ].
    intros κ1 Hid Hinc1.
    inversion Hinc1 as [ | | Θp κp Θq α1p τd1 τ1 Hincp Hwf1p Hm1p Heq1p
                           [Heqγ1 Heqκ1] Heqt1 | | | ]; subst.
    apply is_id_msubst_inv in Hid as [Heqτ1 Hid']; subst τ1.
    (* the sub-derivation's own soundness: id-witness + target wf *)
    destruct (proj2 (proj2 a_assign_unify_consis_sound) _ _ _ _ _ _ _ Hcons
                Hwf0 HwfPB HwfPA
                ltac:(intros α0 Hα0; exfalso; clear - Hα0; solve_notin_auto)
                ltac:(repeat intro; solve_notin_auto)
                ltac:(repeat intro; solve_notin_auto))
      as [[[w [Hidw Hincw]] _] [Hwf1' _]].
    assert (Hw : κp = w) by (eapply is_id_inc_unique; eauto).
    subst w.
    assert (Hγw : α1 `notin` dom κp)
      by (pose proof (a_inc_dom_sub Hincw) as Hs; clear - Hs Hnd; fsetdec).
    destruct (Hopt' κp Hid' Hincw) as [ζ' [Hζ' [Hie' _]]].
    exists ((α1, τα1) :: ζ'). split.
    + apply a_inc__flex_def; [ exact Hζ' | exact Hwfτα1 | exact Hmτα1 | ].
      (* the definition's image transports across the equivalent increments *)
      eapply a_tyequiv__trans; [ exact Heqd | ].
      rewrite <- (msubst_compose_id_ptyp Hwf0 Hwf1' Hid' Hincw Hζ' Hwfτd).
      eapply a_inc_equiv_msubst_ptyp;
        [ exact Hwfτd | exact Hie' | exact Hwf0
        | eapply a_inc_msubst_lc; exact Hinc'
        | eapply msubst_lc_compose;
            [ eapply a_inc_msubst_lc; exact Hζ'
            | eapply is_id_msubst_values_lc; exact Hidw ] ].
    + assert (Heqc : msubst_compose ((α1, τα1) :: ζ') ((α1, ptyp_var_f α1) :: κp)
                     = (α1, τα1) :: msubst_compose ζ' κp).
      { change (msubst_compose ((α1, τα1) :: ζ') ((α1, ptyp_var_f α1) :: κp))
          with ((α1, msubst_ptyp ((α1, τα1) :: ζ') (ptyp_var_f α1))
                :: msubst_compose ((α1, τα1) :: ζ') κp).
        rewrite (msubst_compose_cons_l_id τα1 ζ' Hid' Hγw).
        change (msubst_ptyp ((α1, τα1) :: ζ') (ptyp_var_f α1))
          with (msubst_lookup ((α1, τα1) :: ζ') α1).
        rewrite msubst_lookup_cons_eq. reflexivity. }
      rewrite Heqc.
      apply a_inc_equiv__flex_def;
        [ exact Hie'
        | apply a_tyequiv__refl; apply mono_ptyp_lc; exact Hmτα1
        | exact Heqd ].
Qed.
