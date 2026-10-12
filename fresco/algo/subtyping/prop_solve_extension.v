Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.
Require Import src.fresco.notations.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.decl.prop_skeleton.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo_decl.def_subtyping.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo.basic.prop_context_normalization.
Require Import src.fresco.algo_decl.prop_stability.
Require Import src.fresco.algo_decl.prop_refinement.
Require Import src.fresco.algo.consistency.prop_soundness_consis.
Require Import src.fresco.algo.consistency.prop_completeness_consis.
Require Import src.fresco.algo.consistency.prop_consis_monotype_equiv.
Require Import src.fresco.algo_decl.prop_precision.
Require Import src.fresco.algo_decl.prop_subtyping.
Require Import src.fresco.algo.consistency.prop_consis_precise.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo.subtyping.prop_looksub.
Require Import src.fresco.algo.subtyping.prop_solve_sub.
Require Import src.fresco.algo.subtyping.prop_completeness_sub_precise.
Require Import src.fresco.algo.basic.prop_metasubst.
Require Import src.fresco.algo.basic.prop_metasubst_composition.
Require Import src.fresco.algo.subtyping.prop_rigid_substitution.

Set Implicit Arguments.

Definition solve_scope (Θ0 Θ Θw : aenv) (κ : metasubst) : Prop :=
  (forall x b, binds x b Θw -> binds x b Θ) /\
  (forall x b, binds x b Θ -> binds x b Θw \/ b = abind_tvar) /\
  (forall α, a_flex_tvar Θ0 α ->
     ftvar_in_ptyp (msubst_lookup κ α) [<=] dom Θw).

Lemma solve_scope_open_tvar : forall Θ0 Θ Θw κ β,
  solve_scope Θ0 Θ Θw κ -> β `notin` dom Θ ->
  β `notin` dom Θw /\
  solve_scope ((β ~ abind_tvar) ++ Θ0) ((β ~ abind_tvar) ++ Θ) Θw κ.
Proof.
  intros * (Hmon & Hnr & Hκw) Hβ.
  split.
  - intro Hin. apply binds_In_inv in Hin; destruct Hin as [b Hb].
    apply Hβ. eapply binds_In; apply Hmon; exact Hb.
  - unfold solve_scope. repeat split.
    + intros x b Hb; apply binds_app_3; apply Hmon; exact Hb.
    + intros x b Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heq] | Hb'];
        [ right; exact Heq | exact (Hnr _ _ Hb') ].
    + intros α Hf; apply Hκw; eapply a_flex_tvar_strip_tvar; exact Hf.
Qed.

Lemma solve_scope_flex_prefix : forall Θ0 Θ Θw κ Ξ κa,
  solve_scope Θ0 Θ Θw κ ->
  keys κa = keys Ξ ->
  (forall p, In p κa -> ftvar_in_ptyp (snd p) [<=] dom Θw) ->
  solve_scope (Ξ ++ Θ0) Θ Θw (κa ++ κ).
Proof.
  intros * (Hmon & Hnr & Hκw) Hkeys Himg.
  split; [ exact Hmon | ]. split; [ exact Hnr | ].
  intros α Hf.
  destruct (AtomSetProperties.In_dec α (dom κa)) as [Hin | Hnin].
  - rewrite (@msubst_lookup_app_in κa κ α Hin).
    destruct (msubst_lookup_in_or κa α) as [Hp | [Hni _]];
      [ exact (Himg _ Hp) | exfalso; clear - Hin Hni; fsetdec ].
  - rewrite (@msubst_lookup_app_notin κa κ α Hnin). apply Hκw.
    pose proof (@keys_eq_dom _ _ κa Ξ Hkeys) as Hd.
    eapply (proj1 (@a_flex_tvar_app_notin Ξ Θ0 α ltac:(clear - Hd Hnin; fsetdec))).
    exact Hf.
Qed.
Arguments solve_scope_flex_prefix [Θ0 Θ Θw κ Ξ κa] _ _ _.

Lemma solve_context_open_tvar : forall Θ0 Θ κ α β P0 Pi,
  {{ ⊢ Θ }}a -> {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a -> {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a ->
  κ ∷ Θ0 ⊑ Θ ->
  α `notin` dom Θ -> α `notin` dom Θ0 ->
  β <> α -> β `notin` dom Θ -> β `notin` dom Θ0 ->
  (forall (x : atom) (b : abind),
     binds x b Θ0 -> binds x b ((β ~ abind_tvar) ++ Θ0))
  /\ (forall (x : atom) (b : abind),
        binds x b Θ -> binds x b ((β ~ abind_tvar) ++ Θ))
  /\ {{ ⊢ ((β ~ abind_tvar) ++ Θ) }}a
  /\ {{ ⊢ ((β ~ abind_tvar) ++ Θ0) }}a
  /\ α `notin` dom ((β ~ abind_tvar) ++ Θ)
  /\ α `notin` dom ((β ~ abind_tvar) ++ Θ0)
  /\ κ ∷ ((β ~ abind_tvar) ++ Θ0) ⊑ ((β ~ abind_tvar) ++ Θ)
  /\ {{ ((β ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a
  /\ {{ ((β ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ Pi }}a.
Proof.
  intros Θ0 Θ κ α β P0 Pi HwfΘ HwfΘ0 HwfP0 HwfPi Hκ HαΘ HαΘ0 Hβα HβΘ HβΘ0.
  assert (Hweak0 : forall (x : atom) (b : abind),
            binds x b Θ0 -> binds x b ((β ~ abind_tvar) ++ Θ0))
    by (intros x b Hb; apply binds_app_3; exact Hb).
  assert (Hweak : forall (x : atom) (b : abind),
            binds x b Θ -> binds x b ((β ~ abind_tvar) ++ Θ))
    by (intros x b Hb; apply binds_app_3; exact Hb).
  repeat split; try assumption.
  - apply a_wf_aenv__tvar; assumption.
  - apply a_wf_aenv__tvar; assumption.
  - simpl; clear - HαΘ Hβα; fsetdec.
  - simpl; clear - HαΘ0 Hβα; fsetdec.
  - apply a_inc_cons_tvar; exact Hκ.
  - eapply a_wf_pskl_weaken; eassumption.
  - eapply a_wf_pskl_weaken; eassumption.
Qed.

Lemma a_inc_flex_prefix_split : forall Ξ κa Θ0 κb Θ,
  all_flex_mono Ξ ->
  keys κa = keys Ξ ->
  (κa ++ κb) ∷ (Ξ ++ Θ0) ⊑ Θ ->
  Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κa /\ κb ∷ Θ0 ⊑ Θ.
Proof.
  induction Ξ as [ | [x b] Ξ' IH ]; intros κa Θ0 κb Θ Hfm Hmap Hinc.
  - destruct κa as [ | ? ? ]; simpl in Hmap; [ | discriminate ].
    simpl in Hinc. split; [ constructor | exact Hinc ].
  - inversion Hfm as [ | ph pt Hb Hfm' ]; subst; simpl in Hb; subst b.
    destruct κa as [ | [y τ] κa' ]; simpl in Hmap; [ discriminate | ].
    injection Hmap as Hxy Hmap'; subst y.
    simpl in Hinc.
    inversion Hinc as [ | Θ2 κ2 Θ3 x2 τ2 Hinc2 Hwf2 Hmono2 | | | | ]; subst.
    destruct (IH κa' Θ0 κb Θ Hfm' Hmap' Hinc2) as [Hfa Hrest].
    split; [ constructor; [ split; assumption | exact Hfa ] | exact Hrest ].
Qed.

Lemma a_inc_flex_prefix_build : forall Ξ κa Θ0 κb Θ,
  all_flex_mono Ξ ->
  keys κa = keys Ξ ->
  Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κa ->
  κb ∷ Θ0 ⊑ Θ ->
  (κa ++ κb) ∷ (Ξ ++ Θ0) ⊑ Θ.
Proof.
  induction Ξ as [ | [x b] Ξ' IH ]; intros κa Θ0 κb Θ Hfm Hmap Hwm Hinc.
  - destruct κa as [ | ? ? ]; simpl in Hmap; [ | discriminate ].
    simpl. exact Hinc.
  - inversion Hfm as [ | ph pt Hb Hfm' ]; subst; simpl in Hb; subst b.
    destruct κa as [ | [y τ] κa' ]; simpl in Hmap; [ discriminate | ].
    injection Hmap as Hxy Hmap'; subst y.
    inversion Hwm as [ | ph2 pt2 Hwmh Hwm' ]; subst; destruct Hwmh as [Hwfτ Hmτ].
    simpl. apply a_inc__flex; [ apply IH; assumption | exact Hwfτ | exact Hmτ ].
Qed.

Lemma all_flex_mono_decls : forall Ξ, all_flex_mono Ξ -> a_decls Ξ.
Proof.
  intros Ξ H; induction H as [ | [α b] Ξ' Hb Hall IH ]; [ constructor | ].
  simpl in Hb; subst b. apply (a_decls__cons α). exact IH.
Qed.

Lemma all_flex_mono_ftvar_in_aenv : forall Ξ,
  all_flex_mono Ξ -> ftvar_in_aenv Ξ [<=] dom Ξ.
Proof.
  intros Ξ H; induction H as [ | [α b] Ξ' Hb Hall IH ]; simpl in *.
  - fsetdec.
  - subst b. simpl. clear - IH; fsetdec.
Qed.

Lemma a_wf_aenv_prepend_flex_block : forall Ξ Θ,
  all_flex_mono Ξ ->
  uniq Ξ ->
  (forall α, α `in` dom Ξ -> α `notin` dom Θ) ->
  {{ ⊢ Θ }}a ->
  {{ ⊢ (Ξ ++ Θ) }}a.
Proof.
  intros Ξ; induction Ξ as [ | [α b] Ξ' IH ]; intros Θ Hfm Hu Hfr Hwf;
    [ exact Hwf | ].
  pose proof (Forall_inv Hfm) as Hb; simpl in Hb; subst b.
  pose proof (Forall_inv_tail Hfm) as Hfm'.
  assert (HαΘ : α `notin` dom Θ) by (apply Hfr; simpl; fsetdec).
  assert (HαΞ : α `notin` dom Ξ') by (clear - Hu; solve_uniq).
  simpl_env. apply a_wf_aenv__flex.
  - rewrite dom_app. clear - HαΘ HαΞ; fsetdec.
  - apply IH; [ exact Hfm' | clear - Hu; solve_uniq | | exact Hwf ].
    intros α0 Hα0. apply Hfr. simpl. clear - Hα0; fsetdec.
Qed.

Lemma close_pskl_subst_var : forall P α β,
  β `notin` ftvar_in_pskl P ->
  close_pskl_wrt_pskl β (subst_pskl_in_pskl (pskl_var_f β) α P)
  = close_pskl_wrt_pskl α P.
Proof.
  intros P α β Hβ.
  rewrite subst_pskl_in_pskl_spec.
  apply close_pskl_wrt_pskl_open_pskl_wrt_pskl.
  assert (Hcl : ftvar_in_pskl (close_pskl_wrt_pskl α P)
                  [=] AtomSetImpl.remove α (ftvar_in_pskl P))
    by (apply ftvar_in_pskl_close_pskl_wrt_pskl).
  clear - Hβ Hcl. fsetdec.
Qed.

Lemma a_guess_mono_ctx_change_size : forall n Θ Θ' P Ξ A,
  size_pskl P <= n ->
  a_guess_mono Θ P Ξ A ->
  (forall α, α `in` dom Ξ -> α `notin` ftvar_in_aenv Θ') ->
  a_guess_mono Θ' P Ξ A.
Proof.
  induction n as [ | n IH ]; intros Θ Θ' P Ξ A Hsz H Hfr;
    [ exfalso; pose proof (size_pskl_min P); lia | ].
  destruct H as [ Θ0 α Hα | Θ0 Pb Ξb Ab Hg | Θ0 α | Θ0
                | Θ0 Pa Pb Ξa Ξb Aa Ab Hga Hgb
                | Θ0 Pb Ξb Ab b0 Hfrb Hg ]; cbn in Hsz.
  -
    apply a_guess_mono__ghost. apply Hfr. simpl; clear; fsetdec.
  -  apply a_guess_mono__univ_ghost.
    eapply IH; [ lia | exact Hg | exact Hfr ].
  -  apply a_guess_mono__var.
  -  apply a_guess_mono__unit.
  -
    apply a_guess_mono__arrow.
    + eapply IH; [ lia | exact Hga | ].
      intros α Hα; apply Hfr; rewrite dom_app; clear - Hα; fsetdec.
    + eapply IH; [ lia | exact Hgb | ].
      intros α Hα; apply Hfr; rewrite dom_app; clear - Hα; fsetdec.
  -
    destruct (atom_fresh (ftvar_in_aenv Θ' `union` ftvar_in_pskl Pb
                `union` dom Ξb `union` ftvar_in_ptyp Ab
                `union` singleton b0)) as [δ Hδ].
    assert (Hb0Ξ : b0 `notin` dom Ξb)
      by (eapply a_guess_mono_generated_fresh_binder; exact Hg).
    assert (HΞftv : ftvar_in_aenv Ξb [<=] dom Ξb)
      by (eapply a_guess_mono_generated_ftvar; exact Hg).
    pose proof (@a_guess_mono_swap b0 δ _ _ _ _ Hg) as Hsw.
    rewrite swap_aenv_app, swap_aenv_one_tvar in Hsw.
    rewrite swap_pskl_open_var, swap_atom_l in Hsw.
    rewrite (swap_pskl_fresh_id b0 δ Pb) in Hsw
      by (clear - Hfrb Hδ; fsetdec).
    rewrite (swap_aenv_fresh_id b0 δ Ξb) in Hsw
      by (clear - Hb0Ξ Hδ HΞftv; fsetdec).
    rewrite (@swap_ptyp_as_subst b0 δ Ab) in Hsw
      by (clear - Hδ; fsetdec).
    assert (Hgδ : a_guess_mono ((δ ~ abind_tvar) ++ Θ')
                    (open_pskl_wrt_pskl Pb (pskl_var_f δ)) Ξb
                    (subst_ptyp_in_ptyp (ptyp_var_f δ) b0 Ab)).
    { eapply IH;
        [ rewrite size_pskl_open_pskl_wrt_pskl_var; lia
        | exact Hsw
        | intros α Hα; specialize (Hfr α Hα); simpl;
          assert (Hne : α `notin` singleton δ) by (clear - Hα Hδ; fsetdec);
          clear - Hfr Hne; fsetdec ]. }
    rewrite <- (@close_ptyp_subst_var Ab b0 δ ltac:(clear - Hδ; solve_notin_auto)).
    apply a_guess_mono__forall with (β := δ);
      [ clear - Hδ; fsetdec | exact Hgδ ].
Qed.

Lemma a_guess_mono_ctx_change : forall Θ Θ' P Ξ A,
  a_guess_mono Θ P Ξ A ->
  (forall α, α `in` dom Ξ -> α `notin` ftvar_in_aenv Θ') ->
  a_guess_mono Θ' P Ξ A.
Proof.
  intros Θ Θ' P Ξ A H Hfr.
  eapply a_guess_mono_ctx_change_size; [ reflexivity | exact H | exact Hfr ].
Qed.

Lemma binds_strengthen_mid : forall (x : atom) (b : abind) Ξl Ξm Θ0,
  binds x b (Ξl ++ Ξm ++ Θ0) -> x `notin` dom Ξm -> binds x b (Ξl ++ Θ0).
Proof.
  intros x b Ξl Ξm Θ0 H Hx. apply binds_app_1 in H as [H | H].
  - apply binds_app_2; exact H.
  - apply binds_app_1 in H as [H | H].
    + exfalso. apply Hx. eapply binds_In; exact H.
    + apply binds_app_3; exact H.
Qed.

Lemma a_non_flex_weaken_mid : forall Ξl Ξm Θ0 P,
  (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P) ->
  a_non_flex (Ξl ++ Θ0) P -> a_non_flex (Ξl ++ Ξm ++ Θ0) P.
Proof.
  intros Ξl Ξm Θ0 P Hftv [Hlc Hnf]. split; [ exact Hlc | ].
  intro Hf. apply Hnf. inversion Hf as [ Θx αx Hb | Θx αx τ Hb ]; subst.
  - assert (Hin : αx `notin` dom Ξm)
      by (intro Hc; apply (Hftv _ Hc); simpl; fsetdec).
    apply a_flex__var with (α := αx).
    eapply binds_strengthen_mid; eassumption.
  - assert (Hin : αx `notin` dom Ξm)
      by (intro Hc; apply (Hftv _ Hc); simpl; fsetdec).
    apply a_flex__var_def with (α := αx) (τ := τ).
    eapply binds_strengthen_mid; eassumption.
Qed.

Lemma ftvar_in_aenv_weaken_mid : forall Ξl Ξm Θ0,
  all_flex_mono Ξm ->
  ftvar_in_aenv (Ξl ++ Ξm ++ Θ0)
    [<=] ftvar_in_aenv (Ξl ++ Θ0) `union` dom Ξm.
Proof.
  intros Ξl Ξm Θ0 Hfm.
  rewrite ! ftvar_in_aenv_app.
  pose proof (all_flex_mono_ftvar_in_aenv Hfm) as Hm.
  clear - Hm; fsetdec.
Qed.

Lemma a_solve_sub_eq_weaken_mid_flex_size : forall n,
  (forall Θ m P P0 Ξ P',
     2 * (size_pskl P + size_pskl P0) + 1 <= n ->
     {{ Θ ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' }}a ->
     forall Ξl Ξm Θ0, Θ = Ξl ++ Θ0 -> all_flex_mono Ξm ->
     (forall x, x `in` dom Ξm -> x `notin` dom (Ξl ++ Θ0)) ->
     (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P) ->
     (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P') ->
     (forall x, x `in` dom Ξm -> x `notin` dom Ξ) ->
     {{ (Ξl ++ Ξm ++ Θ0) ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' }}a) /\
  (forall Θ P P0 Ξ P',
     2 * (size_pskl P + size_pskl P0) <= n ->
     {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a ->
     forall Ξl Ξm Θ0, Θ = Ξl ++ Θ0 -> all_flex_mono Ξm ->
     (forall x, x `in` dom Ξm -> x `notin` dom (Ξl ++ Θ0)) ->
     (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P) ->
     (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P') ->
     (forall x, x `in` dom Ξm -> x `notin` dom Ξ) ->
     {{ (Ξl ++ Ξm ++ Θ0) ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a).
Proof.
  induction n as [| n IHall];
    [ split; intros * Hsz Hd; inversion Hd; subst; cbn in Hsz; lia | ].
  destruct IHall as [IHs IHe].
  split.

  { intros Θ m P P0 Ξ P' Hsz Hd.
    destruct Hd as
      [ Θ m α Q
      | Θ m P Q Ξ P' b Hfr Hp
      | Θ m P Q Ξ P' Hp
      | Θ m P Hoff
      | Θ P Q Ξ P' Hgf0 Hg1 Hg2 Hp
      | Θ A B Ξ P' b Hgf0 Hoff Hfr Hp
      | Θ m P1 P2 Q1 Q2 Ξ1 Ξ2 P1' P2' Hp1 Hp2
      | Θ m Q1 Q2 Ξ1 Ξ2 P1' P2' Hp1 Hp2
      | Θ B Hgf0 Hg ];
      intros Ξl Ξm Θ0 Heq Hfm Hdisj Hftv Hout Hblk; subst; cbn in Hsz.
    -  apply a_solve_sub__var.
    -
      assert (HbΞ : b `notin` dom Ξ)
        by (eapply a_solve_sub_generated_apart_binder; exact Hp).
      assert (HΞf : ftvar_in_aenv Ξ [<=] dom Ξ)
        by (eapply (proj1 a_solve_sub_eq_generated_ftvar); exact Hp).
      pick fresh δ for
        (ftvar_in_aenv (Ξl ++ Θ0) `union` dom Ξm `union` dom Ξ
           `union` ftvar_in_pskl P `union` ftvar_in_pskl Q
           `union` ftvar_in_pskl P' `union` singleton b).
      pose proof (@a_solve_sub_move_binder_l _ _ _ _ _ _ _ δ Hp
                    ltac:(clear - Hfr; solve_notin_auto)
                    ltac:(clear - Fr; solve_notin_auto)) as Hr.
      rewrite (swap_aenv_fresh_id b δ (Ξl ++ Θ0)) in Hr
        by (clear - Hfr Fr; fsetdec).
      rewrite (swap_aenv_fresh_id b δ Ξ) in Hr
        by (clear - HbΞ Fr HΞf; fsetdec).
      rewrite <- (@close_pskl_subst_var P' b δ ltac:(clear - Fr; solve_notin_auto)).
      apply a_solve_sub__forall_l with (β := δ);
        [ rewrite ftvar_in_aenv_weaken_mid by exact Hfm;
          clear - Fr; fsetdec | ].
      eapply IHs with (Ξl := ((δ ~ abind_tvar) ++ Ξl)) (Ξm := Ξm) (Θ0 := Θ0);
        [ rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia
        | exact Hr | reflexivity | exact Hfm
        | intros x Hx; specialize (Hdisj x Hx);
          assert (Hxδ : x `notin` singleton δ)
            by (clear - Fr Hx; fsetdec);
          simpl_env in Hdisj; simpl_env;
          clear - Hdisj Hxδ; fsetdec
        | intros x Hx; specialize (Hftv x Hx);
          pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f δ))
            as Hup2;
          assert (Hxδ : x `notin` singleton δ) by (clear - Fr Hx; fsetdec);
          cbn in Hftv, Hup2; clear - Hftv Hup2 Hxδ; fsetdec
        | intros x Hx; specialize (Hout x Hx);
          pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                        P' (pskl_var_f δ) b) as Hsu;
          pose proof (ftvar_in_pskl_close_pskl_wrt_pskl P' b) as Hcl;
          assert (Hxδ : x `notin` singleton δ) by (clear - Fr Hx; fsetdec);
          cbn in Hout, Hsu; clear - Hout Hsu Hcl Hxδ; fsetdec
        | exact Hblk ].
    -
      apply a_solve_sub__univ_ghost_l.
      eapply IHs with (Ξl := Ξl) (Ξm := Ξm) (Θ0 := Θ0);
        [ cbn; lia | exact Hp | reflexivity | exact Hfm | exact Hdisj
        | intros x Hx; specialize (Hftv x Hx); cbn in Hftv; exact Hftv
        | intros x Hx; specialize (Hout x Hx); cbn in Hout; exact Hout
        | exact Hblk ].
    -  apply a_solve_sub__vacuous; exact Hoff.
    -
      apply a_solve_sub__check; [ exact Hgf0 | exact Hg1 | exact Hg2 | ].
      eapply IHe with (Ξl := Ξl) (Ξm := Ξm) (Θ0 := Θ0);
        [ cbn; lia | exact Hp | reflexivity | exact Hfm | exact Hdisj
        | exact Hftv | exact Hout | exact Hblk ].
    -
      assert (HbΞ : b `notin` dom Ξ)
        by (eapply a_solve_sub_generated_apart_binder; exact Hp).
      assert (HΞf : ftvar_in_aenv Ξ [<=] dom Ξ)
        by (eapply (proj1 a_solve_sub_eq_generated_ftvar); exact Hp).
      destruct (AtomSetProperties.In_dec b (dom Ξm)) as [Hin | Hnin].
      + pose proof (Hout b Hin) as HbP'.
        pick fresh δ for
          (ftvar_in_aenv (Ξl ++ Θ0) `union` dom Ξm `union` dom Ξ
             `union` ftvar_in_pskl A `union` ftvar_in_pskl B
             `union` ftvar_in_pskl P' `union` singleton b).
        pose proof (@a_solve_sub_move_binder_r _ _ _ _ _ _ δ Hp
                      ltac:(clear - Hfr; solve_notin_auto)
                      ltac:(clear - Fr; solve_notin_auto)) as Hr.
        rewrite (swap_aenv_fresh_id b δ (Ξl ++ Θ0)) in Hr
          by (clear - Hfr Fr; fsetdec).
        rewrite (swap_aenv_fresh_id b δ Ξ) in Hr
          by (clear - HbΞ Fr HΞf; fsetdec).
        rewrite (subst_pskl_in_pskl_fresh_eq P') in Hr
          by (clear - HbP'; fsetdec).
        apply a_solve_sub__forall_r with (β := δ);
          [ exact Hgf0 | exact Hoff
          | rewrite ftvar_in_aenv_weaken_mid by exact Hfm;
            clear - Fr; fsetdec | ].
        eapply IHs with (Ξl := ((δ ~ abind_tvar) ++ Ξl)) (Ξm := Ξm) (Θ0 := Θ0);
          [ rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia
          | exact Hr | reflexivity | exact Hfm
          | intros x Hx; specialize (Hdisj x Hx);
            assert (Hxδ : x `notin` singleton δ) by (clear - Fr Hx; fsetdec);
            simpl_env in Hdisj; simpl_env;
            clear - Hdisj Hxδ; fsetdec
          | intros x Hx; specialize (Hftv x Hx); cbn in Hftv; exact Hftv
          | exact Hout | exact Hblk ].
      + apply a_solve_sub__forall_r with (β := b);
          [ exact Hgf0 | exact Hoff
          | rewrite ftvar_in_aenv_weaken_mid by exact Hfm;
            clear - Hfr Hnin; fsetdec | ].
        eapply IHs with (Ξl := ((b ~ abind_tvar) ++ Ξl)) (Ξm := Ξm) (Θ0 := Θ0);
          [ rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia
          | exact Hp | reflexivity | exact Hfm
          | intros x Hx; specialize (Hdisj x Hx);
            assert (Hxb : x `notin` singleton b)
              by (clear - Hnin Hx; fsetdec);
            simpl_env in Hdisj; simpl_env;
            clear - Hdisj Hxb; fsetdec
          | intros x Hx; specialize (Hftv x Hx); cbn in Hftv; exact Hftv
          | exact Hout | exact Hblk ].
    -
      apply a_solve_sub__arrow with (Ξ1 := Ξ1).
      + eapply IHe with (Ξl := Ξl) (Ξm := Ξm) (Θ0 := Θ0);
          [ cbn; lia | exact Hp1 | reflexivity | exact Hfm | exact Hdisj
          | intros x Hx; specialize (Hftv x Hx); cbn in Hftv;
            clear - Hftv; fsetdec
          | intros x Hx; specialize (Hout x Hx); cbn in Hout;
            clear - Hout; fsetdec
          | intros x Hx; specialize (Hblk x Hx); rewrite dom_app in Hblk;
            clear - Hblk; fsetdec ].
      + rewrite <- (list_app_assoc Ξ1 Ξl (Ξm ++ Θ0)).
        eapply IHs with (Ξl := (Ξ1 ++ Ξl)) (Ξm := Ξm) (Θ0 := Θ0);
          [ cbn; lia | exact Hp2 | rewrite list_app_assoc; reflexivity | exact Hfm
          | intros x Hx; specialize (Hdisj x Hx); specialize (Hblk x Hx);
            rewrite dom_app in Hblk; rewrite ! dom_app;
            clear - Hdisj Hblk; rewrite dom_app in Hdisj; fsetdec
          | intros x Hx; specialize (Hftv x Hx); cbn in Hftv;
            clear - Hftv; fsetdec
          | intros x Hx; specialize (Hout x Hx); cbn in Hout;
            clear - Hout; fsetdec
          | intros x Hx; specialize (Hblk x Hx); rewrite dom_app in Hblk;
            clear - Hblk; fsetdec ].
    -
      apply a_solve_sub__ghost_l_fn with (Ξ1 := Ξ1).
      + eapply IHe with (Ξl := Ξl) (Ξm := Ξm) (Θ0 := Θ0);
          [ cbn; lia | exact Hp1 | reflexivity | exact Hfm | exact Hdisj
          | intros x Hx; cbn; clear; fsetdec
          | intros x Hx; specialize (Hout x Hx); cbn in Hout;
            clear - Hout; fsetdec
          | intros x Hx; specialize (Hblk x Hx); rewrite dom_app in Hblk;
            clear - Hblk; fsetdec ].
      + rewrite <- (list_app_assoc Ξ1 Ξl (Ξm ++ Θ0)).
        eapply IHs with (Ξl := (Ξ1 ++ Ξl)) (Ξm := Ξm) (Θ0 := Θ0);
          [ cbn; lia | exact Hp2 | rewrite list_app_assoc; reflexivity | exact Hfm
          | intros x Hx; specialize (Hdisj x Hx); specialize (Hblk x Hx);
            rewrite dom_app in Hblk; rewrite ! dom_app;
            clear - Hdisj Hblk; rewrite dom_app in Hdisj; fsetdec
          | intros x Hx; cbn; clear; fsetdec
          | intros x Hx; specialize (Hout x Hx); cbn in Hout;
            clear - Hout; fsetdec
          | intros x Hx; specialize (Hblk x Hx); rewrite dom_app in Hblk;
            clear - Hblk; fsetdec ].
    -  apply a_solve_sub__ghost_l; eassumption. }

  { intros Θ P P0 Ξ P' Hsz Hd.
    destruct Hd as
      [ Θ
      | Θ α Q
      | Θ α P Ξ A Hflex Hnf Hng Hgu
      | Θ Q
      | Θ P
      | Θ P1 P2 Q1 Q2 Ξ1 Ξ2 P1' P2' Hp1 Hp2
      | Θ P Q Ξ P' b Hfr Hp
      | Θ P Q Ξ P' Hp
      | Θ P Q Ξ P' b Hfr Hp
      | Θ P Q Ξ P' Hg Hp
      | Θ P Q Ξ P' b Hfr Hp
      | Θ P Q Ξ P' Hg Hp ];
      intros Ξl Ξm Θ0 Heq Hfm Hdisj Hftv Hout Hblk; subst; cbn in Hsz.
    -  apply a_solve_eq__unit.
    -  apply a_solve_eq__var.
    -
      apply a_solve_eq__flex_r;
        [ apply a_flex_tvar_weaken_mid; exact Hflex
        | apply a_non_flex_weaken_mid; eassumption
        | exact Hng
        | eapply a_guess_mono_ctx_change; [ exact Hgu | ] ].
      intros α0 Hα0.
      pose proof (a_guess_mono_generated_fresh Hgu Hα0) as Hf0.
      rewrite ftvar_in_aenv_weaken_mid by exact Hfm.
      assert (Hne : α0 `notin` dom Ξm)
        by (intro Hc; exact (Hblk α0 Hc Hα0)).
      clear - Hf0 Hne; fsetdec.
    -  apply a_solve_eq__ghost_l.
    -  apply a_solve_eq__ghost_r.
    -
      apply a_solve_eq__arrow with (Ξ1 := Ξ1).
      + eapply IHe with (Ξl := Ξl) (Ξm := Ξm) (Θ0 := Θ0);
          [ cbn; lia | exact Hp1 | reflexivity | exact Hfm | exact Hdisj
          | intros x Hx; specialize (Hftv x Hx); cbn in Hftv;
            clear - Hftv; fsetdec
          | intros x Hx; specialize (Hout x Hx); cbn in Hout;
            clear - Hout; fsetdec
          | intros x Hx; specialize (Hblk x Hx); rewrite dom_app in Hblk;
            clear - Hblk; fsetdec ].
      + rewrite <- (list_app_assoc Ξ1 Ξl (Ξm ++ Θ0)).
        eapply IHe with (Ξl := (Ξ1 ++ Ξl)) (Ξm := Ξm) (Θ0 := Θ0);
          [ cbn; lia | exact Hp2 | rewrite list_app_assoc; reflexivity | exact Hfm
          | intros x Hx; specialize (Hdisj x Hx); specialize (Hblk x Hx);
            rewrite dom_app in Hblk; rewrite ! dom_app;
            clear - Hdisj Hblk; rewrite dom_app in Hdisj; fsetdec
          | intros x Hx; specialize (Hftv x Hx); cbn in Hftv;
            clear - Hftv; fsetdec
          | intros x Hx; specialize (Hout x Hx); cbn in Hout;
            clear - Hout; fsetdec
          | intros x Hx; specialize (Hblk x Hx); rewrite dom_app in Hblk;
            clear - Hblk; fsetdec ].
    -
      assert (HbΞ : b `notin` dom Ξ)
        by (eapply a_solve_eq_generated_apart_binder; exact Hp).
      assert (HΞf : ftvar_in_aenv Ξ [<=] dom Ξ)
        by (eapply (proj2 a_solve_sub_eq_generated_ftvar); exact Hp).
      pick fresh δ for
        (ftvar_in_aenv (Ξl ++ Θ0) `union` dom Ξm `union` dom Ξ
           `union` ftvar_in_pskl P `union` ftvar_in_pskl Q
           `union` ftvar_in_pskl P' `union` singleton b).
      pose proof (@a_solve_eq_move_binder _ _ _ _ _ _ δ Hp
                    ltac:(clear - Hfr; solve_notin_auto)
                    ltac:(clear - Fr; solve_notin_auto)) as Hr.
      rewrite (swap_aenv_fresh_id b δ (Ξl ++ Θ0)) in Hr
        by (clear - Hfr Fr; fsetdec).
      rewrite (swap_aenv_fresh_id b δ Ξ) in Hr
        by (clear - HbΞ Fr HΞf; fsetdec).
      rewrite <- (@close_pskl_subst_var P' b δ ltac:(clear - Fr; solve_notin_auto)).
      apply a_solve_eq__forall with (β := δ);
        [ rewrite ftvar_in_aenv_weaken_mid by exact Hfm;
          clear - Fr; fsetdec | ].
      eapply IHe with (Ξl := ((δ ~ abind_tvar) ++ Ξl)) (Ξm := Ξm) (Θ0 := Θ0);
        [ rewrite ! size_pskl_open_pskl_wrt_pskl_var; cbn; lia
        | exact Hr | reflexivity | exact Hfm
        | intros x Hx; specialize (Hdisj x Hx);
          assert (Hxδ : x `notin` singleton δ) by (clear - Fr Hx; fsetdec);
          simpl_env in Hdisj; simpl_env;
          clear - Hdisj Hxδ; fsetdec
        | intros x Hx; specialize (Hftv x Hx);
          pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f δ))
            as Hup2;
          assert (Hxδ : x `notin` singleton δ) by (clear - Fr Hx; fsetdec);
          cbn in Hftv, Hup2; clear - Hftv Hup2 Hxδ; fsetdec
        | intros x Hx; specialize (Hout x Hx);
          pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                        P' (pskl_var_f δ) b) as Hsu;
          pose proof (ftvar_in_pskl_close_pskl_wrt_pskl P' b) as Hcl;
          assert (Hxδ : x `notin` singleton δ) by (clear - Fr Hx; fsetdec);
          cbn in Hout, Hsu; clear - Hout Hsu Hcl Hxδ; fsetdec
        | exact Hblk ].
    -
      apply a_solve_eq__univ_ghost_both.
      eapply IHe with (Ξl := Ξl) (Ξm := Ξm) (Θ0 := Θ0);
        [ cbn; lia | exact Hp | reflexivity | exact Hfm | exact Hdisj
        | intros x Hx; specialize (Hftv x Hx); cbn in Hftv; exact Hftv
        | intros x Hx; specialize (Hout x Hx); cbn in Hout; exact Hout
        | exact Hblk ].
    -
      assert (HbΞ : b `notin` dom Ξ)
        by (eapply a_solve_eq_generated_apart_binder; exact Hp).
      assert (HΞf : ftvar_in_aenv Ξ [<=] dom Ξ)
        by (eapply (proj2 a_solve_sub_eq_generated_ftvar); exact Hp).
      pick fresh δ for
        (ftvar_in_aenv (Ξl ++ Θ0) `union` dom Ξm `union` dom Ξ
           `union` ftvar_in_pskl P `union` ftvar_in_pskl Q
           `union` ftvar_in_pskl P' `union` singleton b).
      pose proof (@a_solve_eq_move_binder_univ_ghost_l _ _ _ _ _ _ δ Hp
                    ltac:(clear - Hfr; cbn in Hfr; solve_notin_auto)
                    ltac:(clear - Fr; solve_notin_auto)) as Hr.
      rewrite (swap_aenv_fresh_id b δ (Ξl ++ Θ0)) in Hr
        by (clear - Hfr Fr; fsetdec).
      rewrite (swap_aenv_fresh_id b δ Ξ) in Hr
        by (clear - HbΞ Fr HΞf; fsetdec).
      rewrite <- (@close_pskl_subst_var P' b δ ltac:(clear - Fr; solve_notin_auto)).
      apply a_solve_eq__univ_ghost_l_all with (β := δ);
        [ rewrite ftvar_in_aenv_weaken_mid by exact Hfm;
          clear - Fr; fsetdec | ].
      eapply IHe with (Ξl := ((δ ~ abind_tvar) ++ Ξl)) (Ξm := Ξm) (Θ0 := Θ0);
        [ rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia
        | exact Hr | reflexivity | exact Hfm
        | intros x Hx; specialize (Hdisj x Hx);
          assert (Hxδ : x `notin` singleton δ) by (clear - Fr Hx; fsetdec);
          simpl_env in Hdisj; simpl_env;
          clear - Hdisj Hxδ; fsetdec
        | intros x Hx; specialize (Hftv x Hx); cbn in Hftv |- *; exact Hftv
        | intros x Hx; specialize (Hout x Hx);
          pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                        P' (pskl_var_f δ) b) as Hsu;
          pose proof (ftvar_in_pskl_close_pskl_wrt_pskl P' b) as Hcl;
          assert (Hxδ : x `notin` singleton δ) by (clear - Fr Hx; fsetdec);
          cbn in Hout, Hsu; clear - Hout Hsu Hcl Hxδ; fsetdec
        | exact Hblk ].
    -
      apply a_solve_eq__univ_ghost_l_guarded; [ exact Hg | ].
      eapply IHe with (Ξl := Ξl) (Ξm := Ξm) (Θ0 := Θ0);
        [ cbn; lia | exact Hp | reflexivity | exact Hfm | exact Hdisj
        | intros x Hx; specialize (Hftv x Hx); cbn in Hftv; exact Hftv
        | exact Hout | exact Hblk ].
    -
      assert (HbΞ : b `notin` dom Ξ)
        by (eapply a_solve_eq_generated_apart_binder; exact Hp).
      assert (HΞf : ftvar_in_aenv Ξ [<=] dom Ξ)
        by (eapply (proj2 a_solve_sub_eq_generated_ftvar); exact Hp).
      pick fresh δ for
        (ftvar_in_aenv (Ξl ++ Θ0) `union` dom Ξm `union` dom Ξ
           `union` ftvar_in_pskl P `union` ftvar_in_pskl Q
           `union` ftvar_in_pskl P' `union` singleton b).
      pose proof (@a_solve_eq_move_binder_univ_ghost_r _ _ _ _ _ _ δ Hp
                    ltac:(clear - Hfr; cbn in Hfr; solve_notin_auto)
                    ltac:(clear - Fr; solve_notin_auto)) as Hr.
      rewrite (swap_aenv_fresh_id b δ (Ξl ++ Θ0)) in Hr
        by (clear - Hfr Fr; fsetdec).
      rewrite (swap_aenv_fresh_id b δ Ξ) in Hr
        by (clear - HbΞ Fr HΞf; fsetdec).
      rewrite <- (@close_pskl_subst_var P' b δ ltac:(clear - Fr; solve_notin_auto)).
      apply a_solve_eq__all_l_univ_ghost with (β := δ);
        [ rewrite ftvar_in_aenv_weaken_mid by exact Hfm;
          clear - Fr; fsetdec | ].
      eapply IHe with (Ξl := ((δ ~ abind_tvar) ++ Ξl)) (Ξm := Ξm) (Θ0 := Θ0);
        [ rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia
        | exact Hr | reflexivity | exact Hfm
        | intros x Hx; specialize (Hdisj x Hx);
          assert (Hxδ : x `notin` singleton δ) by (clear - Fr Hx; fsetdec);
          simpl_env in Hdisj; simpl_env;
          clear - Hdisj Hxδ; fsetdec
        | intros x Hx; specialize (Hftv x Hx);
          pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f δ))
            as Hup2;
          assert (Hxδ : x `notin` singleton δ) by (clear - Fr Hx; fsetdec);
          cbn in Hftv, Hup2; clear - Hftv Hup2 Hxδ; fsetdec
        | intros x Hx; specialize (Hout x Hx);
          pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                        P' (pskl_var_f δ) b) as Hsu;
          pose proof (ftvar_in_pskl_close_pskl_wrt_pskl P' b) as Hcl;
          assert (Hxδ : x `notin` singleton δ) by (clear - Fr Hx; fsetdec);
          cbn in Hout, Hsu; clear - Hout Hsu Hcl Hxδ; fsetdec
        | exact Hblk ].
    -
      apply a_solve_eq__univ_ghost_r_guarded; [ exact Hg | ].
      eapply IHe with (Ξl := Ξl) (Ξm := Ξm) (Θ0 := Θ0);
        [ cbn; lia | exact Hp | reflexivity | exact Hfm | exact Hdisj
        | exact Hftv | exact Hout | exact Hblk ]. }
Qed.

Lemma a_solve_sub_weaken_mid_flex : forall Θ m P P0 Ξ P' Ξl Ξm Θ0,
  {{ Θ ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' }}a ->
  Θ = Ξl ++ Θ0 -> all_flex_mono Ξm ->
  (forall x, x `in` dom Ξm -> x `notin` dom (Ξl ++ Θ0)) ->
  (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P) ->
  (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P') ->
  (forall x, x `in` dom Ξm -> x `notin` dom Ξ) ->
  {{ (Ξl ++ Ξm ++ Θ0) ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' }}a.
Proof.
  intros. eapply (proj1 (a_solve_sub_eq_weaken_mid_flex_size
                           (2 * (size_pskl P + size_pskl P0) + 1)));
    eauto.
Qed.

Lemma a_solve_eq_weaken_mid_flex : forall Θ P P0 Ξ P' Ξl Ξm Θ0,
  {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a ->
  Θ = Ξl ++ Θ0 -> all_flex_mono Ξm ->
  (forall x, x `in` dom Ξm -> x `notin` dom (Ξl ++ Θ0)) ->
  (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P) ->
  (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P') ->
  (forall x, x `in` dom Ξm -> x `notin` dom Ξ) ->
  {{ (Ξl ++ Ξm ++ Θ0) ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a.
Proof.
  intros. eapply (proj2 (a_solve_sub_eq_weaken_mid_flex_size
                           (2 * (size_pskl P + size_pskl P0))));
    eauto.
Qed.

Lemma a_solve_eq_weaken_flex_block : forall Θ0 P P0 Ξ P' Ξm,
  {{ Θ0 ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a ->
  all_flex_mono Ξm ->
  (forall x, x `in` dom Ξm -> x `notin` dom Θ0) ->
  (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P) ->
  (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P') ->
  (forall x, x `in` dom Ξm -> x `notin` dom Ξ) ->
  {{ (Ξm ++ Θ0) ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a.
Proof.
  intros Θ0 P P0 Ξ P' Ξm H Hfm Hd HP HP' Hblk.
  exact (@a_solve_eq_weaken_mid_flex Θ0 P P0 Ξ P' nil Ξm Θ0
           H eq_refl Hfm Hd HP HP' Hblk).
Qed.

Definition solve_ext (Θ0 Θ : aenv) (Pi P0 : pskl) (L : atoms)
    (Post : metasubst -> pskl -> Prop) : Prop :=
  exists (Ξ : aenv) (Pa : pskl) (κ' : metasubst),
    {{ Θ0 ⊢ₑ Pi ∼ P0 ⤳ Ξ ⨾ Pa }}a /\
    all_flex_mono Ξ /\
    uniq Ξ /\
    keys κ' = keys Ξ /\
    (forall α, α `in` dom Ξ -> α `notin` L) /\
    Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κ' /\
    Post κ' Pa.

Lemma forall_wf_mono_weaken : forall (Θ Θ' : aenv) (κ' : metasubst),
  (forall x b, binds x b Θ -> binds x b Θ') ->
  Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κ' ->
  Forall (fun p => a_wf_ptyp Θ' (snd p) /\ mono_ptyp (snd p)) κ'.
Proof.
  intros Θ Θ' κ' Hmon H; induction H as [ | p l0 Hp Hl IH ]; [ constructor | ].
  constructor; [ | exact IH ].
  destruct Hp as [Hw Hm]; split;
    [ eapply a_wf_ptyp_weaken; eassumption | exact Hm ].
Qed.

Lemma solve_ext_nil : forall Θ0 Θ Pi P0 L Post Pa,
  {{ Θ0 ⊢ₑ Pi ∼ P0 ⤳ nil ⨾ Pa }}a ->
  Post nil Pa ->
  solve_ext Θ0 Θ Pi P0 L Post.
Proof.
  intros Θ0 Θ Pi P0 L Post Pa Hs Hq.
  exists nil, Pa, nil.
  split; [ exact Hs | ].
  split; [ apply Forall_nil | ].
  split; [ apply uniq_nil | ].
  split; [ reflexivity | ].
  split; [ intros α0 Hα0; cbn in Hα0; exfalso; clear - Hα0; fsetdec | ].
  split; [ apply Forall_nil | ].
  exact Hq.
Qed.

Lemma solve_ext_step : forall Θ0 Θ Pi P0 Pi' P0' L Post Post',
  (forall Ξ Pa, {{ Θ0 ⊢ₑ Pi' ∼ P0' ⤳ Ξ ⨾ Pa }}a -> {{ Θ0 ⊢ₑ Pi ∼ P0 ⤳ Ξ ⨾ Pa }}a) ->
  (forall κ' Pa, Post' κ' Pa -> Post κ' Pa) ->
  solve_ext Θ0 Θ Pi' P0' L Post' ->
  solve_ext Θ0 Θ Pi P0 L Post.
Proof.
  intros Θ0 Θ Pi P0 Pi' P0' L Post Post' Hstep Hpost
         (Ξ & Pa & κ' & Hs & Hfm & Hu & Hk & Hfr & HF & Hq).
  exists Ξ, Pa, κ'. repeat split; auto.
Qed.

Lemma solve_ext_post_solve : forall Θ0 Θ Pi P0 L Post Post',
  (forall Ξ κ' Pa, {{ Θ0 ⊢ₑ Pi ∼ P0 ⤳ Ξ ⨾ Pa }}a -> Post' κ' Pa -> Post κ' Pa) ->
  solve_ext Θ0 Θ Pi P0 L Post' ->
  solve_ext Θ0 Θ Pi P0 L Post.
Proof.
  intros Θ0 Θ Pi P0 L Post Post' Hpost
         (Ξ & Pa & κ' & Hs & Hfm & Hu & Hk & Hfr & HF & Hq).
  exists Ξ, Pa, κ'. repeat split; eauto.
Qed.

Definition solve_sub_ext (Θ0 Θ : aenv) (m : mode) (Pi P0 : pskl) (L : atoms)
    (Post : metasubst -> pskl -> Prop) : Prop :=
  exists (Ξ : aenv) (Pa : pskl) (κ' : metasubst),
    {{ Θ0 ⊢ₛ Pi ≼[ m ] P0 ⤳ Ξ ⨾ Pa }}a /\
    all_flex_mono Ξ /\
    uniq Ξ /\
    keys κ' = keys Ξ /\
    (forall α, α `in` dom Ξ -> α `notin` L) /\
    Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κ' /\
    {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ Pa }}a /\
    Post κ' Pa.

Lemma solve_sub_ext_nil : forall Θ0 Θ m Pi P0 L Post Pa,
  {{ Θ0 ⊢ₛ Pi ≼[ m ] P0 ⤳ nil ⨾ Pa }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ Pa }}a ->
  Post nil Pa ->
  solve_sub_ext Θ0 Θ m Pi P0 L Post.
Proof.
  intros Θ0 Θ m Pi P0 L Post Pa Hs Hwf Hq.
  exists nil, Pa, nil.
  split; [ exact Hs | ].
  split; [ apply Forall_nil | ].
  split; [ apply uniq_nil | ].
  split; [ reflexivity | ].
  split; [ intros α0 Hα0; cbn in Hα0; exfalso; clear - Hα0; fsetdec | ].
  split; [ apply Forall_nil | ].
  split; [ cbn [app]; exact Hwf | ].
  exact Hq.
Qed.

Definition solve_eq_mono_concl (Θ0 Θ Θw : aenv) (κ : metasubst) (Δ Ψi : atoms)
    (τ : ptyp) (Pi P0 : pskl) (L : atoms) : Prop :=
  solve_ext Θ0 Θw Pi P0 L
    (fun κ' Pa =>
       {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κ' ++ κ) Pa) ⊑ᵖ[ Ψi ] (ptyp_to_uskl_syn τ) }}ad).

Lemma solve_eq_mono_nil : forall Θ0 Θ Θw κ Δ Ψi τ Pi P0 L Pa,
  {{ Θ0 ⊢ₑ Pi ∼ P0 ⤳ nil ⨾ Pa }}a ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pa) ⊑ᵖ[ Ψi ] (ptyp_to_uskl_syn τ) }}ad ->
  solve_eq_mono_concl Θ0 Θ Θw κ Δ Ψi τ Pi P0 L.
Proof.
  intros Θ0 Θ Θw κ Δ Ψi τ Pi P0 L Pa Hs Hq.
  eapply solve_ext_nil; [ exact Hs | cbn [app]; exact Hq ].
Qed.

Lemma solve_eq_mono_wrap : forall Θ0 Θ Θw κ Δ Ψi τ τe Pi P0 Pi' P0' L,
  a_def_chain Θ τ τe ->
  (forall Ξ Pa, {{ Θ0 ⊢ₑ Pi' ∼ P0' ⤳ Ξ ⨾ Pa }}a -> {{ Θ0 ⊢ₑ Pi ∼ P0 ⤳ Ξ ⨾ Pa }}a) ->
  solve_eq_mono_concl Θ0 Θ Θw κ Δ Ψi τe Pi' P0' L ->
  solve_eq_mono_concl Θ0 Θ Θw κ Δ Ψi τ Pi P0 L.
Proof.
  intros Θ0 Θ Θw κ Δ Ψi τ τe Pi P0 Pi' P0' L Hc Hstep H.
  eapply solve_ext_step;
    [ exact Hstep
    | intros κ' Pa Hq; eapply ad_ppre_chain_fold; [ exact Hc | exact Hq ]
    | exact H ].
Qed.

Lemma a_solve_eq_mono : forall n Θ0 Θ Θw κ Δ Ψi τ Pi P0,
  size_pskl Pi + size_pskl P0 <= n ->
  {{ ⊢ Θ }}a -> {{ ⊢ Θ0 }}a ->
  {{ ⊢ Θw }}a ->
  (forall x b, binds x b Θw -> binds x b Θ) ->
  (forall α τ0, binds α (abind_flex_mono_def τ0) Θ ->
     binds α (abind_flex_mono_def τ0) Θw) ->
  {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a -> {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  κ ∷ Θ0 ⊑ Θ ->
  mono_ptyp τ ->
  (a_wf_ptyp Θw τ \/ (exists α0, τ = ptyp_var_f α0 /\ binds α0 abind_tvar Θ)) ->
  delta_def_fresh Δ Θ ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (ptyp_to_uskl_syn τ) }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (ptyp_to_bskl_syn τ) }}ad ->
  forall L, ftvar_in_aenv Θ0 [<=] L ->
  solve_eq_mono_concl Θ0 Θ Θw κ Δ Ψi τ Pi P0 L.
Proof.
  induction n; intros Θ0 Θ Θw κ Δ Ψi τ Pi P0 Hn
    HwfΘ HwfΘ0 HwfΘw Hmon Hdefs HwfPi HwfP0 Hκ Hmτ Hwfτ Hdf Hpre Hrefine L HL.
  { pose proof (size_pskl_min Pi); pose proof (size_pskl_min P0); lia. }
  destruct Pi as [ | nb | α | Pi1 Pi2 | Pib | | Pi' ].
  -
    simpl in Hpre.
    destruct (ad_ppre_unit_subject_chain_inv HwfΘ Hpre eq_refl eq_refl Hmτ)
      as [Hc HΨi].
    pose proof (ad_refine_chain_unfold Hc HwfΘ Hrefine (delta_def_fresh_empty Θ))
      as Href'.
    simpl in Href'.
    assert (Hpre_u : {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ pskl_unit) ⊑ᵖ[ Ψi ] uskl_unit }}ad)
      by (simpl; apply ad_ppre__unit; exact HΨi).
    destruct (a_solve_eq_unit (n := S n) (Θ := Θ) (Δ := Δ)
                Hn HwfΘ HwfΘ0 HwfPi HwfP0 Hκ Hpre_u Href')
      as (Pa & Hsolve & Hprec).
    eapply solve_eq_mono_nil;
      [ exact Hsolve | eapply ad_ppre_chain_fold; eassumption ].
  -  inversion HwfPi.
  -
    eapply solve_eq_mono_nil; [ apply a_solve_eq__var | exact Hpre ].
  -
    assert (HwfPi1 : {{ Θ0 ⨟ empty ⊢ₚₛ Pi1 }}a) by (inversion HwfPi; assumption).
    assert (HwfPi2 : {{ Θ0 ⨟ empty ⊢ₚₛ Pi2 }}a) by (inversion HwfPi; assumption).
    simpl in Hpre.
    destruct (ad_ppre_arrow_subject_chain_inv HwfΘ Hpre eq_refl eq_refl Hmτ)
      as (τ1 & τ2 & Ψ1 & Ψ2 & Hc & Hm1 & Hm2 & Hp1 & Hp2 & HΨ).
    assert (Hwfτ' : a_wf_ptyp Θw τ).
    { destruct Hwfτ as [Hw | (α0 & Heqτ & Hrig0)]; [ exact Hw | ].
      exfalso. subst τ.
      pose proof (a_def_chain_rigid_var_inv Hc HwfΘ Hrig0) as Hcc.
      discriminate Hcc. }
    pose proof (ad_refine_chain_unfold Hc HwfΘ Hrefine (delta_def_fresh_empty Θ))
      as Href'.
    destruct P0 as [ | nb0 | β | P01 P02 | P0b | | P0' ].
    +
      simpl in Href'. inversion Href'.
    +  inversion HwfP0.
    +
      inversion HwfP0; subst;
      match goal with H : a_binds_tvar β _ |- _ => rename H into Habt end.
      destruct Habt as [Hrig | Hflx].
      *
        exfalso.
        assert (Hmid : msubst_pskl κ (pskl_var_f β) = pskl_var_f β)
          by (eapply msubst_pskl_tvar_id;
                [ exact HwfΘ0 | exact Hκ | exact Hrig ]).
        rewrite Hmid in Href'. simpl in Href'.
        eapply (ad_refine_syn_rigid_var_nonvar_absurd Href');
          [ intros x b Hb; exact Hb | apply a_wf_aenv_uniq; exact HwfΘ
          | eapply a_inc_binds_tvar; eauto | intros β0 Hcc; discriminate Hcc ].
      *
        assert (HΨi : Ψi [=] empty)
          by (eapply ad_ppre_mono_tags_empty;
                [ exact HwfΘ | exact Hpre | reflexivity | exact Hmτ ]).
        assert (Hszg : size_pskl (pskl_arrow Pi1 Pi2) <= S n)
          by (cbn in Hn |- *; lia).
        destruct (@a_guess_ty_witness_mono (S n) Θ0 Θ Θw κ Δ Ψi τ
                    (pskl_arrow Pi1 Pi2) Hszg HwfΘ HwfΘw Hmon Hdefs
                    HwfPi Hmτ Hwfτ' Hpre L)
          as (Ξg & Ag & κg & Hgu & Hfmg & Hug & Hkg & Hfrg & HFg & Hqg).
        exists Ξg, (ptyp_to_pskl Ag), κg.
        split; [ apply a_solve_eq__flex_r;
                   [ exact Hflx
                   | split; [ eapply a_wf_pskl_lc; exact HwfPi
                            | intros Hf; inversion Hf ]
                   | apply nonghost_pskl__arrow
                   | apply Hgu; exact HL ] | ].
        split; [ exact Hfmg | ].
        split; [ exact Hug | ].
        split; [ exact Hkg | ].
        split; [ exact Hfrg | ].
        split; [ exact HFg | ].
        exact Hqg.
    +
      assert (HwfP01 : {{ Θ0 ⨟ empty ⊢ₚₛ P01 }}a) by (inversion HwfP0; assumption).
      assert (HwfP02 : {{ Θ0 ⨟ empty ⊢ₚₛ P02 }}a) by (inversion HwfP0; assumption).
      assert (Hwfar : a_wf_ptyp Θw (ptyp_arrow τ1 τ2))
        by (eapply a_def_chain_wf_at; eassumption).
      assert (Hwf1 : a_wf_ptyp Θw τ1) by (inversion Hwfar; assumption).
      assert (Hwf2 : a_wf_ptyp Θw τ2) by (inversion Hwfar; assumption).
      simpl in Href'.
      inversion Href'; subst.
      match goal with
      | Hr1 : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ P01) ⊳ _ }}ad,
        Hr2 : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ P02) ⊳ _ }}ad |- _ =>
        rename Hr1 into Href1; rename Hr2 into Href2
      end.

      assert (HL1 : ftvar_in_aenv Θ0
                    [<=] L `union` ftvar_in_pskl Pi1 `union` ftvar_in_pskl Pi2
                           `union` ftvar_in_pskl P01 `union` ftvar_in_pskl P02)
        by (clear - HL; fsetdec).
      destruct (IHn Θ0 Θ Θw κ Δ Ψ1 τ1 Pi1 P01
                  ltac:(simpl in Hn; lia)
                  HwfΘ HwfΘ0 HwfΘw Hmon Hdefs HwfPi1 HwfP01 Hκ Hm1 (or_introl Hwf1) Hdf Hp1 Href1
                  (L `union` ftvar_in_pskl Pi1 `union` ftvar_in_pskl Pi2
                     `union` ftvar_in_pskl P01 `union` ftvar_in_pskl P02)
                  HL1)
        as (Ξ1 & Pa1 & κa & Hs1 & Hfm1 & Hu1 & Hk1 & Hfr1 & HF1 & Hq1).
      assert (Hdκa : dom κa [=] dom Ξ1) by (apply keys_eq_dom; exact Hk1).

      assert (HΞ1Θ0 : forall α0, α0 `in` dom Ξ1 -> α0 `notin` dom Θ0).
      { intros α0 Hα0. specialize (Hfr1 α0 Hα0).
        pose proof (dom_subset_ftvar_in_aenv Θ0) as Hd.
        clear - Hfr1 Hd HL; fsetdec. }
      assert (Hwfblk : {{ ⊢ (Ξ1 ++ Θ0) }}a)
        by (apply a_wf_aenv_prepend_flex_block; assumption).
      assert (Hκ1 : (κa ++ κ) ∷ (Ξ1 ++ Θ0) ⊑ Θ)
        by (apply a_inc_flex_prefix_build;
              [ exact Hfm1 | exact Hk1
              | eapply forall_wf_mono_weaken; eassumption
              | exact Hκ ]).
      assert (HwfPi2' : {{ (Ξ1 ++ Θ0) ⨟ empty ⊢ₚₛ Pi2 }}a)
        by (apply a_wf_pskl_app_weaken; exact HwfPi2).
      assert (HwfP02' : {{ (Ξ1 ++ Θ0) ⨟ empty ⊢ₚₛ P02 }}a)
        by (apply a_wf_pskl_app_weaken; exact HwfP02).
      assert (Heqi2 : msubst_pskl (nil ++ κa ++ κ) Pi2
                      = msubst_pskl (nil ++ κ) Pi2).
      { apply msubst_pskl_mid_skip. intros α0 Hα0.
        assert (Hin : α0 `in` dom Ξ1) by (clear - Hα0 Hdκa; fsetdec).
        specialize (Hfr1 α0 Hin). clear - Hfr1; fsetdec. }
      assert (Heqp2 : msubst_pskl (nil ++ κa ++ κ) P02
                      = msubst_pskl (nil ++ κ) P02).
      { apply msubst_pskl_mid_skip. intros α0 Hα0.
        assert (Hin : α0 `in` dom Ξ1) by (clear - Hα0 Hdκa; fsetdec).
        specialize (Hfr1 α0 Hin). clear - Hfr1; fsetdec. }
      cbn [app] in Heqi2, Heqp2.
      assert (Hp2' : {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κa ++ κ) Pi2)
                             ⊑ᵖ[ Ψ2 ] (ptyp_to_uskl_syn τ2) }}ad)
        by (rewrite Heqi2; exact Hp2).
      assert (Href2' : {{ Θ ⨟ empty ⊢ᵣ
                (pskl_to_bskl_inh (msubst_pskl (κa ++ κ) P02))
                ⊳ (ptyp_to_bskl_syn τ2) }}ad)
        by (rewrite Heqp2; exact Href2).
      assert (HL2 : ftvar_in_aenv (Ξ1 ++ Θ0)
                    [<=] L `union` ftvar_in_pskl Pi1 `union` ftvar_in_pskl Pi2
                           `union` ftvar_in_pskl P01 `union` ftvar_in_pskl P02
                           `union` dom Ξ1).
      { rewrite ftvar_in_aenv_app.
        pose proof (all_flex_mono_ftvar_in_aenv Hfm1) as Hf1.
        clear - HL Hf1; fsetdec. }

      destruct (IHn (Ξ1 ++ Θ0) Θ Θw (κa ++ κ) Δ Ψ2 τ2 Pi2 P02
                  ltac:(simpl in Hn; lia)
                  HwfΘ Hwfblk HwfΘw Hmon Hdefs HwfPi2' HwfP02' Hκ1 Hm2 (or_introl Hwf2) Hdf Hp2' Href2'
                  (L `union` ftvar_in_pskl Pi1 `union` ftvar_in_pskl Pi2
                     `union` ftvar_in_pskl P01 `union` ftvar_in_pskl P02
                     `union` dom Ξ1)
                  HL2)
        as (Ξ2 & Pa2 & κb & Hs2 & Hfm2 & Hu2 & Hk2 & Hfr2 & HF2 & Hq2).
      assert (Hdκb : dom κb [=] dom Ξ2) by (apply keys_eq_dom; exact Hk2).
      assert (Hdisj : disjoint Ξ2 Ξ1).
      { unfold disjoint. intros α0 Hα0.
        assert (Hin2 : α0 `in` dom Ξ2) by (clear - Hα0; fsetdec).
        specialize (Hfr2 α0 Hin2). clear - Hα0 Hfr2; fsetdec. }
      assert (HPa1 : ftvar_in_pskl Pa1
                     [<=] ftvar_in_pskl Pi1 `union` ftvar_in_pskl P01
                            `union` dom Ξ1)
        by (eapply a_solve_eq_ftv; exact Hs1).
      assert (Heq1 : msubst_pskl (nil ++ κb ++ (κa ++ κ)) Pa1
                     = msubst_pskl (nil ++ (κa ++ κ)) Pa1).
      { apply msubst_pskl_mid_skip. intros α0 Hα0.
        assert (Hin2 : α0 `in` dom Ξ2) by (clear - Hα0 Hdκb; fsetdec).
        specialize (Hfr2 α0 Hin2). clear - Hfr2 HPa1; fsetdec. }
      cbn [app] in Heq1.
      exists (Ξ2 ++ Ξ1), (pskl_arrow Pa1 Pa2), (κb ++ κa).
      split; [ apply a_solve_eq__arrow; eassumption | ].
      split; [ apply all_flex_mono_app; assumption | ].
      split; [ clear - Hu1 Hu2 Hdisj; solve_uniq | ].
      split; [ rewrite ! keys_app; rewrite Hk1, Hk2; reflexivity | ].
      split; [ intros α0 Hα0; rewrite dom_app in Hα0;
               destruct (union_1 Hα0) as [Hin2 | Hin1];
                 [ specialize (Hfr2 α0 Hin2); clear - Hfr2; fsetdec
                 | specialize (Hfr1 α0 Hin1); clear - Hfr1; fsetdec ] | ].
      split; [ apply Forall_app; split; assumption | ].
      eapply ad_ppre_chain_fold; [ exact Hc | ].
      rewrite list_app_assoc. cbn [msubst_pskl ptyp_to_uskl_syn].
      rewrite Heq1.
      apply ad_ppre__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2); eassumption.
    +
      simpl in Href'.
      exfalso.
      eapply ad_refine_allinh_lhs_mono_absurd;
        [ exact HwfΘ | exact Href' | reflexivity | reflexivity
        | apply mono_ptyp__arrow; assumption ].
    +
      eapply solve_eq_mono_nil; [ apply a_solve_eq__ghost_r | exact Hpre ].
    +
      assert (HwfP0' : {{ Θ0 ⨟ empty ⊢ₚₛ P0' }}a)
        by (inversion HwfP0; subst; rewrite aenv_minus_empty in *; assumption).
      assert (Hwfar : a_wf_ptyp Θw (ptyp_arrow τ1 τ2))
        by (eapply a_def_chain_wf_at; eassumption).
      simpl in Href'.
      inversion Href'; subst.
      assert (Hpre' : {{ Θ ⨟ Δ ⊢ˢ msubst_pskl κ (pskl_arrow Pi1 Pi2) ⊑ᵖ[ Ψi ]
                        (ptyp_to_uskl_syn (ptyp_arrow τ1 τ2)) }}ad)
        by (simpl; eapply ad_ppre__arrow; eassumption).
      assert (Hcv : solve_eq_mono_concl Θ0 Θ Θw κ Δ Ψi (ptyp_arrow τ1 τ2)
                      (pskl_arrow Pi1 Pi2) P0' L).
      { match goal with
        | Hin : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ P0') ⊳ _ }}ad |- _ =>
          apply (IHn Θ0 Θ Θw κ Δ Ψi (ptyp_arrow τ1 τ2) (pskl_arrow Pi1 Pi2) P0'
                   ltac:(simpl in Hn; simpl; lia)
                   HwfΘ HwfΘ0 HwfΘw Hmon Hdefs HwfPi HwfP0' Hκ
                   ltac:(apply mono_ptyp__arrow; assumption)
                   (or_introl Hwfar) Hdf Hpre' Hin L HL)
        end. }
      eapply solve_eq_mono_wrap; [ exact Hc | | exact Hcv ].
      intros Ξ0 Pa Hs. apply a_solve_eq__univ_ghost_r_guarded;
        [ apply guarded_pskl__arrow;
            [ eapply a_wf_pskl_lc; exact HwfPi1
            | eapply a_wf_pskl_lc; exact HwfPi2 ]
        | exact Hs ].
  -
    simpl in Hpre.
    exfalso.
    eapply ad_ppre_allsyn_subject_mono_absurd;
      [ exact HwfΘ | exact Hpre | reflexivity | reflexivity | exact Hmτ ].
  -
    simpl in Hpre.
    eapply solve_eq_mono_nil; [ apply a_solve_eq__ghost_l | ].
    eapply ad_refine_inh_ghost_ppre with (Δr := empty);
      [ exact HwfΘ | clear; fsetdec | exact Hrefine | reflexivity | reflexivity
      | exact Hmτ
      | destruct Hwfτ as [Hw | (α0 & -> & Hrig0)];
          [ eapply a_wf_ptyp_weaken; eassumption
          | apply a_wf_ptyp__var; left; exact Hrig0 ]
      | exact Hdf | exact Hpre ].
  -
    assert (HgPi' : guarded_pskl Pi') by (inversion HwfPi; assumption).
    assert (HwfPi' : {{ Θ0 ⨟ empty ⊢ₚₛ Pi' }}a)
      by (inversion HwfPi; subst; rewrite aenv_minus_empty in *; assumption).
    simpl in Hpre.
    destruct (ad_ppre_univ_ghost_subject_chain_inv HwfΘ Hpre eq_refl eq_refl Hmτ)
      as (τe & Hc & Hme & Hp').

    assert (Hwfe : a_wf_ptyp Θw τe \/
                   (exists α0, τe = ptyp_var_f α0 /\ binds α0 abind_tvar Θ))
      by (eapply a_def_chain_wf_or_rigid; eassumption).
    pose proof (ad_refine_chain_unfold Hc HwfΘ Hrefine (delta_def_fresh_empty Θ))
      as Href'.
    destruct P0 as [ | nb0 | β | P01 P02 | P0b | | P0' ].
    +
      assert (Hcv : solve_eq_mono_concl Θ0 Θ Θw κ Δ Ψi τe Pi' pskl_unit L)
        by (apply (IHn Θ0 Θ Θw κ Δ Ψi τe Pi' pskl_unit
                     ltac:(simpl in Hn; simpl; lia)
                     HwfΘ HwfΘ0 HwfΘw Hmon Hdefs HwfPi' HwfP0 Hκ Hme Hwfe
                     Hdf Hp' Href' L HL)).
      eapply solve_eq_mono_wrap; [ exact Hc | | exact Hcv ].
      intros Ξ0 Pa Hs. apply a_solve_eq__univ_ghost_l_guarded;
        [ apply guarded_pskl__unit | exact Hs ].
    +  inversion HwfP0.
    +
      assert (Hcv : solve_eq_mono_concl Θ0 Θ Θw κ Δ Ψi τe Pi' (pskl_var_f β) L)
        by (apply (IHn Θ0 Θ Θw κ Δ Ψi τe Pi' (pskl_var_f β)
                     ltac:(simpl in Hn; simpl; lia)
                     HwfΘ HwfΘ0 HwfΘw Hmon Hdefs HwfPi' HwfP0 Hκ Hme Hwfe
                     Hdf Hp' Href' L HL)).
      eapply solve_eq_mono_wrap; [ exact Hc | | exact Hcv ].
      intros Ξ0 Pa Hs. apply a_solve_eq__univ_ghost_l_guarded;
        [ apply guarded_pskl__var | exact Hs ].
    +
      assert (HwfP01 : {{ Θ0 ⨟ empty ⊢ₚₛ P01 }}a) by (inversion HwfP0; assumption).
      assert (HwfP02 : {{ Θ0 ⨟ empty ⊢ₚₛ P02 }}a) by (inversion HwfP0; assumption).
      assert (Hcv : solve_eq_mono_concl Θ0 Θ Θw κ Δ Ψi τe Pi' (pskl_arrow P01 P02) L)
        by (apply (IHn Θ0 Θ Θw κ Δ Ψi τe Pi' (pskl_arrow P01 P02)
                     ltac:(simpl in Hn; simpl; lia)
                     HwfΘ HwfΘ0 HwfΘw Hmon Hdefs HwfPi' HwfP0 Hκ Hme Hwfe
                     Hdf Hp' Href' L HL)).
      eapply solve_eq_mono_wrap; [ exact Hc | | exact Hcv ].
      intros Ξ0 Pa Hs. apply a_solve_eq__univ_ghost_l_guarded;
        [ apply guarded_pskl__arrow;
            [ eapply a_wf_pskl_lc; exact HwfP01
            | eapply a_wf_pskl_lc; exact HwfP02 ]
        | exact Hs ].
    +
      simpl in Href'.
      exfalso.
      eapply ad_refine_allinh_lhs_mono_absurd;
        [ exact HwfΘ | exact Href' | reflexivity | reflexivity | exact Hme ].
    +
      eapply solve_eq_mono_nil; [ apply a_solve_eq__ghost_r | exact Hpre ].
    +
      assert (HwfP0' : {{ Θ0 ⨟ empty ⊢ₚₛ P0' }}a)
        by (inversion HwfP0; subst; rewrite aenv_minus_empty in *; assumption).
      simpl in Href'.
      destruct (ad_refine_univ_ghost_lhs_chain_inv HwfΘ Href' eq_refl eq_refl Hme)
        as (τf & Hc2 & Hmf & Hin).
      assert (Hwff : a_wf_ptyp Θw τf \/
                     (exists α0, τf = ptyp_var_f α0 /\ binds α0 abind_tvar Θ))
        by (eapply a_def_chain_wf_or_rigid; eassumption).
      pose proof (ad_ppre_chain_unfold Hc2 HwfΘ Hdf Hp') as Hp''.
      destruct (IHn Θ0 Θ Θw κ Δ Ψi τf Pi' P0'
                  ltac:(simpl in Hn; simpl; lia)
                  HwfΘ HwfΘ0 HwfΘw Hmon Hdefs HwfPi' HwfP0' Hκ Hmf Hwff
                  Hdf Hp'' Hin L HL)
        as (Ξ0 & Pa & κ' & Hs & Hfm & Hu & Hk & Hfr & HF & Hq).
      exists Ξ0, (pskl_univ_ghost Pa), κ'.
      split; [ apply a_solve_eq__univ_ghost_both; exact Hs | ].
      split; [ exact Hfm | ].
      split; [ exact Hu | ].
      split; [ exact Hk | ].
      split; [ exact Hfr | ].
      split; [ exact HF | ].
      eapply ad_ppre_chain_fold;
        [ eapply a_def_chain_trans; eassumption | ].
      simpl. apply ad_ppre__univ_ghost_remove. exact Hq.
Qed.

Lemma a_solve_eq_var : forall n Θ0 Θ Θw κ Δ Ψi α Pi P0,
  size_pskl Pi + size_pskl P0 <= n ->
  {{ ⊢ Θ }}a -> {{ ⊢ Θ0 }}a ->
  {{ ⊢ Θw }}a ->
  (forall x b, binds x b Θw -> binds x b Θ) ->
  (forall α0 τ0, binds α0 (abind_flex_mono_def τ0) Θ ->
     binds α0 (abind_flex_mono_def τ0) Θw) ->
  {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a -> {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  κ ∷ Θ0 ⊑ Θ ->
  (a_binds_tvar α Θw \/ binds α abind_tvar Θ) ->
  delta_def_fresh Δ Θ ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (uskl_var_f α) }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (bskl_var_f α) }}ad ->
  forall L, ftvar_in_aenv Θ0 [<=] L ->
  solve_eq_mono_concl Θ0 Θ Θw κ Δ Ψi (ptyp_var_f α) Pi P0 L.
Proof.
  intros n Θ0 Θ Θw κ Δ Ψi α Pi P0 Hn HwfΘ HwfΘ0 HwfΘw Hmon Hdefs
         HwfPi HwfP0 Hκ Hbα Hdf Hpre Hrefine L HL.
  eapply a_solve_eq_mono with (τ := ptyp_var_f α) (Θw := Θw); eauto.
  - auto with fresco.
  - destruct Hbα as [Hb | Hb];
      [ left; apply a_wf_ptyp__var; exact Hb
      | right; exists α; split; [ reflexivity | exact Hb ] ].
Qed.

Lemma ad_ppre_mono_paint_dot_ghost_absurd : forall Θ Δ Ψ P ψ,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  ψ = uskl_dot_ghost ->
  forall τb, P = ptyp_to_pskl τb -> mono_ptyp τb ->
  False.
Proof.
  intros Θ Δ Ψ P ψ HwfΘ H; induction H; intros Heqψ τb HeqS Hmb;
    try discriminate Heqψ.
  -
    destruct τb; simpl in HeqS; discriminate HeqS.
  -
    destruct τb; simpl in HeqS; discriminate HeqS.
  -
    destruct τb; simpl in HeqS; try discriminate HeqS.
    inversion HeqS; subst.
    eapply IHad_partial_precise;
      [ exact HwfΘ | reflexivity | reflexivity
      | eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

Lemma ad_refine_mono_paint_ghost_rhs_absurd : forall Θ Δr Q' Q,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δr ⊢ᵣ Q' ⊳ Q }}ad ->
  Q = bskl_ghost ->
  forall τb, Q' = ptyp_to_bskl_syn τb -> mono_ptyp τb ->
  False.
Proof.
  intros Θ Δr Q' Q HwfΘ H; induction H; intros HeqQ τb HeqL Hmb;
    try discriminate HeqQ.
  -
    destruct τb; simpl in HeqL; discriminate HeqL.
  -
    destruct τb; simpl in HeqL; discriminate HeqL.
  -
    destruct τb; simpl in HeqL; try discriminate HeqL.
    inversion HeqL; subst.
    eapply IHad_refine_syn;
      [ exact HwfΘ | reflexivity | reflexivity
      | eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

Lemma a_solve_eq_ghostg : forall Θ0 Θ κ Δ Ψi Pi P0,
  {{ ⊢ Θ }}a -> {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a -> {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  κ ∷ Θ0 ⊑ Θ ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] uskl_dot_ghost }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ bskl_ghost }}ad ->
  exists Pa, {{ Θ0 ⊢ₑ Pi ∼ P0 ⤳ nil ⨾ Pa }}a /\
             {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pa) ⊑ᵖ[ Ψi ] uskl_dot_ghost }}ad.
Proof.
  intros Θ0 Θ κ Δ Ψi Pi P0 HwfΘ HwfΘ0 HwfPi HwfP0 Hκ Hpre Hrefine.
  assert (Habs_pre_var : forall v Ψ',
            {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ (pskl_var_f v)) ⊑ᵖ[ Ψ' ] uskl_dot_ghost }}ad ->
            False).
  { intros v Ψ' Hp. simpl in Hp.
    eapply ad_ppre_mono_paint_dot_ghost_absurd;
      [ exact HwfΘ | exact Hp | reflexivity | reflexivity
      | eapply a_inc_lookup_mono; eauto ]. }
  assert (Habs_ref_var : forall v,
            {{ Θ ⨟ empty ⊢ᵣ
              (pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f v))) ⊳ bskl_ghost }}ad ->
            False).
  { intros v Hr. simpl in Hr.
    assert (Hml : mono_ptyp (msubst_lookup κ v))
      by (eapply a_inc_lookup_mono; eauto).
    rewrite (ptyp_to_bskl_inh_syn_eq Hml) in Hr.
    eapply ad_refine_mono_paint_ghost_rhs_absurd;
      [ exact HwfΘ | exact Hr | reflexivity | reflexivity | exact Hml ]. }
  destruct Pi as [ | nb | α | Pi1 Pi2 | Pib | | Pi' ].
  -
    simpl in Hpre. inversion Hpre.
  -  inversion HwfPi.
  -
    exfalso. eapply Habs_pre_var. exact Hpre.
  -  simpl in Hpre. inversion Hpre.
  -  simpl in Hpre. inversion Hpre.
  -
    destruct P0 as [ | nb0 | β | P01 P02 | P0b | | P0' ].
    +
      simpl in Hrefine. inversion Hrefine.
    +  inversion HwfP0.
    +
      exfalso. eapply Habs_ref_var. exact Hrefine.
    +  simpl in Hrefine. inversion Hrefine.
    +  simpl in Hrefine. inversion Hrefine.
    +
      exists pskl_ghost; split; [ apply a_solve_eq__ghost_l | exact Hpre ].
    +
      simpl in Hrefine. inversion Hrefine; subst.
      exfalso.
      assert (HgP0' : guarded_pskl P0') by (inversion HwfP0; assumption).
      inversion HgP0'; subst.
      *
        match goal with
        | Hin : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ pskl_unit) ⊳ _ }}ad
          |- _ => simpl in Hin; inversion Hin
        end.
      *
        match goal with
        | Hin : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f _)) ⊳ _ }}ad
          |- _ => eapply Habs_ref_var; exact Hin
        end.
      *
        match goal with
        | Hin : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ (pskl_arrow _ _)) ⊳ _ }}ad
          |- _ => simpl in Hin; inversion Hin
        end.
  -
    simpl in Hpre. inversion Hpre; subst.
    exfalso.
    assert (HgPi' : guarded_pskl Pi') by (inversion HwfPi; assumption).
    inversion HgPi'; subst.
    +
      match goal with
      | Hp' : {{ _ ⨟ _ ⊢ˢ msubst_pskl κ pskl_unit ⊑ᵖ[ _ ] _ }}ad |- _ =>
          simpl in Hp'; inversion Hp'
      end.
    +
      match goal with
      | Hp' : {{ _ ⨟ _ ⊢ˢ msubst_pskl κ (pskl_var_f _) ⊑ᵖ[ _ ] _ }}ad |- _ =>
          eapply Habs_pre_var; exact Hp'
      end.
    +
      match goal with
      | Hp' : {{ _ ⨟ _ ⊢ˢ msubst_pskl κ (pskl_arrow _ _) ⊑ᵖ[ _ ] _ }}ad |- _ =>
          simpl in Hp'; inversion Hp'
      end.
Qed.

Lemma d_tags_skl_mono_paint : forall τ,
  mono_ptyp τ -> d_tags_skl empty (ptyp_to_uskl_syn τ).
Proof.
  intros τ Hm; induction Hm; simpl.
  - apply d_tags_skl__unit; fsetdec.
  - apply d_tags_skl__var; fsetdec.
  - apply d_tags_skl__arrow with (Ψ1 := empty) (Ψ2 := empty);
      [ assumption | assumption | fsetdec | fsetdec ].
Qed.

Lemma a_tags_sort_mono_paint : forall NM τ,
  mono_ptyp τ -> a_tags_sort NM empty (ptyp_to_uskl_syn τ).
Proof.
  intros NM τ Hm; destruct NM; constructor;
    auto using mono_ptyp_to_uskl_syn_is_dskl, d_tags_skl_mono_paint,
               mono_ptyp_to_uskl_syn_ghost_free.
Qed.

Lemma a_tags_sort_dot_univ_ghost_inv : forall NM Ψ ψ,
  a_tags_sort NM Ψ (uskl_dot_univ_ghost ψ) -> a_tags_sort NM Ψ ψ.
Proof.
  intros NM Ψ ψ H; inversion H; subst.
  - apply a_tags_sort__sk;
      [ match goal with Ht : is_dskl (uskl_dot_univ_ghost _) |- _ =>
          inversion Ht; subst; assumption end
      | match goal with Hd : d_tags_skl _ (uskl_dot_univ_ghost _) |- _ =>
          inversion Hd; subst; assumption end ].
  - match goal with Hg : uskl_ghost_free (uskl_dot_univ_ghost _) |- _ =>
      inversion Hg end.
Qed.

Lemma ad_ppre_mono_paint_dot_univ_ghost_absurd : forall Θ Δ Ψ P ψ,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  forall ψ0, ψ = uskl_dot_univ_ghost ψ0 ->
  forall τb, P = ptyp_to_pskl τb -> mono_ptyp τb ->
  False.
Proof.
  intros Θ Δ Ψ P ψ HwfΘ H; induction H; intros ψ0' Heqψ τb HeqS Hmb;
    try discriminate Heqψ.
  -  destruct τb; simpl in HeqS; discriminate HeqS.
  -  destruct τb; simpl in HeqS; discriminate HeqS.
  -  destruct τb; simpl in HeqS; discriminate HeqS.
  -
    destruct τb; simpl in HeqS; try discriminate HeqS.
    inversion HeqS; subst.
    eapply IHad_partial_precise;
      [ exact HwfΘ | reflexivity | reflexivity
      | eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

Lemma ad_refine_mono_paint_univ_ghost_rhs_absurd : forall Θ Δr Q' Q,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δr ⊢ᵣ Q' ⊳ Q }}ad ->
  forall Q0, Q = bskl_univ_ghost Q0 ->
  forall τb, Q' = ptyp_to_bskl_syn τb -> mono_ptyp τb ->
  False.
Proof.
  intros Θ Δr Q' Q HwfΘ H; induction H; intros Q0' HeqQ τb HeqL Hmb;
    try discriminate HeqQ.
  -  destruct τb; simpl in HeqL; discriminate HeqL.
  -  destruct τb; simpl in HeqL; discriminate HeqL.
  -  destruct τb; simpl in HeqL; discriminate HeqL.
  -
    destruct τb; simpl in HeqL; try discriminate HeqL.
    inversion HeqL; subst.
    eapply IHad_refine_syn;
      [ exact HwfΘ | reflexivity | reflexivity
      | eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.
