Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.prop_tag.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.basic.def_supply.
Require Import src.fresco.ext_algo.basic.def_guess.
Require Import src.fresco.ext_algo.consistency.def_consis.
Require Import src.fresco.ext_algo.consistency.prop_consis.
Require Import src.fresco.ext_algo.subtyping.def_look.
Require Import src.fresco.ext_algo.subtyping.def_solve.
Require Import src.fresco.ext_algo.subtyping.def_extract.
Require Import src.fresco.ext_algo.subtyping.prop_extract.
Require Import src.fresco.ext_algo.subtyping.def_sub.

Set Implicit Arguments.

Open Scope fresco_e_scope.

Lemma e_sub_sub_flex_supply_grows :
  (forall S0 NM M P0 Θ0 P Q S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e -> S0 [<=] S1) /\
  (forall S0 NM M P0 Θ0 Ξ α Q S1 Θ1,
     e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1 -> S0 [<=] S1).
Proof.
  apply e_sub_sub_flex_mutind;
    intros;
    try (match goal with
         | Hc : e_consis_chk _ _ _ _ _ _ |- _ =>
             destruct Hc as [Q0 Hc]; pose proof (e_consis_supply_grows Hc)
         end);
    try (match goal with
         | Hc : e_consis _ _ _ _ _ _ _ _ _ |- _ =>
             pose proof (e_consis_supply_grows Hc)
         end);
    try (match goal with
         | He : e_extract _ _ _ _ _ _ _ _ _ _ |- _ =>
             pose proof (e_extract_supply_grows He)
         end);
    fsetdec.
Qed.

Corollary e_sub_supply_grows : forall S0 NM M P0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e -> S0 [<=] S1.
Proof. apply e_sub_sub_flex_supply_grows. Qed.

Corollary e_sub_flex_supply_grows : forall S0 NM M P0 Θ0 Ξ α Q S1 Θ1,
  e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1 -> S0 [<=] S1.
Proof. apply e_sub_sub_flex_supply_grows. Qed.

#[local] Ltac sub_dom_facts :=
  repeat match goal with
  | H : e_consis_chk _ _ _ _ _ _ |- _ => destruct H as [? H]
  end;
  repeat match goal with
  | H : e_sub ?S0 _ _ _ _ _ _ ?S1 _ |- _ =>
      lazymatch goal with
      | _ : S0 [<=] S1 |- _ => fail
      | _ => pose proof (e_sub_supply_grows H)
      end
  | H : e_sub_flex ?S0 _ _ _ _ _ _ _ ?S1 _ |- _ =>
      lazymatch goal with
      | _ : S0 [<=] S1 |- _ => fail
      | _ => pose proof (e_sub_flex_supply_grows H)
      end
  | H : e_consis _ _ ?S0 _ _ _ _ ?S1 _ |- _ =>
      lazymatch goal with
      | _ : S0 [<=] S1 |- _ => fail
      | _ => pose proof (e_consis_supply_grows H)
      end
  | H : e_extract ?S0 _ _ _ _ _ _ ?S1 _ _ |- _ =>
      lazymatch goal with
      | _ : S0 [<=] S1 |- _ => fail
      | _ => pose proof (e_extract_supply_grows H)
      end
  end;
  repeat match goal with
  | H : e_consis _ _ _ ?Θ0 _ _ _ _ ?Θ1 |- _ =>
      lazymatch goal with
      | _ : dom Θ1 [<=] dom Θ0 ∪ _ |- _ => fail
      | _ => pose proof ((proj2 (proj2 e_assign_unify_consis_dom_upper))
                           _ _ _ _ _ _ _ _ _ H)
      end
  | H : e_extract _ _ _ _ _ _ _ _ ?Ξ _ |- _ =>
      lazymatch goal with
      | _ : dom Ξ [<=] _ |- _ => fail
      | _ => pose proof (e_extract_block H) as [? [? _]]
      end
  end.

Lemma e_sub_sub_flex_dom_upper :
  (forall S0 NM M P0 Θ0 P Q S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
     dom Θ1 [<=] dom Θ0 ∪ (S1 ∖ S0)) /\
  (forall S0 NM M P0 Θ0 Ξ α Q S1 Θ1,
     e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1 ->
     dom Θ1 [<=] dom (Ξ ++ Θ0) ∪ (S1 ∖ S0)).
Proof.
  apply e_sub_sub_flex_mutind;
    intros; sub_dom_facts;
    simpl_env in *; repeat rewrite dom_app in *; simpl dom in *;
    first [ match goal with
            | H : dom ?T [<=] _ |- dom ?T [<=] _ =>
                let z := fresh "z" in let Hz := fresh "Hz" in
                intros z Hz; apply H in Hz; clear H; fsetdec
            end
          | fsetdec ].
Qed.

Corollary e_sub_dom_upper : forall S0 NM M P0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
  dom Θ1 [<=] dom Θ0 ∪ (S1 ∖ S0).
Proof. apply e_sub_sub_flex_dom_upper. Qed.

Corollary e_sub_flex_dom_upper : forall S0 NM M P0 Θ0 Ξ α Q S1 Θ1,
  e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1 ->
  dom Θ1 [<=] dom (Ξ ++ Θ0) ∪ (S1 ∖ S0).
Proof. apply e_sub_sub_flex_dom_upper. Qed.

#[local] Ltac uniq_env :=
  simpl_env in *; destruct_uniq;
  repeat first [ apply uniq_push | apply uniq_cons_3 | apply uniq_app_4
               | apply uniq_one_1 | apply uniq_nil ];
  try unfold disjoint in *; simpl_env in *;
  solve [ assumption | fsetdec ].

Lemma e_sub_sub_flex_sound :
  (forall S0 NM M P0 Θ0 P Q S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
     uniq Θ0 ->
     ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 ∪ ftvar_in_pskl P [<=] S0 ->
     {{ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}a
     /\ uniq Θ1 /\ ftvar_in_aenv Θ1 [<=] S1 /\ ftvar_in_pskl Q [<=] S1) /\
  (forall S0 NM M P0 Θ0 Ξ α Q S1 Θ1,
     e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1 ->
     uniq (Ξ ++ Θ0) ->
     add α (ftvar_in_aenv (Ξ ++ Θ0) ∪ ftvar_in_pskl P0) [<=] S0 ->
     a_sub_flex NM M P0 Θ0 Ξ α Q Θ1
     /\ uniq Θ1 /\ ftvar_in_aenv Θ1 [<=] S1 /\ ftvar_in_pskl Q [<=] S1).
Proof.
  apply e_sub_sub_flex_mutind.

  -
    intros S NM P Θ0 Hu Hcov.
    repeat split; [ apply a_sub__infer | assumption
                  | clear - Hcov; fsetdec | clear - Hcov; fsetdec ].

  -
    intros S0 S1 Θ0 Θ1 A B HgfA HgfB HgdA HgdB Hc Hu Hcov.
    destruct Hc as [Q0 Hc].
    pose proof ((proj2 (proj2 e_assign_unify_consis_sound))
                  _ _ _ _ _ _ _ _ _ Hc Hu ltac:(clear - Hcov; fsetdec))
      as [Hca [Hu1 Hcv1]].
    pose proof (e_consis_supply_grows Hc) as Hgc.
    repeat split; [ | assumption | assumption | clear - Hcov Hgc; fsetdec ].
    apply a_sub__check; try assumption. exists Q0. assumption.

  -
    intros α S0 S1 Θ0 Θ1 Ξ A B Hgf Hsuf HuΞΘ Hnα Hs IH Hu Hcov.
    simpl in Hcov.
    pose proof (dom_subset_ftvar_in_aenv Θ0) as Hdc.
    assert (Hαdom : α `notin` dom Θ0) by (clear - Hdc Hcov Hnα; fsetdec).
    assert (Hu' : uniq ((α ~ abind_tvar) ++ Θ0))
      by (clear - Hu Hαdom; solve_uniq).
    assert (Hcov' : ftvar_in_aenv ((α ~ abind_tvar) ++ Θ0)
                    ∪ ftvar_in_pskl (open_pskl_wrt_pskl B (pskl_var_f α))
                    ∪ ftvar_in_pskl A [<=] add α S0).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B (pskl_var_f α)) as H1.
      simpl in H1. clear - H1 Hcov. env_simp. fsetdec. }
    destruct (IH Hu' Hcov') as [Hsa [Hu1 [Hcv1 Hq1]]].
    assert (HαΞ : α `notin` dom Ξ) by (clear - Hu1; simpl_env in *; solve_uniq).
    assert (HαΘ1 : α `notin` dom Θ1)
      by (clear - Hu1; simpl_env in *; solve_uniq).
    repeat split.
    + apply a_sub__forall_r with (α := α) (Ξ := Ξ); try assumption.
      clear - HαΞ HαΘ1 Hαdom Hnα Hcov. env_simp. fsetdec.
    + clear - Hu1; simpl_env in *; solve_uniq.
    + clear - Hcv1. env_simp. fsetdec.
    + pose proof (e_sub_supply_grows Hs) as Hgs.
      simpl. clear - Hcov Hgs. fsetdec.

  -
    intros S Θ0 P Hgd Hu Hcov.
    repeat split; [ apply a_sub__univ_ghost_r; assumption | assumption
                  | clear - Hcov; fsetdec | simpl; clear - Hcov; fsetdec ].

  -
    intros S0 S1 NM M P0 Θ0 Θ1 α Q Hf IH Hu Hcov.
    simpl in Hcov.
    assert (Hu' : uniq (nil ++ Θ0)) by (clear - Hu; simpl_env; assumption).
    assert (Hcov' : add α (ftvar_in_aenv (nil ++ Θ0) ∪ ftvar_in_pskl P0) [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    destruct (IH Hu' Hcov') as [Hfa [Hu1 [Hcv1 Hq1]]].
    repeat split; [ apply a_sub__flex_mono; assumption | assumption
                  | assumption | assumption ].

  -
    intros S0 S1 S2 NM M Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc Hs IH Hu Hcov.
    simpl in Hcov.
    pose proof ((proj2 (proj2 e_assign_unify_consis_sound))
                  _ _ _ _ _ _ _ _ _ Hc Hu ltac:(clear - Hcov; fsetdec))
      as [Hca [Hu1 Hcv1]].
    pose proof (e_consis_supply_grows Hc) as Hg1.
    assert (Hcov2 : ftvar_in_aenv Θ1 ∪ ftvar_in_pskl P0b
                      ∪ ftvar_in_pskl P2 [<=] S1)
      by (clear - Hcov Hcv1 Hg1; fsetdec).
    destruct (IH Hu1 Hcov2) as [Hsa [Hu2 [Hcv2 Hq2]]].
    pose proof (e_consis_out_ftvar Hc Hu ltac:(clear - Hcov; fsetdec)) as HqC.
    pose proof (e_sub_supply_grows Hs) as Hg2.
    repeat split; [ eapply a_sub__arrow; eassumption | assumption
                  | assumption | simpl; clear - HqC Hq2 Hg2; fsetdec ].

  -
    intros α S0 S1 S2 NM M P0 Θ0 Θ1 P Q Ξ P1 Hne Hgd Hnα Hex Hwf Hs IH Hu Hcov.
    simpl in Hcov.
    pose proof (e_extract_supply_grows Hex) as Hg1.
    pose proof (e_extract_block Hex) as [HinΞ [HfrΞ [HuΞ HftΞ]]].
    pose proof (e_extract_out_ftvar Hex) as Hout.
    pose proof (dom_subset_ftvar_in_aenv Θ0) as Hdc.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f α)) as Hop.
    simpl in Hop.
    assert (Hexa : {{ Θ0 ⊢ (open_pskl_wrt_pskl P (pskl_var_f α))
                      ⊳[ NM , α , M ] P0 ⤳ Ξ ↪ P1 }}a).
    { eapply e_extract_sound; [ exact Hex | ]. clear - Hop Hcov. fsetdec. }
    assert (HuΞΘ : uniq (Ξ ++ Θ0)).
    { apply uniq_app_4; [ assumption | assumption | ].
      unfold disjoint. intros y Hy.
      assert (Hy1 : y `in` dom Ξ) by (clear - Hy; fsetdec).
      assert (Hy2 : y `in` dom Θ0) by (clear - Hy; fsetdec).
      clear - Hy1 Hy2 HfrΞ Hdc Hcov. fsetdec. }
    assert (HcovP1 : ftvar_in_pskl P1 [<=] S1)
      by (clear - Hout Hop Hcov Hg1; fsetdec).
    assert (Hcov2 : ftvar_in_aenv (Ξ ++ Θ0) ∪ ftvar_in_pskl P0
                      ∪ ftvar_in_pskl (open_pskl_wrt_pskl P P1) [<=] S1).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P P1) as H2.
      rewrite ftvar_in_aenv_app.
      clear - H2 HcovP1 HinΞ HftΞ Hcov Hg1. fsetdec. }
    destruct (IH HuΞΘ Hcov2) as [Hsa [Hu1 [Hcv1 Hq1]]].
    repeat split; [ | assumption | assumption | assumption ].
    apply a_sub__forall_l with (α := α) (Ξ := Ξ) (P1 := P1); try assumption.
    clear - Hnα Hcov. fsetdec.

  -
    intros S M Θ0 P0 Hne Hu Hcov.
    repeat split; [ apply a_sub__ghost; exact Hne | assumption
                  | clear - Hcov; fsetdec | clear - Hcov; fsetdec ].

  -
    intros S0 S1 M Θ0 Θ1 P0 P Q Hne Hs IH Hu Hcov.
    simpl in Hcov.
    destruct (IH Hu ltac:(clear - Hcov; fsetdec)) as [Hsa [Hu1 [Hcv1 Hq1]]].
    repeat split; [ apply a_sub__univ_ghost_l; assumption | assumption
                  | assumption | assumption ].

  -
    intros S0 S1 NM M P0 Θ0 Θ1 Ξ α0 α β Q Hnα Hnβ Hs IH Hu Hcov.
    pose proof (dom_subset_ftvar_in_aenv (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0))
      as Hdc.
    assert (HdomS : dom (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0) [<=] S0)
      by (clear - Hdc Hcov; fsetdec).
    assert (Hne : α <> β)
      by (intro Heq; subst; clear - Hnβ; fsetdec).
    assert (Hαd' : α `notin` dom (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0))
      by (clear - HdomS Hnα; fsetdec).
    assert (Hβd' : β `notin` dom (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0))
      by (clear - HdomS Hnβ; fsetdec).
    assert (Hαd : α `notin` add α0 (dom (Ξ ++ Θ0)))
      by (clear - Hαd'; env_simp; fsetdec).
    assert (Hβd : β `notin` add α0 (dom (Ξ ++ Θ0)))
      by (clear - Hβd'; env_simp; fsetdec).
    assert (Hu' : uniq (Ξ ++ (α0 ~ abind_flex_mono_def
                                 (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
                          ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono)
                          ++ Θ0)).
    { clear - Hu Hαd' Hβd' Hne. uniq_env. }
    assert (Hcov' : ftvar_in_aenv
                      (Ξ ++ (α0 ~ abind_flex_mono_def
                                   (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
                         ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono)
                         ++ Θ0)
                    ∪ ftvar_in_pskl P0
                    ∪ ftvar_in_pskl (pskl_arrow (pskl_var_f α) (pskl_var_f β))
                    [<=] add β (add α S0))
      by (clear - Hcov; env_simp; simpl in *; fsetdec).
    destruct (IH Hu' Hcov') as [Hsa [Hu1 [Hcv1 Hq1]]].
    repeat split; [ | assumption | assumption | assumption ].
    apply a_sub_flex__solve with (α := α) (β := β); assumption.

  -
    intros S0 S1 NM M P0 Θ0 Θ1 Ξ α β τ Q Hs IH Hu Hcov.
    assert (HuΞΘ : uniq (Ξ ++ Θ0)) by (clear - Hu; simpl_env in *; solve_uniq).
    assert (Hβd : β `notin` dom (Ξ ++ Θ0))
      by (clear - Hu; simpl_env in *; solve_uniq).
    assert (HβS : β `in` S0) by (clear - Hcov; env_simp; fsetdec).
    assert (HαS : α `in` S0) by (clear - Hcov; fsetdec).
    assert (Hτ : ftvar_in_ptyp τ [<=] S0) by (clear - Hcov; env_simp; fsetdec).
    assert (HcovΞΘ : ftvar_in_aenv (Ξ ++ Θ0) [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    assert (HcovP0 : ftvar_in_pskl P0 [<=] S0) by (clear - Hcov; fsetdec).
    assert (Hcov' : ftvar_in_aenv (Ξ ++ Θ0)
              ∪ ftvar_in_pskl (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0)
              ∪ ftvar_in_pskl
                  (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α))
              [<=] S0).
    { apply subst_pskl_preserves_cover. rewrite ftvar_ptyp_to_pskl. simpl.
      clear - Hτ HcovΞΘ HcovP0 HαS. fsetdec. }
    destruct (IH HuΞΘ Hcov') as [Hsa [Hu1 [Hcv1 Hq1]]].
    pose proof (e_sub_supply_grows Hs) as Hgrow.
    assert (Hβ1 : β `notin` dom Θ1).
    { pose proof (e_sub_dom_upper Hs) as Hdu. clear - Hdu Hβd HβS. fsetdec. }
    repeat split.
    + apply a_sub_flex__assign; assumption.
    + apply uniq_push; assumption.
    + clear - Hcv1 HβS Hτ Hgrow. env_simp. fsetdec.
    + assumption.

  -
    intros S0 S1 NM M P0 Θ0 Θ1 Ξ α β Q Hne Hin Hf IH Hu Hcov.
    assert (Hu' : uniq ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0))
      by (clear - Hu; simpl_env in *; solve_uniq).
    assert (Hcov' : add α (ftvar_in_aenv ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0)
                             ∪ ftvar_in_pskl P0) [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    destruct (IH Hu' Hcov') as [Hfa [Hu1 [Hcv1 Hq1]]].
    repeat split; [ apply a_sub_flex__depend | | | ]; assumption.

  -
    intros S0 S1 NM M P0 Θ0 Θ1 Ξ α β Q Hne Hnin Hf IH Hu Hcov.
    assert (Hu' : uniq (Ξ ++ Θ0)) by (clear - Hu; simpl_env in *; solve_uniq).
    assert (Hβd : β `notin` dom (Ξ ++ Θ0))
      by (clear - Hu; simpl_env in *; solve_uniq).
    assert (HβS : β `in` S0) by (clear - Hcov; env_simp; fsetdec).
    assert (Hcov' : add α (ftvar_in_aenv (Ξ ++ Θ0) ∪ ftvar_in_pskl P0) [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    destruct (IH Hu' Hcov') as [Hfa [Hu1 [Hcv1 Hq1]]].
    pose proof (e_sub_flex_supply_grows Hf) as Hgrow.
    assert (Hβ1 : β `notin` dom Θ1).
    { pose proof (e_sub_flex_dom_upper Hf) as Hdu.
      clear - Hdu Hβd HβS. fsetdec. }
    repeat split.
    + apply a_sub_flex__skip; assumption.
    + apply uniq_push; assumption.
    + clear - Hcv1 HβS Hgrow. env_simp. fsetdec.
    + assumption.

  -
    intros S0 S1 NM M P0 Θ0 Θ1 Ξ α β Q Hne Hnin Hf IH Hu Hcov.
    assert (Hu' : uniq (Ξ ++ Θ0)) by (clear - Hu; simpl_env in *; solve_uniq).
    assert (Hβd : β `notin` dom (Ξ ++ Θ0))
      by (clear - Hu; simpl_env in *; solve_uniq).
    assert (HβS : β `in` S0) by (clear - Hcov; env_simp; fsetdec).
    assert (Hcov' : add α (ftvar_in_aenv (Ξ ++ Θ0) ∪ ftvar_in_pskl P0) [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    destruct (IH Hu' Hcov') as [Hfa [Hu1 [Hcv1 Hq1]]].
    pose proof (e_sub_flex_supply_grows Hf) as Hgrow.
    assert (Hβ1 : β `notin` dom Θ1).
    { pose proof (e_sub_flex_dom_upper Hf) as Hdu.
      clear - Hdu Hβd HβS. fsetdec. }
    repeat split.
    + apply a_sub_flex__skip_rigid; assumption.
    + apply uniq_push; assumption.
    + clear - Hcv1 HβS Hgrow. env_simp. fsetdec.
    + assumption.

  -
    intros S0 S1 NM M P0 Θ0 Θ1 Ξ α x Apay Q Hf IH Hu Hcov.
    assert (Hu' : uniq (Ξ ++ Θ0)) by (clear - Hu; simpl_env in *; solve_uniq).
    assert (Hxd : x `notin` dom (Ξ ++ Θ0))
      by (clear - Hu; simpl_env in *; solve_uniq).
    assert (HxS : x `in` S0) by (clear - Hcov; env_simp; fsetdec).
    assert (HA : ftvar_in_ptyp Apay [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    assert (Hcov' : add α (ftvar_in_aenv (Ξ ++ Θ0) ∪ ftvar_in_pskl P0) [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    destruct (IH Hu' Hcov') as [Hfa [Hu1 [Hcv1 Hq1]]].
    pose proof (e_sub_flex_supply_grows Hf) as Hgrow.
    assert (Hx1 : x `notin` dom Θ1).
    { pose proof (e_sub_flex_dom_upper Hf) as Hdu.
      clear - Hdu Hxd HxS. fsetdec. }
    repeat split.
    + apply a_sub_flex__skip_tm_var; assumption.
    + apply uniq_push; assumption.
    + clear - Hcv1 HxS HA Hgrow. env_simp. fsetdec.
    + assumption.

  -
    intros S0 S1 NM M P0 Θ0 Θ1 Ξ α x Qpay Q Hf IH Hu Hcov.
    assert (Hu' : uniq (Ξ ++ Θ0)) by (clear - Hu; simpl_env in *; solve_uniq).
    assert (Hxd : x `notin` dom (Ξ ++ Θ0))
      by (clear - Hu; simpl_env in *; solve_uniq).
    assert (HxS : x `in` S0) by (clear - Hcov; env_simp; fsetdec).
    assert (HQ : ftvar_in_pskl Qpay [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    assert (Hcov' : add α (ftvar_in_aenv (Ξ ++ Θ0) ∪ ftvar_in_pskl P0) [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    destruct (IH Hu' Hcov') as [Hfa [Hu1 [Hcv1 Hq1]]].
    pose proof (e_sub_flex_supply_grows Hf) as Hgrow.
    assert (Hx1 : x `notin` dom Θ1).
    { pose proof (e_sub_flex_dom_upper Hf) as Hdu.
      clear - Hdu Hxd HxS. fsetdec. }
    repeat split.
    + apply a_sub_flex__skip_tm_skl; assumption.
    + apply uniq_push; assumption.
    + clear - Hcv1 HxS HQ Hgrow. env_simp. fsetdec.
    + assumption.
Qed.

Corollary e_sub_sound : forall S0 NM M P0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
  uniq Θ0 ->
  ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 ∪ ftvar_in_pskl P [<=] S0 ->
  {{ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}a.
Proof.
  intros. eapply (proj1 e_sub_sub_flex_sound); eassumption.
Qed.

Corollary e_sub_sound_init : forall NM M P0 P Q S1 Θ1,
  {{ (ftvar_in_pskl P0 ∪ ftvar_in_pskl P) ↝ S1
     ⊨ nil ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
  {{ nil ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}a.
Proof.
  intros * He. eapply e_sub_sound; [ exact He | apply uniq_nil | ].
  simpl. fsetdec.
Qed.

Lemma e_consis_empty_swap : forall a b S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ empty | empty | P0 ] P ∼ Q ⊣ Θ1 }}e ->
  forall S0', S0' [=] swap_atoms a b S0 ->
  exists S1', S1' [=] swap_atoms a b S1 /\
    {{ S0' ↝ S1' ⊨ (swap_aenv a b Θ0) ⊢[ empty | empty | (swap_pskl a b P0) ]
       (swap_pskl a b P) ∼ (swap_pskl a b Q) ⊣ (swap_aenv a b Θ1) }}e.
Proof.
  intros a b S0 Θ0 P0 P Q S1 Θ1 Hc S0' Heq.
  eapply e_consis_swap;
    [ exact Hc | apply empty_eq_swap_atoms_empty
    | apply empty_eq_swap_atoms_empty | exact Heq ].
Qed.

Lemma e_consis_chk_swap : forall a b S0 Θ0 A B S1 Θ1,
  e_consis_chk S0 Θ0 A B S1 Θ1 ->
  forall S0', S0' [=] swap_atoms a b S0 ->
  exists S1', S1' [=] swap_atoms a b S1 /\
    e_consis_chk S0' (swap_aenv a b Θ0) (swap_pskl a b A) (swap_pskl a b B)
      S1' (swap_aenv a b Θ1).
Proof.
  intros a b S0 Θ0 A B S1 Θ1 [Q Hc] S0' Heq.
  destruct (e_consis_empty_swap Hc Heq) as [S1' [HS1 Hc']].
  exists S1'. split; [ exact HS1 | exists (swap_pskl a b Q); exact Hc' ].
Qed.

Lemma e_sub_sub_flex_swap : forall a b,
  (forall S0 NM M P0 Θ0 P Q S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
     forall S0', S0' [=] swap_atoms a b S0 ->
     exists S1', S1' [=] swap_atoms a b S1 /\
       {{ S0' ↝ S1' ⊨ (swap_aenv a b Θ0) ⊢[ NM | M | (swap_pskl a b P0) ]
          (swap_pskl a b P) ⩽ (swap_pskl a b Q)
          ⊣ (swap_aenv a b Θ1) }}e) /\
  (forall S0 NM M P0 Θ0 Ξ α Q S1 Θ1,
     e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1 ->
     forall S0', S0' [=] swap_atoms a b S0 ->
     exists S1', S1' [=] swap_atoms a b S1 /\
       e_sub_flex S0' NM M (swap_pskl a b P0) (swap_aenv a b Θ0)
         (swap_aenv a b Ξ) (swap_atom a b α) (swap_pskl a b Q)
         S1' (swap_aenv a b Θ1)).
Proof.
  intros a b.
  apply e_sub_sub_flex_mutind.

  -
    intros S NM P Θ0 S0' Heq. simpl.
    exists S0'. split; [ exact Heq | apply e_sub__infer ].
  -
    intros S0 S1 Θ0 Θ1 A B HgfA HgfB HgdA HgdB Hc S0' Heq. simpl.
    destruct (e_consis_chk_swap Hc Heq) as [S1' [HS1 Hc']].
    exists S1'. split; [ exact HS1 | ].
    apply e_sub__check;
      auto using guarded_pskl_swap, pskl_ghost_free_swap.
  -
    intros α S0 S1 Θ0 Θ1 Ξ A B Hgf Hsuf HuΞΘ Hnα Hs IH S0' Heq. simpl.
    destruct (IH (add (swap_atom a b α) S0')) as [S1' [HS1 Hd]];
      [ apply eq_swap_atoms_add; exact Heq | ].
    exists S1'. split; [ exact HS1 | ].
    apply e_sub__forall_r with (α := swap_atom a b α) (Ξ := swap_aenv a b Ξ).
    + apply pskl_ghost_free_swap; exact Hgf.
    + apply a_suffix_swap; exact Hsuf.
    + rewrite <- swap_aenv_app. apply swap_aenv_uniq; exact HuΞΘ.
    + eapply swap_notin_eq; eassumption.
    + rewrite swap_pskl_open_var in Hd. rewrite !swap_aenv_app in Hd.
      exact Hd.
  -
    intros S Θ0 P Hgd S0' Heq. simpl.
    exists S0'. split; [ exact Heq | ].
    apply e_sub__univ_ghost_r; auto using guarded_pskl_swap.
  -
    intros S0 S1 NM M P0 Θ0 Θ1 α Q Hf IH S0' Heq. simpl.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | apply e_sub__flex_mono; exact Hd ].
  -
    intros S0 S1 S2 NM M Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc Hs IH S0' Heq. simpl.
    destruct (e_consis_empty_swap Hc Heq) as [S1' [HS1 Hc']].
    destruct (IH _ HS1) as [S2' [HS2 Hd]].
    exists S2'. split; [ exact HS2 | ].
    eapply e_sub__arrow; [ exact Hc' | exact Hd ].
  -
    intros α S0 S1 S2 NM M P0 Θ0 Θ1 P Q Ξ P1 Hne Hgd Hnα Hex Hwf Hs IH S0' Heq.
    simpl.
    assert (Heqα : add (swap_atom a b α) S0' [=] swap_atoms a b (add α S0))
      by (apply eq_swap_atoms_add; exact Heq).
    destruct (e_extract_swap Hex Heqα) as [S1' [HS1 Hex']].
    destruct (IH _ HS1) as [S2' [HS2 Hd]].
    exists S2'. split; [ exact HS2 | ].
    eapply e_sub__forall_l with (α := swap_atom a b α)
      (Ξ := swap_aenv a b Ξ) (P1 := swap_pskl a b P1).
    + exact Hne.
    + destruct Hgd as [hg | ->];
        [ left; apply guarded_pskl_swap; exact hg | right; reflexivity ].
    + eapply swap_notin_eq; eassumption.
    + rewrite swap_pskl_open_var in Hex'. exact Hex'.
    + rewrite <- swap_aenv_app.
      apply (a_wf_pskl_swap a b _ _ _ Hwf). apply empty_eq_swap_atoms_empty.
    + rewrite swap_pskl_open in Hd. rewrite swap_aenv_app in Hd. exact Hd.
  -
    intros S M Θ0 P0 Hne S0' Heq. simpl.
    exists S0'. split; [ exact Heq | apply e_sub__ghost; exact Hne ].
  -
    intros S0 S1 M Θ0 Θ1 P0 P Q Hne Hs IH S0' Heq. simpl.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | ].
    apply e_sub__univ_ghost_l; [ exact Hne | exact Hd ].

  -
    intros S0 S1 NM M P0 Θ0 Θ1 Ξ α0 α β Q Hnα Hnβ Hs IH S0' Heq. simpl.
    destruct (IH (add (swap_atom a b β) (add (swap_atom a b α) S0')))
      as [S1' [HS1 Hd]];
      [ apply eq_swap_atoms_add; apply eq_swap_atoms_add; exact Heq | ].
    exists S1'. split; [ exact HS1 | ].
    apply e_sub_flex__solve with (α := swap_atom a b α)
      (β := swap_atom a b β).
    + eapply swap_notin_eq; eassumption.
    + eapply swap_notin_eq;
        [ apply eq_swap_atoms_add; exact Heq | exact Hnβ ].
    + rewrite !swap_aenv_app in Hd. exact Hd.
  -
    intros S0 S1 NM M P0 Θ0 Θ1 Ξ α β τ Q Hs IH S0' Heq. simpl.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | ].
    apply e_sub_flex__assign.
    rewrite !swap_pskl_subst in Hd.
    rewrite !swap_pskl_ptyp_to_pskl in Hd.
    change (swap_pskl a b (pskl_var_f α)) with
      (pskl_var_f (swap_atom a b α)) in Hd.
    rewrite swap_aenv_app in Hd. exact Hd.
  -
    intros S0 S1 NM M P0 Θ0 Θ1 Ξ α β Q Hne Hin Hf IH S0' Heq. simpl.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | ].
    apply e_sub_flex__depend;
      auto using swap_atom_neq, swap_pskl_ftv_in.
    rewrite swap_aenv_app in Hd. exact Hd.
  -
    intros S0 S1 NM M P0 Θ0 Θ1 Ξ α β Q Hne Hni Hf IH S0' Heq. simpl.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | ].
    apply e_sub_flex__skip;
      auto using swap_atom_neq, swap_pskl_ftv_notin.
  -
    intros S0 S1 NM M P0 Θ0 Θ1 Ξ α β Q Hne Hni Hf IH S0' Heq. simpl.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | ].
    apply e_sub_flex__skip_rigid;
      auto using swap_atom_neq, swap_pskl_ftv_notin.
  -
    intros S0 S1 NM M P0 Θ0 Θ1 Ξ α x Apay Q Hf IH S0' Heq. simpl.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | apply e_sub_flex__skip_tm_var; exact Hd ].
  -
    intros S0 S1 NM M P0 Θ0 Θ1 Ξ α x Qpay Q Hf IH S0' Heq. simpl.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | apply e_sub_flex__skip_tm_skl; exact Hd ].
Qed.

Lemma e_sub_sub_flex_supply_respect :
  (forall S0 NM M P0 Θ0 P Q S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
     forall S0', S0' [=] S0 ->
     exists S1', S1' [=] S1 /\
       {{ S0' ↝ S1' ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e) /\
  (forall S0 NM M P0 Θ0 Ξ α Q S1 Θ1,
     e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1 ->
     forall S0', S0' [=] S0 ->
     exists S1', S1' [=] S1 /\
       e_sub_flex S0' NM M P0 Θ0 Ξ α Q S1' Θ1).
Proof.
  destruct (atom_fresh empty) as [a _].
  pose proof (@e_sub_sub_flex_swap a a) as Hswap.
  setoid_rewrite swap_aenv_same in Hswap.
  setoid_rewrite swap_pskl_same in Hswap.
  setoid_rewrite swap_atom_same in Hswap.
  setoid_rewrite swap_atoms_same in Hswap.
  exact Hswap.
Qed.

Corollary e_sub_supply_respect : forall S0 NM M P0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
  forall S0', S0' [=] S0 ->
  exists S1', S1' [=] S1 /\
    {{ S0' ↝ S1' ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e.
Proof. apply e_sub_sub_flex_supply_respect. Qed.

Corollary e_sub_swap : forall a b S0 NM M P0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
  forall S0', S0' [=] swap_atoms a b S0 ->
  exists S1', S1' [=] swap_atoms a b S1 /\
    {{ S0' ↝ S1' ⊨ (swap_aenv a b Θ0) ⊢[ NM | M | (swap_pskl a b P0) ]
       (swap_pskl a b P) ⩽ (swap_pskl a b Q) ⊣ (swap_aenv a b Θ1) }}e.
Proof. intros a b. apply e_sub_sub_flex_swap. Qed.
