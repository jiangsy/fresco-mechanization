Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.prop_tag.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.basic.def_supply.
Require Import src.fresco.ext_algo.basic.def_guess.
Require Import src.fresco.ext_algo.basic.prop_guess.
Require Import src.fresco.ext_algo.consistency.def_consis.

Set Implicit Arguments.

Lemma subst_pskl_preserves_cover : forall P Q R α V S,
  V ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q ∪ ftvar_in_pskl R [<=] S ->
  V ∪ ftvar_in_pskl (subst_pskl_in_pskl R α P)
    ∪ ftvar_in_pskl (subst_pskl_in_pskl R α Q) [<=] S.
Proof.
  intros P Q R α V S Hcov x Hx. apply Hcov.
  repeat rewrite union_iff in Hx |- *.
  destruct Hx as [Hx | [Hx | Hx]]; [ tauto | | ].
  - apply (ftvar_in_pskl_subst_pskl_in_pskl_upper P R α) in Hx.
    clear - Hx. fsetdec.
  - apply (ftvar_in_pskl_subst_pskl_in_pskl_upper Q R α) in Hx.
    clear - Hx. fsetdec.
Qed.

Open Scope fresco_e_scope.

Lemma e_assign_unify_consis_supply_grows :
  (forall S0 Θ0 Ξ α P S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e -> S0 [<=] S1) /\
  (forall S0 Θ0 α β S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}e -> S0 [<=] S1) /\
  (forall Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}e -> S0 [<=] S1).
Proof.
  apply e_assign_unify_consis_mutind;
    intros;
    try (match goal with
         | Hg : e_guess_mono _ _ _ _ _ |- _ =>
             exact (e_guess_mono_supply_grows Hg)
         end);
    fsetdec.
Qed.

Corollary e_assign_supply_grows : forall S0 Θ0 Ξ α P S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e -> S0 [<=] S1.
Proof. apply e_assign_unify_consis_supply_grows. Qed.

Corollary e_unify_supply_grows : forall S0 Θ0 α β S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}e -> S0 [<=] S1.
Proof. apply e_assign_unify_consis_supply_grows. Qed.

Corollary e_consis_supply_grows : forall Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}e -> S0 [<=] S1.
Proof. apply e_assign_unify_consis_supply_grows. Qed.

#[local] Ltac supply_grow_facts :=
  repeat match goal with
  | H : e_assign ?S0 _ _ _ _ ?S1 _ |- _ =>
      lazymatch goal with
      | _ : S0 [<=] S1 |- _ => fail
      | _ => pose proof (e_assign_supply_grows H)
      end
  | H : e_unify ?S0 _ _ _ ?S1 _ |- _ =>
      lazymatch goal with
      | _ : S0 [<=] S1 |- _ => fail
      | _ => pose proof (e_unify_supply_grows H)
      end
  | H : e_consis _ _ ?S0 _ _ _ _ ?S1 _ |- _ =>
      lazymatch goal with
      | _ : S0 [<=] S1 |- _ => fail
      | _ => pose proof (e_consis_supply_grows H)
      end
  end.

Lemma e_assign_unify_consis_dom_upper :
  (forall S0 Θ0 Ξ α P S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
     dom Θ1 [<=] dom (Ξ ++ Θ0) ∪ (S1 ∖ S0)) /\
  (forall S0 Θ0 α β S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}e ->
     dom Θ1 [<=] dom Θ0 ∪ (S1 ∖ S0)) /\
  (forall Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}e ->
     dom Θ1 [<=] dom Θ0 ∪ (S1 ∖ S0)).
Proof.
  apply e_assign_unify_consis_mutind;
    intros; supply_grow_facts;
    try solve [ simpl_env in *; repeat rewrite dom_app in *;
                simpl dom in *; fsetdec ].
  match goal with Hg : e_guess_mono _ _ _ _ _ |- _ =>
    pose proof (e_guess_mono_generated_in_supply Hg) as Hin;
    pose proof (@e_guess_mono_generated_fresh _ _ _ _ _ Hg) as Hfr
  end.
  assert (Hblock : dom βs [<=] S1 ∖ S0).
  { intros γ Hγ.
    assert (Hin1 : γ `in` S1) by (clear - Hin Hγ; fsetdec).
    pose proof (Hfr γ Hγ) as Hout. clear - Hin1 Hout. fsetdec. }
  repeat rewrite dom_app. simpl dom. clear - Hblock. fsetdec.
Qed.

#[local] Ltac sgf_ctx :=
  repeat match goal with
  | H : e_assign ?S0 _ _ _ _ ?S1 _ |- _ =>
      lazymatch goal with
      | _ : S0 [<=] S1 |- _ => fail
      | _ => pose proof (e_assign_supply_grows H)
      end
  | H : e_unify ?S0 _ _ _ ?S1 _ |- _ =>
      lazymatch goal with
      | _ : S0 [<=] S1 |- _ => fail
      | _ => pose proof (e_unify_supply_grows H)
      end
  | H : e_consis _ _ ?S0 _ _ _ _ ?S1 _ |- _ =>
      lazymatch goal with
      | _ : S0 [<=] S1 |- _ => fail
      | _ => pose proof (e_consis_supply_grows H)
      end
  | H : e_guess_mono ?S0 _ ?S1 _ _ |- _ =>
      lazymatch goal with
      | _ : S0 [<=] S1 |- _ => fail
      | _ => pose proof (e_guess_mono_supply_grows H)
      end
  end.

Lemma e_assign_unify_consis_ctx_ftvar :
  (forall S0 Θ0 Ξ α P S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
     ftvar_in_aenv (Ξ ++ Θ0) ∪ ftvar_in_pskl P [<=] S0 ->
     ftvar_in_aenv Θ1 [<=] S1) /\
  (forall S0 Θ0 α β S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}e ->
     ftvar_in_aenv Θ0 [<=] S0 ->
     ftvar_in_aenv Θ1 [<=] S1) /\
  (forall Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}e ->
     ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 ∪ ftvar_in_pskl P [<=] S0 ->
     ftvar_in_aenv Θ1 [<=] S1).
Proof.
  apply e_assign_unify_consis_mutind;
    intros; sgf_ctx;
    repeat rewrite ftvar_in_aenv_app in *; simpl in *;
    try solve [ clear - H; fsetdec ]; try solve [ fsetdec ].

  all: try (match goal with
            | IH : _ -> ftvar_in_aenv ?Θ [<=] ?S |- _ =>
                let Hih := fresh "Hih" in
                assert (Hih : ftvar_in_aenv Θ [<=] S)
                  by (apply IH; repeat rewrite ftvar_in_aenv_app; simpl;
                      fsetdec)
            end; fsetdec).

  { match goal with
    | Hg : e_guess_mono _ _ _ _ _ |- _ =>
        pose proof (e_guess_mono_ftv Hg) as Hgf;
        pose proof (e_guess_mono_generated_in_supply Hg) as Hgd;
        pose proof (e_guess_mono_generated_ftvar Hg) as Hgv
    end.
    fsetdec. }

  { match goal with | Hc : _ [<=] S0 |- _ => rename Hc into Hcov0 end.
    assert (Hτ : ftvar_in_ptyp τ [<=] S0) by (clear - Hcov0; fsetdec).
    assert (HP : ftvar_in_pskl P [<=] S0) by (clear - Hcov0; fsetdec).
    assert (Hα : singleton α [<=] S0).
    { match goal with
      | Hf : a_flex_tvar ?Θ α |- _ =>
          pose proof (a_flex_tvar_in_dom Hf) as Hd;
          pose proof (dom_subset_ftvar_in_aenv Θ) as Hds
      end. simpl in *. clear - Hcov0 Hd Hds. fsetdec. }
    assert (HΘ : ftvar_in_aenv Ξ ∪ ftvar_in_aenv Θ0 [<=] S0)
      by (clear - Hcov0; fsetdec).
    match goal with
    | IH : _ -> ftvar_in_aenv ?Θ [<=] ?S |- _ =>
        assert (Hih : ftvar_in_aenv Θ [<=] S)
    end.
    { match goal with
      | IH : _ -> ftvar_in_aenv _ [<=] _ |- _ => apply IH
      end.
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P (ptyp_to_pskl τ) β)
        as Hu1.
      rewrite ftvar_ptyp_to_pskl in Hu1.
      assert (Hs1 : ftvar_in_pskl (subst_pskl_in_pskl (ptyp_to_pskl τ) β P)
                    [<=] S0) by (clear - Hu1 HP Hτ; fsetdec).
      match goal with
      | |- context [ if ?X then _ else _ ] => destruct X
      end.
      - rewrite ftvar_ptyp_to_pskl. clear - HΘ Hs1 Hτ. fsetdec.
      - simpl. clear - HΘ Hs1 Hα. fsetdec. }
    assert (Hhd : add β (ftvar_in_ptyp τ) [<=] S0) by (clear - Hcov0; fsetdec).
    match goal with | Hg : S0 [<=] S1 |- _ => rename Hg into Hgr end.
    clear - Hih Hhd Hgr. fsetdec. }

  { match goal with | Hc : _ [<=] ?S |- _ [<=] ?S => rename Hc into Hcov0 end.
    match goal with
    | Hf : a_flex_tvar ?Θ ?y |- _ =>
        pose proof (a_flex_tvar_in_dom Hf) as Hd;
        pose proof (dom_subset_ftvar_in_aenv Θ) as Hds
    end. clear - Hcov0 Hd Hds. fsetdec. }
  { match goal with | Hc : _ [<=] ?S |- _ [<=] ?S => rename Hc into Hcov0 end.
    match goal with
    | Hf : a_flex_tvar ?Θ ?y |- _ =>
        pose proof (a_flex_tvar_in_dom Hf) as Hd;
        pose proof (dom_subset_ftvar_in_aenv Θ) as Hds
    end. clear - Hcov0 Hd Hds. fsetdec. }

  { match goal with | Hc : _ [<=] S0 |- _ => rename Hc into Hcov0 end.
    assert (Hτ : ftvar_in_ptyp τ [<=] S0) by (clear - Hcov0; fsetdec).
    assert (HΘ : ftvar_in_aenv Θ0 [<=] S0) by (clear - Hcov0; fsetdec).
    assert (Hd0 : add α1 (dom Θ0) [<=] S0).
    { pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
      clear - Hcov0 Hds. fsetdec. }
    assert (Hab : singleton α ∪ singleton β [<=] S0).
    { match goal with
      | Hfa : a_flex_tvar ?Θ α, Hfb : a_flex_tvar ?Θ β |- _ =>
          pose proof (a_flex_tvar_in_dom Hfa) as Hda;
          pose proof (a_flex_tvar_in_dom Hfb) as Hdb
      end. simpl in Hda, Hdb. clear - Hd0 Hda Hdb. fsetdec. }
    match goal with
    | IH : _ -> ftvar_in_aenv ?Θ [<=] ?S |- _ =>
        assert (Hih : ftvar_in_aenv Θ [<=] S)
    end.
    { match goal with
      | IH : _ -> ftvar_in_aenv _ [<=] _ |- _ => apply IH
      end.
      repeat rewrite ftvar_ptyp_to_pskl.
      repeat match goal with
      | |- context [ if ?X then _ else _ ] => destruct X
      end; simpl; clear - HΘ Hτ Hab; fsetdec. }
    assert (Hhd : add α1 (ftvar_in_ptyp τ) [<=] S0) by (clear - Hcov0; fsetdec).
    match goal with | Hg : S0 [<=] S1 |- _ => rename Hg into Hgr end.
    clear - Hih Hhd Hgr. fsetdec. }

  { match goal with
    | IH1 : _ -> ftvar_in_aenv ?Θa [<=] ?Sa,
      IH2 : _ -> ftvar_in_aenv ?Θb [<=] ?Sb |- _ =>
        let H1 := fresh "Hih1" in
        assert (H1 : ftvar_in_aenv Θa [<=] Sa) by (apply IH1; fsetdec);
        apply IH2; fsetdec
    end. }

  all: match goal with
       | IH : ?A -> ?C |- _ =>
           let Hih := fresh "Hih" in
           assert (Hih : C);
           [ apply IH;
             repeat match goal with
             | |- context [ open_pskl_wrt_pskl ?B (pskl_var_f ?a) ] =>
                 lazymatch goal with
                 | _ : ftvar_in_pskl (open_pskl_wrt_pskl B (pskl_var_f a))
                       [<=] _ |- _ => fail
                 | _ => pose proof
                          (ftvar_in_pskl_open_pskl_wrt_pskl_upper B
                             (pskl_var_f a))
                 end
             end;
             simpl in *; fsetdec
           | clear - Hih; simpl in Hih; fsetdec ]
       end.
Qed.

Ltac env_simp :=
  simpl_env in *;
  repeat (rewrite ftvar_in_aenv_app in * );
  repeat (rewrite dom_app in * );
  simpl ftvar_in_aenv in *; simpl dom in *; simpl_env in *.

Lemma e_assign_unify_consis_sound :
  (forall S0 Θ0 Ξ α P S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
     uniq (Ξ ++ Θ0) ->
     ftvar_in_aenv (Ξ ++ Θ0) ∪ ftvar_in_pskl P [<=] S0 ->
     {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a /\ uniq Θ1 /\ ftvar_in_aenv Θ1 [<=] S1) /\
  (forall S0 Θ0 α β S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}e ->
     uniq Θ0 ->
     ftvar_in_aenv Θ0 [<=] S0 ->
     {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a /\ uniq Θ1 /\ ftvar_in_aenv Θ1 [<=] S1) /\
  (forall Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}e ->
     uniq Θ0 ->
     ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 ∪ ftvar_in_pskl P
       ∪ Δ1 ∪ Δ2 [<=] S0 ->
     {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}a
     /\ uniq Θ1 /\ ftvar_in_aenv Θ1 [<=] S1).
Proof.
  apply e_assign_unify_consis_mutind.

  -
    intros S Θ0 α Hu Hcov.
    repeat split;
      [ apply a_assign__univ_ghost_id
      | clear - Hu; solve_uniq
      | clear - Hcov; env_simp; fsetdec ].

  -
    intros S0 S1 Θ0 Ξ α P βs τ Hnα Hg Hm Hu Hcov.
    pose proof (e_guess_mono_uniq Hg) as Hubs.
    pose proof (e_guess_mono_generated_in_supply Hg) as Hbin.
    pose proof (@e_guess_mono_generated_fresh _ _ _ _ _ Hg) as Hbfr.
    pose proof (e_guess_mono_supply_grows Hg) as Hgrow.
    pose proof (dom_subset_ftvar_in_aenv (Ξ ++ (α ~ abind_flex_mono) ++ Θ0))
      as Hdcov.
    assert (HcovΘ : ftvar_in_aenv Θ0 [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    assert (HcovP : ftvar_in_pskl P [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    assert (Hga : a_guess_mono Θ0 P βs τ)
      by (eapply e_guess_mono_sound; eauto).
    assert (HdomS : dom (Ξ ++ (α ~ abind_flex_mono) ++ Θ0) [<=] S0)
      by (clear - Hcov Hdcov; fsetdec).
    assert (Hfilter : forall α1, α1 `in` dom βs ->
                      α1 `notin` add α (dom (Ξ ++ Θ0))).
    { intros α1 Hα1. pose proof (Hbfr α1 Hα1) as Hout.
      clear - Hout HdomS. env_simp. fsetdec. }
    pose proof (a_guess_mono_generated_ftvar Hga) as Hbftv.
    pose proof (a_guess_mono_ftv Hga) as Hτ.
    assert (HuΞΘ : uniq (Ξ ++ Θ0)) by (clear - Hu; solve_uniq).
    assert (Hαdom : α `notin` dom (Ξ ++ Θ0)) by (clear - Hu; solve_uniq).
    assert (HαS : α `in` S0) by (clear - HdomS; env_simp; fsetdec).
    repeat split.
    + apply a_assign__solve_m; assumption.
    + apply uniq_push.
      * apply uniq_app_4; [ assumption | assumption | ].
        unfold disjoint. intros y Hy.
        assert (Hy1 : y `in` dom βs) by (clear - Hy; fsetdec).
        assert (Hy2 : y `in` dom (Ξ ++ Θ0)) by (clear - Hy; fsetdec).
        pose proof (Hfilter y Hy1) as Hd. clear - Hd Hy2. fsetdec.
      * assert (Hαβs : α `notin` dom βs).
        { intros Hin. pose proof (Hbfr α Hin) as Hc. clear - Hc HαS.
          contradiction. }
        clear - Hαdom Hαβs. env_simp. fsetdec.
    + assert (HcovΞΘ : ftvar_in_aenv (Ξ ++ Θ0) [<=] S0)
        by (clear - Hcov; env_simp; fsetdec).
      clear - HαS HcovΞΘ Hbin Hbftv Hτ HcovP Hgrow. env_simp. fsetdec.

  -
    intros S0 S1 Θ0 Θ1 Ξ α β τ P Q Hf Hc IH Hu Hcov.
    assert (HuΞΘ : uniq (Ξ ++ Θ0)) by (clear - Hu; solve_uniq).
    assert (Hβdom : β `notin` dom (Ξ ++ Θ0)) by (clear - Hu; solve_uniq).
    assert (HβS : β `in` S0) by (clear - Hcov; env_simp; fsetdec).
    assert (Hτcov : ftvar_in_ptyp τ [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    assert (HcovΞΘ : ftvar_in_aenv (Ξ ++ Θ0) [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    assert (HcovP : ftvar_in_pskl P [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    assert (HαS : α `in` S0).
    { pose proof (a_flex_tvar_in_dom Hf) as Hd.
      pose proof (dom_subset_ftvar_in_aenv
                    ((β ~ abind_flex_mono_def τ) ++ Θ0)) as He.
      clear - Hd He Hcov. env_simp. fsetdec. }
    assert (Hsub : ftvar_in_aenv (Ξ ++ Θ0)
              ∪ ftvar_in_pskl (subst_pskl_in_pskl (ptyp_to_pskl τ) β P)
              ∪ ftvar_in_pskl
                  (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α))
              ∪ empty ∪ empty [<=] S0).
    { repeat rewrite (empty_union_2 (s := empty)) by (unfold Empty; clear; fsetdec).
      apply subst_pskl_preserves_cover.
      rewrite ftvar_ptyp_to_pskl. simpl.
      clear - Hτcov HcovΞΘ HcovP HαS. fsetdec. }
    destruct (IH HuΞΘ Hsub) as [Hca [Hu1 Hcov1]].
    pose proof (e_consis_supply_grows Hc) as Hgrow.
    assert (Hβ1 : β `notin` dom Θ1).
    { pose proof ((proj2 (proj2 e_assign_unify_consis_dom_upper)) _ _ _ _ _ _ _ _ _ Hc)
        as Hdu. clear - Hdu Hβdom HβS. fsetdec. }
    repeat split.
    + apply a_assign__assign with (Q := Q); assumption.
    + apply uniq_push; assumption.
    + clear - Hcov1 HβS Hτcov Hgrow. env_simp. fsetdec.

  -
    intros S0 S1 Θ0 Θ1 Ξ α β P Hne Hin Ha IH Hu Hcov.
    assert (Hu' : uniq ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0))
      by (clear - Hu; simpl_env in *; solve_uniq).
    assert (Hcov' : ftvar_in_aenv ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0)
                      ∪ ftvar_in_pskl P [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    destruct (IH Hu' Hcov') as [Hca [Hu1 Hcov1]].
    repeat split; [ apply a_assign__depend | | ]; assumption.

  -
    intros S0 S1 Θ0 Θ1 Ξ α β P Hne Hnb Ha IH Hu Hcov.
    assert (Hu' : uniq (Ξ ++ Θ0)) by (clear - Hu; solve_uniq).
    assert (Hβdom : β `notin` dom (Ξ ++ Θ0)) by (clear - Hu; solve_uniq).
    assert (HβS : β `in` S0) by (clear - Hcov; env_simp; fsetdec).
    assert (Hcov' : ftvar_in_aenv (Ξ ++ Θ0) ∪ ftvar_in_pskl P [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    destruct (IH Hu' Hcov') as [Hca [Hu1 Hcov1]].
    pose proof (e_assign_supply_grows Ha) as Hgrow.
    assert (Hβ1 : β `notin` dom Θ1).
    { pose proof ((proj1 e_assign_unify_consis_dom_upper) _ _ _ _ _ _ _ Ha)
        as Hdu. clear - Hdu Hβdom HβS. fsetdec. }
    repeat split.
    + apply a_assign__skip; assumption.
    + apply uniq_push; assumption.
    + clear - Hcov1 HβS Hgrow. env_simp. fsetdec.

  -
    intros S0 S1 Θ0 Θ1 Ξ α β P Hnb Ha IH Hu Hcov.
    assert (Hu' : uniq (Ξ ++ Θ0)) by (clear - Hu; solve_uniq).
    assert (Hβdom : β `notin` dom (Ξ ++ Θ0)) by (clear - Hu; solve_uniq).
    assert (HβS : β `in` S0) by (clear - Hcov; env_simp; fsetdec).
    assert (Hcov' : ftvar_in_aenv (Ξ ++ Θ0) ∪ ftvar_in_pskl P [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    destruct (IH Hu' Hcov') as [Hca [Hu1 Hcov1]].
    pose proof (e_assign_supply_grows Ha) as Hgrow.
    assert (Hβ1 : β `notin` dom Θ1).
    { pose proof ((proj1 e_assign_unify_consis_dom_upper) _ _ _ _ _ _ _ Ha)
        as Hdu. clear - Hdu Hβdom HβS. fsetdec. }
    repeat split.
    + apply a_assign__skip_rigid; assumption.
    + apply uniq_push; assumption.
    + clear - Hcov1 HβS Hgrow. env_simp. fsetdec.

  -
    intros S0 S1 Θ0 Θ1 Ξ α x A P Ha IH Hu Hcov.
    assert (Hu' : uniq (Ξ ++ Θ0)) by (clear - Hu; solve_uniq).
    assert (Hxdom : x `notin` dom (Ξ ++ Θ0)) by (clear - Hu; solve_uniq).
    assert (HxS : x `in` S0) by (clear - Hcov; env_simp; fsetdec).
    assert (HAcov : ftvar_in_ptyp A [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    assert (Hcov' : ftvar_in_aenv (Ξ ++ Θ0) ∪ ftvar_in_pskl P [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    destruct (IH Hu' Hcov') as [Hca [Hu1 Hcov1]].
    pose proof (e_assign_supply_grows Ha) as Hgrow.
    assert (Hx1 : x `notin` dom Θ1).
    { pose proof ((proj1 e_assign_unify_consis_dom_upper) _ _ _ _ _ _ _ Ha)
        as Hdu. clear - Hdu Hxdom HxS. fsetdec. }
    repeat split.
    + apply a_assign__skip_tm_var; assumption.
    + apply uniq_push; assumption.
    + clear - Hcov1 HxS HAcov Hgrow. env_simp. fsetdec.

  -
    intros S0 S1 Θ0 Θ1 Ξ α x Q P Ha IH Hu Hcov.
    assert (Hu' : uniq (Ξ ++ Θ0)) by (clear - Hu; solve_uniq).
    assert (Hxdom : x `notin` dom (Ξ ++ Θ0)) by (clear - Hu; solve_uniq).
    assert (HxS : x `in` S0) by (clear - Hcov; env_simp; fsetdec).
    assert (HQcov : ftvar_in_pskl Q [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    assert (Hcov' : ftvar_in_aenv (Ξ ++ Θ0) ∪ ftvar_in_pskl P [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    destruct (IH Hu' Hcov') as [Hca [Hu1 Hcov1]].
    pose proof (e_assign_supply_grows Ha) as Hgrow.
    assert (Hx1 : x `notin` dom Θ1).
    { pose proof ((proj1 e_assign_unify_consis_dom_upper) _ _ _ _ _ _ _ Ha)
        as Hdu. clear - Hdu Hxdom HxS. fsetdec. }
    repeat split.
    + apply a_assign__skip_tm_skl; assumption.
    + apply uniq_push; assumption.
    + clear - Hcov1 HxS HQcov Hgrow. env_simp. fsetdec.

  -
    intros S Θ0 α Hf Hu Hcov.
    repeat split; [ apply a_unify__flex_id | | ]; assumption.

  -
    intros S Θ0 α β Hne Hf Hu Hcov.
    assert (HβS : β `in` S).
    { pose proof (a_flex_tvar_in_dom Hf) as Hd.
      pose proof (dom_subset_ftvar_in_aenv Θ0) as He.
      clear - Hd He Hcov. env_simp. fsetdec. }
    repeat split.
    + apply a_unify__flex_l; assumption.
    + clear - Hu; solve_uniq.
    + clear - Hcov HβS. env_simp. fsetdec.

  -
    intros S Θ0 α β Hne Hf Hu Hcov.
    assert (HαS : α `in` S).
    { pose proof (a_flex_tvar_in_dom Hf) as Hd.
      pose proof (dom_subset_ftvar_in_aenv Θ0) as He.
      clear - Hd He Hcov. env_simp. fsetdec. }
    repeat split.
    + apply a_unify__flex_r; assumption.
    + clear - Hu; solve_uniq.
    + clear - Hcov HαS. env_simp. fsetdec.

  -
    intros S0 S1 Θ0 Θ1 α1 τ α β Q Hfα Hfβ Hc IH Hu Hcov.
    assert (Hu' : uniq Θ0) by (clear - Hu; solve_uniq).
    assert (H1dom : α1 `notin` dom Θ0) by (clear - Hu; solve_uniq).
    assert (H1S : α1 `in` S0) by (clear - Hcov; env_simp; fsetdec).
    assert (Hτcov : ftvar_in_ptyp τ [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    assert (HcovΘ : ftvar_in_aenv Θ0 [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    pose proof (dom_subset_ftvar_in_aenv ((α1 ~ abind_flex_mono_def τ) ++ Θ0))
      as Hdc.
    assert (HαS : α `in` S0).
    { pose proof (a_flex_tvar_in_dom Hfα) as Hd. clear - Hd Hdc Hcov. fsetdec. }
    assert (HβS : β `in` S0).
    { pose proof (a_flex_tvar_in_dom Hfβ) as Hd. clear - Hd Hdc Hcov. fsetdec. }
    assert (Hsub : ftvar_in_aenv Θ0
              ∪ ftvar_in_pskl (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f β)))
              ∪ ftvar_in_pskl (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f α)))
              ∪ empty ∪ empty [<=] S0).
    { repeat rewrite (empty_union_2 (s := empty)) by (unfold Empty; clear; fsetdec).
      repeat rewrite ptyp_to_pskl_subst.
      apply subst_pskl_preserves_cover. repeat rewrite ftvar_ptyp_to_pskl. simpl.
      clear - Hτcov HcovΘ HαS HβS. fsetdec. }
    destruct (IH Hu' Hsub) as [Hca [Hu1 Hcv1]].
    pose proof (e_consis_supply_grows Hc) as Hgrow.
    assert (H11 : α1 `notin` dom Θ1).
    { pose proof ((proj2 (proj2 e_assign_unify_consis_dom_upper))
                    _ _ _ _ _ _ _ _ _ Hc) as Hdu.
      clear - Hdu H1dom H1S. fsetdec. }
    repeat split.
    + apply a_unify__flex_assign with (Q := Q); assumption.
    + apply uniq_push; assumption.
    + clear - Hcv1 H1S Hτcov Hgrow. env_simp. fsetdec.

  -
    intros S0 S1 Θ0 Θ1 α1 α β Hn1 Hn2 Hun IH Hu Hcov.
    assert (Hu' : uniq Θ0) by (clear - Hu; solve_uniq).
    assert (H1dom : α1 `notin` dom Θ0) by (clear - Hu; solve_uniq).
    assert (H1S : α1 `in` S0) by (clear - Hcov; env_simp; fsetdec).
    assert (Hcov' : ftvar_in_aenv Θ0 [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    destruct (IH Hu' Hcov') as [Hca [Hu1 Hcv1]].
    pose proof (e_unify_supply_grows Hun) as Hgrow.
    assert (H11 : α1 `notin` dom Θ1).
    { pose proof ((proj1 (proj2 e_assign_unify_consis_dom_upper))
                    _ _ _ _ _ _ Hun) as Hdu.
      clear - Hdu H1dom H1S. fsetdec. }
    repeat split.
    + apply a_unify__flex_skip; assumption.
    + apply uniq_push; assumption.
    + clear - Hcv1 H1S Hgrow. env_simp. fsetdec.

  -
    intros S0 S1 Θ0 Θ1 c b α β Hb Hun IH Hu Hcov.
    assert (Hu' : uniq Θ0) by (clear - Hu; solve_uniq).
    assert (Hcdom : c `notin` dom Θ0) by (clear - Hu; solve_uniq).
    assert (HcS : c `in` S0) by (clear - Hcov; env_simp; fsetdec).
    assert (Hbcov : ftvar_in_abind b [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    assert (Hcov' : ftvar_in_aenv Θ0 [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    destruct (IH Hu' Hcov') as [Hca [Hu1 Hcv1]].
    pose proof (e_unify_supply_grows Hun) as Hgrow.
    assert (Hc1 : c `notin` dom Θ1).
    { pose proof ((proj1 (proj2 e_assign_unify_consis_dom_upper))
                    _ _ _ _ _ _ Hun) as Hdu.
      clear - Hdu Hcdom HcS. fsetdec. }
    repeat split.
    + apply a_unify__skip_other; assumption.
    + apply uniq_push; assumption.
    + clear - Hcv1 HcS Hbcov Hgrow. env_simp. fsetdec.

  -
    intros Δ1 Δ2 S Θ0 P0 Hd Hu Hcov.
    repeat split; [ apply a_consis__ghost | | ];
      solve [ assumption | clear - Hcov; fsetdec ].
  -
    intros Δ1 Δ2 S Θ0 Hu Hcov.
    repeat split; [ apply a_consis__unit | assumption
                  | clear - Hcov; fsetdec ].
  -
    intros Δ1 Δ2 S Θ0 α Hb Hu Hcov.
    repeat split; [ apply a_consis__rigid; assumption | assumption
                  | clear - Hcov; fsetdec ].

  -
    intros Δ1 Δ2 S0 S1 S2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc1 IH1 Hc2 IH2 Hu Hcov.
    simpl in Hcov.
    assert (Hcov1 : ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0a ∪ ftvar_in_pskl P1
                      ∪ Δ1 ∪ Δ2 [<=] S0) by (clear - Hcov; fsetdec).
    destruct (IH1 Hu Hcov1) as [Ha1 [Hu1 Hcv1]].
    pose proof (e_consis_supply_grows Hc1) as Hg1.
    assert (Hcov2 : ftvar_in_aenv Θ1 ∪ ftvar_in_pskl P0b ∪ ftvar_in_pskl P2
                      ∪ Δ1 ∪ Δ2 [<=] S1) by (clear - Hcov Hcv1 Hg1; fsetdec).
    destruct (IH2 Hu1 Hcov2) as [Ha2 [Hu2 Hcv2]].
    repeat split; [ eapply a_consis__arrow; eassumption | assumption
                  | assumption ].

  -
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q α Hnα Hc IH Hu Hcov.
    simpl in Hcov.
    pose proof (dom_subset_ftvar_in_aenv Θ0) as Hdc.
    assert (Hαdom : α `notin` dom Θ0) by (clear - Hdc Hcov Hnα; fsetdec).
    assert (Hu' : uniq ((α ~ abind_tvar) ++ Θ0))
      by (clear - Hu Hαdom; solve_uniq).
    assert (Hcov' : ftvar_in_aenv ((α ~ abind_tvar) ++ Θ0)
                    ∪ ftvar_in_pskl (open_pskl_wrt_pskl P0 (pskl_var_f α))
                    ∪ ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f α))
                    ∪ add α Δ1 ∪ add α Δ2 [<=] add α S0).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0 (pskl_var_f α)) as H1.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f α)) as H2.
      simpl in H1, H2. clear - H1 H2 Hcov. env_simp. fsetdec. }
    destruct (IH Hu' Hcov') as [Hca [Hu1 Hcv1]].
    repeat split.
    + apply a_consis__forall_inh; [ clear - Hcov Hnα; fsetdec | assumption ].
    + clear - Hu1; solve_uniq.
    + clear - Hcv1. env_simp. fsetdec.

  -
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q α Hnα Hc IH Hu Hcov.
    simpl in Hcov.
    pose proof (dom_subset_ftvar_in_aenv Θ0) as Hdc.
    assert (Hαdom : α `notin` dom Θ0) by (clear - Hdc Hcov Hnα; fsetdec).
    assert (Hu' : uniq ((α ~ abind_tvar) ++ Θ0))
      by (clear - Hu Hαdom; solve_uniq).
    assert (Hcov' : ftvar_in_aenv ((α ~ abind_tvar) ++ Θ0)
                    ∪ ftvar_in_pskl (pskl_univ_ghost P0)
                    ∪ ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f α))
                    ∪ Δ1 ∪ add α Δ2 [<=] add α S0).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f α)) as H2.
      simpl in H2 |- *. clear - H2 Hcov. env_simp. fsetdec. }
    destruct (IH Hu' Hcov') as [Hca [Hu1 Hcv1]].
    repeat split.
    + apply a_consis__forall_syn; [ clear - Hcov Hnα; fsetdec | assumption ].
    + clear - Hu1; solve_uniq.
    + clear - Hcv1. env_simp. fsetdec.

  -
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q Hc IH Hu Hcov.
    simpl in Hcov.
    destruct (IH Hu ltac:(clear - Hcov; fsetdec)) as [Hca [Hu1 Hcv1]].
    repeat split; [ apply a_consis__univ_ghost | | ]; assumption.

  -
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q α Hnα Hc IH Hu Hcov.
    simpl in Hcov.
    pose proof (dom_subset_ftvar_in_aenv Θ0) as Hdc.
    assert (Hαdom : α `notin` dom Θ0) by (clear - Hdc Hcov Hnα; fsetdec).
    assert (Hu' : uniq ((α ~ abind_tvar) ++ Θ0))
      by (clear - Hu Hαdom; solve_uniq).
    assert (Hcov' : ftvar_in_aenv ((α ~ abind_tvar) ++ Θ0)
                    ∪ ftvar_in_pskl (open_pskl_wrt_pskl P0 (pskl_var_f α))
                    ∪ ftvar_in_pskl (pskl_univ_ghost P)
                    ∪ add α Δ1 ∪ Δ2 [<=] add α S0).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0 (pskl_var_f α)) as H1.
      simpl in H1 |- *. clear - H1 Hcov. env_simp. fsetdec. }
    destruct (IH Hu' Hcov') as [Hca [Hu1 Hcv1]].
    repeat split.
    + apply a_consis__univ_ghost1; [ clear - Hcov Hnα; fsetdec | assumption ].
    + clear - Hu1; solve_uniq.
    + clear - Hcv1. env_simp. fsetdec.

  -
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q Hgd Hnf Hc IH Hu Hcov.
    simpl in Hcov.
    destruct (IH Hu ltac:(clear - Hcov; fsetdec)) as [Hca [Hu1 Hcv1]].
    repeat split; [ apply a_consis__univ_ghost2 | | ]; assumption.

  -
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 α β Hun IH Hu Hcov.
    destruct (IH Hu ltac:(clear - Hcov; fsetdec)) as [Hua [Hu1 Hcv1]].
    repeat split; [ apply a_consis__flex | | ]; assumption.

  -
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 α P0 Hnf Hnhole Ha IH Hu Hcov.
    assert (Hu' : uniq (nil ++ Θ0)) by (clear - Hu; simpl_env; assumption).
    assert (Hcov' : ftvar_in_aenv (nil ++ Θ0) ∪ ftvar_in_pskl P0 [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    destruct (IH Hu' Hcov') as [Haa [Hu1 Hcv1]].
    repeat split; [ apply a_consis__flex_l | | ]; assumption.

  -
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 α P Hnf Hnhole Ha IH Hu Hcov.
    assert (Hu' : uniq (nil ++ Θ0)) by (clear - Hu; simpl_env; assumption).
    assert (Hcov' : ftvar_in_aenv (nil ++ Θ0) ∪ ftvar_in_pskl P [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    destruct (IH Hu' Hcov') as [Haa [Hu1 Hcv1]].
    repeat split; [ apply a_consis__flex_r | | ]; assumption.

  -
    intros Δ1 Δ2 S Θ0 P Hd Hu Hcov.
    repeat split; [ apply a_consis__ghost_r; assumption | assumption
                  | clear - Hcov; fsetdec ].

  -
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q Hgd Hnf Hc IH Hu Hcov.
    simpl in Hcov.
    destruct (IH Hu ltac:(clear - Hcov; fsetdec)) as [Hca [Hu1 Hcv1]].
    repeat split; [ apply a_consis__univ_ghost_r | | ]; assumption.
Qed.

Corollary e_consis_sound : forall Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}e ->
  uniq Θ0 ->
  ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 ∪ ftvar_in_pskl P ∪ Δ1 ∪ Δ2 [<=] S0 ->
  {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}a.
Proof.
  intros. eapply (proj2 (proj2 e_assign_unify_consis_sound)); eassumption.
Qed.

Corollary e_consis_sound_init : forall P0 P Q S1 Θ1,
  {{ (ftvar_in_pskl P0 ∪ ftvar_in_pskl P) ↝ S1
     ⊨ nil ⊢[ empty | empty | P0 ] P ∼ Q ⊣ Θ1 }}e ->
  {{ nil ⊢[ P0 ] P ∼ Q ⊣ Θ1 }}a.
Proof.
  intros * He. eapply e_consis_sound; [ exact He | apply uniq_nil | ].
  simpl. fsetdec.
Qed.

Lemma e_assign_unify_consis_out_ftvar :
  (forall S0 Θ0 Ξ α P S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e -> True) /\
  (forall S0 Θ0 α β S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}e -> True) /\
  (forall Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}e ->
     uniq Θ0 ->
     ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 ∪ ftvar_in_pskl P
       ∪ Δ1 ∪ Δ2 [<=] S0 ->
     ftvar_in_pskl Q [<=] S1).
Proof.
  apply e_assign_unify_consis_mutind;

    try (intros; exact I).

  -
    intros Δ1 Δ2 S Θ0 P0 Hd Hu Hcov. clear - Hcov. fsetdec.
  -
    intros Δ1 Δ2 S Θ0 Hu Hcov. simpl. fsetdec.
  -
    intros Δ1 Δ2 S Θ0 α Hb Hu Hcov. clear - Hcov. simpl in *. fsetdec.

  -
    intros Δ1 Δ2 S0 S1 S2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc1 IH1 Hc2 IH2 Hu Hcov.
    simpl in Hcov |- *.
    pose proof (e_consis_supply_grows Hc1) as Hg1.
    pose proof (e_consis_supply_grows Hc2) as Hg2.
    pose proof ((proj2 (proj2 e_assign_unify_consis_sound))
                  _ _ _ _ _ _ _ _ _ Hc1 Hu ltac:(clear - Hcov; fsetdec))
      as [_ [Hu1 Hcv1]].
    specialize (IH1 Hu ltac:(clear - Hcov; fsetdec)).
    specialize (IH2 Hu1 ltac:(clear - Hcov Hcv1 Hg1; fsetdec)).
    clear - IH1 IH2 Hg2. fsetdec.

  -
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q α Hnα Hc IH Hu Hcov.
    simpl in Hcov.
    pose proof (dom_subset_ftvar_in_aenv Θ0) as Hdc.
    assert (Hαdom : α `notin` dom Θ0) by (clear - Hdc Hcov Hnα; fsetdec).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0 (pskl_var_f α)) as H1.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f α)) as H2.
    simpl in H1, H2.
    specialize (IH ltac:(clear - Hu Hαdom; solve_uniq)
                   ltac:(clear - H1 H2 Hcov; env_simp; fsetdec)).
    simpl. rewrite ftvar_in_pskl_close_pskl_wrt_pskl. clear - IH. fsetdec.

  -
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q α Hnα Hc IH Hu Hcov.
    simpl in Hcov.
    pose proof (dom_subset_ftvar_in_aenv Θ0) as Hdc.
    assert (Hαdom : α `notin` dom Θ0) by (clear - Hdc Hcov Hnα; fsetdec).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f α)) as H2.
    simpl in H2.
    specialize (IH ltac:(clear - Hu Hαdom; solve_uniq)
                   ltac:(clear - H2 Hcov; env_simp; simpl; fsetdec)).
    simpl. rewrite ftvar_in_pskl_close_pskl_wrt_pskl. clear - IH. fsetdec.

  -
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q Hc IH Hu Hcov.
    simpl in Hcov |- *. apply IH; [ exact Hu | clear - Hcov; fsetdec ].

  -
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q α Hnα Hc IH Hu Hcov.
    simpl in Hcov.
    pose proof (dom_subset_ftvar_in_aenv Θ0) as Hdc.
    assert (Hαdom : α `notin` dom Θ0) by (clear - Hdc Hcov Hnα; fsetdec).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0 (pskl_var_f α)) as H1.
    simpl in H1.
    specialize (IH ltac:(clear - Hu Hαdom; solve_uniq)
                   ltac:(clear - H1 Hcov; env_simp; simpl; fsetdec)).
    simpl. rewrite ftvar_in_pskl_close_pskl_wrt_pskl. clear - IH. fsetdec.

  -
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q Hgd Hnf Hc IH Hu Hcov.
    simpl in Hcov. apply IH; [ exact Hu | clear - Hcov; fsetdec ].

  -
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 α β Hun IH Hu Hcov.
    pose proof (e_unify_supply_grows Hun) as Hg.
    clear - Hcov Hg. simpl in *. fsetdec.
  -
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 α P0 Hnf Hnhole Ha IH Hu Hcov.
    pose proof (e_assign_supply_grows Ha) as Hg.
    clear - Hcov Hg. simpl in *. fsetdec.
  -
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 α P Hnf Hnhole Ha IH Hu Hcov.
    pose proof (e_assign_supply_grows Ha) as Hg.
    clear - Hcov Hg. simpl in *. fsetdec.

  -
    intros Δ1 Δ2 S Θ0 P Hd Hu Hcov. clear - Hcov. fsetdec.
  -
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q Hgd Hnf Hc IH Hu Hcov.
    simpl in Hcov. apply IH; [ exact Hu | clear - Hcov; fsetdec ].
Qed.

Corollary e_consis_out_ftvar : forall Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}e ->
  uniq Θ0 ->
  ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 ∪ ftvar_in_pskl P ∪ Δ1 ∪ Δ2 [<=] S0 ->
  ftvar_in_pskl Q [<=] S1.
Proof.
  intros. eapply (proj2 (proj2 e_assign_unify_consis_out_ftvar)); eassumption.
Qed.

Lemma e_assign_target_flex : forall S0 Θ0 Ξ α P S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e -> a_flex_tvar Θ0 α.
Proof.
  intros * Hd.
  induction Hd; try (apply a_flex_tvar_weaken_app; assumption).
  -  left; simpl; auto.
  -  left; simpl; auto.
  -  assumption.
Qed.

Lemma e_unify_target_flex : forall S0 Θ0 α β S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}e ->
  a_flex_tvar Θ0 α /\ a_flex_tvar Θ0 β.
Proof.
  intros * Hd.
  induction Hd;
    try (destruct IHHd as [Hα Hβ];
         split; apply a_flex_tvar_weaken_app; assumption).
  -  split; assumption.
  -
    split; [ left; simpl; auto | apply a_flex_tvar_weaken_app; assumption ].
  -
    split; [ apply a_flex_tvar_weaken_app; assumption | left; simpl; auto ].
  -  split; assumption.
Qed.

Lemma e_consis_delta_respect : forall Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}e ->
  forall Δ1' Δ2', Δ1' [=] Δ1 -> Δ2' [=] Δ2 ->
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1' | Δ2' | P0 ] P ∼ Q ⊣ Θ1 }}e.
Proof.
  induction 1; intros Δ1' Δ2' HD1 HD2;
    try solve [econstructor; eauto 2].
  - apply e_consis__ghost. clear - H HD2; fsetdec.
  - apply e_consis__forall_inh with (α := α); auto.
    apply IHe_consis; [ clear - HD1; fsetdec | clear - HD2; fsetdec ].
  - apply e_consis__forall_syn with (α := α); auto.
    apply IHe_consis; [ assumption | clear - HD2; fsetdec ].
  - apply e_consis__univ_ghost1 with (α := α); auto.
    apply IHe_consis; [ clear - HD1; fsetdec | assumption ].
  - apply e_consis__ghost_r. clear - H HD1; fsetdec.
Qed.

Lemma e_assign_unify_consis_swap : forall a b,
  (forall S0 Θ0 Ξ α P S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
     forall S0', S0' [=] swap_atoms a b S0 ->
     exists S1', S1' [=] swap_atoms a b S1 /\
       {{ S0' ↝ S1' ⊨ (swap_aenv a b Θ0) ⊲[ swap_aenv a b Ξ ]
          (swap_atom a b α) ≔ (swap_pskl a b P)
          ⊣ (swap_aenv a b Θ1) }}e) /\
  (forall S0 Θ0 α β S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}e ->
     forall S0', S0' [=] swap_atoms a b S0 ->
     exists S1', S1' [=] swap_atoms a b S1 /\
       {{ S0' ↝ S1' ⊨ (swap_aenv a b Θ0) ⊲
          (swap_atom a b α) ≈ᵘ (swap_atom a b β)
          ⊣ (swap_aenv a b Θ1) }}e) /\
  (forall Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}e ->
     forall Δ1' Δ2' S0',
       Δ1' [=] swap_atoms a b Δ1 -> Δ2' [=] swap_atoms a b Δ2 ->
       S0' [=] swap_atoms a b S0 ->
     exists S1', S1' [=] swap_atoms a b S1 /\
       {{ S0' ↝ S1' ⊨ (swap_aenv a b Θ0) ⊢[ Δ1' | Δ2' | (swap_pskl a b P0) ]
          (swap_pskl a b P) ∼ (swap_pskl a b Q)
          ⊣ (swap_aenv a b Θ1) }}e).
Proof.
  intros a b.
  apply e_assign_unify_consis_mutind.
  all: try solve [
    intros; simpl;
    repeat match goal with
    | IH : forall S', S' [=] ?S -> exists _, _ /\ _,
      Heq : ?S' [=] ?S |- _ =>
        destruct (IH _ Heq) as [? [? ?]]; clear IH
    | IH : forall Δ1' Δ2' S', Δ1' [=] ?Δ1 -> Δ2' [=] ?Δ2 ->
        S' [=] ?S -> exists _, _ /\ _,
      HΔ1 : ?Δ1' [=] ?Δ1, HΔ2 : ?Δ2' [=] ?Δ2,
      Heq : ?S' [=] ?S |- _ =>
        destruct (IH _ _ _ HΔ1 HΔ2 Heq) as [? [? ?]]; clear IH
    end;
    eexists; split; [ eassumption | econstructor;
      eauto 3 using swap_atom_neq, a_flex_tvar_swap, swap_pskl_ftv_notin,
        swap_aenv_binds, guarded_pskl_swap, a_non_flex_swap,
        swap_pskl_not_ghost, swap_inter_ftv_empty ] ].
  -
    intros S0 S1 Θ0 Ξ α P βs τ Hocc Hg Hm S0' Heq. simpl.
    destruct (e_guess_mono_swap Hg Heq) as [S1' [HS1 Hg']].
    exists S1'. split; [ exact HS1 | ].
    rewrite !swap_aenv_app.
    apply e_assign__solve_m with (βs := swap_aenv a b βs);
      auto using swap_pskl_ftv_notin, mono_ptyp_swap.
  -
    intros S0 S1 Θ0 Θ1 Ξ α β τ P Q Hflex Hd IH S0' Heq. simpl.
    destruct (IH empty empty S0'
                 (empty_eq_swap_atoms_empty a b)
                 (empty_eq_swap_atoms_empty a b) Heq) as [S1' [HS1 Hd']].
    exists S1'. split; [ exact HS1 | ].
    eapply e_assign__assign.
    + exact (a_flex_tvar_swap a b _ _ Hflex).
    + rewrite swap_aenv_app in Hd'.
      rewrite !swap_pskl_subst in Hd'.
      rewrite !swap_pskl_ptyp_to_pskl in Hd'.
      change (swap_pskl a b (pskl_var_f α)) with
        (pskl_var_f (swap_atom a b α)) in Hd'.
      exact Hd'.
  -
    intros S0 S1 Θ0 Θ1 Ξ α β P Hne Hin Hd IH S0' Heq. simpl.
    destruct (IH _ Heq) as [S1' [HS1 Hd']].
    exists S1'. split; [ exact HS1 | ].
    rewrite swap_aenv_app in Hd'.
    apply e_assign__depend;
      [ auto using swap_atom_neq | auto using swap_pskl_ftv_in | exact Hd' ].
  -
    intros S0 S1 Θ0 Θ1 α1 τ α β Q Hf1 Hf2 Hd IH S0' Heq. simpl.
    destruct (IH empty empty S0'
                 (empty_eq_swap_atoms_empty a b)
                 (empty_eq_swap_atoms_empty a b) Heq) as [S1' [HS1 Hd']].
    exists S1'. split; [ exact HS1 | ].
    eapply e_unify__flex_assign.
    + exact (a_flex_tvar_swap a b _ _ Hf1).
    + exact (a_flex_tvar_swap a b _ _ Hf2).
    + rewrite !swap_pskl_ptyp_to_pskl in Hd'.
      rewrite !swap_ptyp_subst in Hd'.
      change (swap_ptyp a b (ptyp_var_f β)) with
        (ptyp_var_f (swap_atom a b β)) in Hd'.
      change (swap_ptyp a b (ptyp_var_f α)) with
        (ptyp_var_f (swap_atom a b α)) in Hd'.
      exact Hd'.
  -
    intros S0 S1 Θ0 Θ1 c bd α β Hb Hd IH S0' Heq. simpl.
    destruct (IH _ Heq) as [S1' [HS1 Hd']].
    exists S1'. split; [ exact HS1 | ].
    apply e_unify__skip_other; [ | exact Hd' ].
    destruct Hb as [-> | [[A ->] | [Qb ->]]]; simpl.
    + left; reflexivity.
    + right; left; eexists; reflexivity.
    + right; right; eexists; reflexivity.
  -
    intros Δ1 Δ2 S Θ0 α Hb Δ1' Δ2' S0' HΔ1 HΔ2 Heq. simpl.
    exists S0'. split; [ exact Heq | ].
    apply e_consis__rigid. exact (swap_aenv_binds a b _ _ _ Hb).
  -
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q α Hfr Hd IH Δ1' Δ2' S0' HΔ1 HΔ2 Heq.
    simpl. rewrite swap_pskl_close.
    destruct (IH (add (swap_atom a b α) Δ1') (add (swap_atom a b α) Δ2')
                 (add (swap_atom a b α) S0')
                 (eq_swap_atoms_add a b α _ _ HΔ1)
                 (eq_swap_atoms_add a b α _ _ HΔ2)
                 (eq_swap_atoms_add a b α _ _ Heq)) as [S1' [HS1 Hd']].
    exists S1'. split; [ exact HS1 | ].
    apply e_consis__forall_inh with (α := swap_atom a b α).
    + eapply swap_notin_eq; eassumption.
    + rewrite !swap_pskl_open_var in Hd'. exact Hd'.
  -
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q α Hfr Hd IH Δ1' Δ2' S0' HΔ1 HΔ2 Heq.
    simpl. rewrite swap_pskl_close.
    destruct (IH Δ1' (add (swap_atom a b α) Δ2')
                 (add (swap_atom a b α) S0')
                 HΔ1 (eq_swap_atoms_add a b α _ _ HΔ2)
                 (eq_swap_atoms_add a b α _ _ Heq)) as [S1' [HS1 Hd']].
    exists S1'. split; [ exact HS1 | ].
    apply e_consis__forall_syn with (α := swap_atom a b α).
    + eapply swap_notin_eq; eassumption.
    + rewrite !swap_pskl_open_var in Hd'. exact Hd'.
  -
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q α Hfr Hd IH Δ1' Δ2' S0' HΔ1 HΔ2 Heq.
    simpl. rewrite swap_pskl_close.
    destruct (IH (add (swap_atom a b α) Δ1') Δ2'
                 (add (swap_atom a b α) S0')
                 (eq_swap_atoms_add a b α _ _ HΔ1) HΔ2
                 (eq_swap_atoms_add a b α _ _ Heq)) as [S1' [HS1 Hd']].
    exists S1'. split; [ exact HS1 | ].
    apply e_consis__univ_ghost1 with (α := swap_atom a b α).
    + eapply swap_notin_eq; eassumption.
    + rewrite !swap_pskl_open_var in Hd'. exact Hd'.
Qed.

Lemma e_assign_unify_consis_supply_respect :
  (forall S0 Θ0 Ξ α P S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
     forall S0', S0' [=] S0 ->
     exists S1', S1' [=] S1 /\ {{ S0' ↝ S1' ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e) /\
  (forall S0 Θ0 α β S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}e ->
     forall S0', S0' [=] S0 ->
     exists S1', S1' [=] S1 /\ {{ S0' ↝ S1' ⊨ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}e) /\
  (forall Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}e ->
     forall S0', S0' [=] S0 ->
     exists S1', S1' [=] S1 /\
       {{ S0' ↝ S1' ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}e).
Proof.
  destruct (atom_fresh empty) as [a _].
  pose proof (@e_assign_unify_consis_swap a a) as Hswap.
  setoid_rewrite swap_aenv_same in Hswap.
  setoid_rewrite swap_pskl_same in Hswap.
  setoid_rewrite swap_atom_same in Hswap.
  setoid_rewrite swap_atoms_same in Hswap.
  destruct Hswap as [Ha [Hu Hc]].
  split; [exact Ha |]. split; [exact Hu |].
  intros Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1 Hd S0' Heq.
  eapply Hc; [exact Hd | reflexivity | reflexivity | exact Heq].
Qed.

Corollary e_consis_supply_respect : forall Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}e ->
  forall S0', S0' [=] S0 ->
  exists S1', S1' [=] S1 /\
    {{ S0' ↝ S1' ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}e.
Proof. apply e_assign_unify_consis_supply_respect. Qed.

Corollary e_consis_swap : forall a b Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}e ->
  forall Δ1' Δ2' S0',
    Δ1' [=] swap_atoms a b Δ1 -> Δ2' [=] swap_atoms a b Δ2 ->
    S0' [=] swap_atoms a b S0 ->
  exists S1', S1' [=] swap_atoms a b S1 /\
    {{ S0' ↝ S1' ⊨ (swap_aenv a b Θ0) ⊢[ Δ1' | Δ2' | (swap_pskl a b P0) ]
       (swap_pskl a b P) ∼ (swap_pskl a b Q) ⊣ (swap_aenv a b Θ1) }}e.
Proof. intros a b. apply e_assign_unify_consis_swap. Qed.
