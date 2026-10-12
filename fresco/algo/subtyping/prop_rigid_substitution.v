Require Import src.fresco.algo_decl.prop_ctx_mono.
Require Import src.fresco.prop_atom_sets.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.prop_tag.
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

Set Implicit Arguments.

Inductive uskl_rsubst (NM : a_sub_mode) (Θ : aenv)
  : atoms -> atoms -> uskl -> uskl -> Prop :=
| ursubst__refl : forall Δρ Ψρ R,
    lc_uskl R ->
    Ψρ [=] empty ->
    uskl_rsubst NM Θ Δρ Ψρ R R
| ursubst__leaf : forall Δρ Ψρ α Ψ'' ψ'',
    α `in` Δρ ->
    a_tags_sort NM Ψ'' ψ'' ->
    {{ Θ ⨟ empty ⊢ₚₛ ⌊ ψ'' ⌋ˢ }}a ->
    Ψρ [=] Ψ'' ->
    uskl_rsubst NM Θ Δρ Ψρ ψ'' (uskl_var_f α)
| ursubst__arrow : forall Δρ Ψρ Ψ1 Ψ2 R1' R2' R1 R2,
    uskl_rsubst NM Θ Δρ Ψ1 R1' R1 ->
    uskl_rsubst NM Θ Δρ Ψ2 R2' R2 ->
    Ψρ [=] Ψ1 `union` Ψ2 ->
    uskl_rsubst NM Θ Δρ Ψρ (uskl_arrow R1' R2') (uskl_arrow R1 R2)
| ursubst__all_syn : forall L Δρ Ψρ R' R,
    (forall α, α `notin` L ->
       uskl_rsubst NM Θ Δρ Ψρ
         (open_uskl_wrt_uskl R' (uskl_var_f α))
         (open_uskl_wrt_uskl R (uskl_var_f α))) ->
    uskl_rsubst NM Θ Δρ Ψρ (uskl_all_syn R') (uskl_all_syn R)
| ursubst__all_tag : forall L Δρ Ψρ ε R' R,
    (forall α, α `notin` L ->
       uskl_rsubst NM Θ Δρ Ψρ
         (open_uskl_wrt_uskl R' (uskl_var_f α))
         (open_uskl_wrt_uskl R (uskl_var_f α))) ->
    uskl_rsubst NM Θ Δρ Ψρ (uskl_all_tag ε R') (uskl_all_tag ε R)
| ursubst__univ_ghost : forall Δρ Ψρ R' R,
    uskl_rsubst NM Θ Δρ Ψρ R' R ->
    uskl_rsubst NM Θ Δρ Ψρ (uskl_univ_ghost R') (uskl_univ_ghost R)
| ursubst__dot_univ_ghost : forall Δρ Ψρ R' R,
    uskl_rsubst NM Θ Δρ Ψρ R' R ->
    uskl_rsubst NM Θ Δρ Ψρ (uskl_dot_univ_ghost R') (uskl_dot_univ_ghost R).

Lemma uskl_rsubst_ftag_sub : forall NM Θ Δρ Ψρ R' R,
  uskl_rsubst NM Θ Δρ Ψρ R' R ->
  ftag_in_uskl R' [<=] Ψρ `union` ftag_in_uskl R.
Proof.
  intros NM Θ Δρ Ψρ R' R H; induction H; simpl; try fsetdec.
  -
    pose proof (d_tags_skl_ftag (a_tags_sort_d_tags H0)) as Ht.
    fsetdec.
  -
    pick fresh α for L.
    pose proof (H0 α ltac:(solve_notin_auto)) as Hα.
    pose proof (ftag_in_uskl_open_var R' α).
    pose proof (ftag_in_uskl_open_var R α).
    fsetdec.
  -
    pick fresh α for L.
    pose proof (H0 α ltac:(solve_notin_auto)) as Hα.
    pose proof (ftag_in_uskl_open_var R' α).
    pose proof (ftag_in_uskl_open_var R α).
    fsetdec.
Qed.

Definition rsubst_leaf (NM : a_sub_mode) (Θ : aenv) (Δρ Ψρ : atoms)
    (R : uskl) (ψa : uskl) : Prop :=
  exists α Ψ'', ψa = uskl_var_f α /\ α `in` Δρ /\
    a_tags_sort NM Ψ'' R /\ {{ Θ ⨟ empty ⊢ₚₛ ⌊ R ⌋ˢ }}a /\ Ψρ [=] Ψ''.

Local Ltac rho_andsplit := repeat match goal with |- _ /\ _ => split end.
Local Ltac rho_refl_tac := left; split; [ reflexivity | assumption ].

Lemma uskl_rsubst_arrow_l_inv : forall NM Θ Δρ Ψρ R1' R2' ψa,
  uskl_rsubst NM Θ Δρ Ψρ (uskl_arrow R1' R2') ψa ->
  (ψa = uskl_arrow R1' R2' /\ Ψρ [=] empty)
  \/ rsubst_leaf NM Θ Δρ Ψρ (uskl_arrow R1' R2') ψa
  \/ (exists R1 R2 Ψ1 Ψ2, ψa = uskl_arrow R1 R2 /\
        uskl_rsubst NM Θ Δρ Ψ1 R1' R1 /\ uskl_rsubst NM Θ Δρ Ψ2 R2' R2 /\
        Ψρ [=] Ψ1 `union` Ψ2).
Proof.
  intros NM Θ Δρ Ψρ R1' R2' ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; left; exists α, Ψ''; rho_andsplit; try reflexivity; assumption.
  - right; right; exists R1, R2, Ψ1, Ψ2; rho_andsplit;
      try reflexivity; assumption.
Qed.

Lemma uskl_rsubst_unit_l_inv : forall NM Θ Δρ Ψρ ψa,
  uskl_rsubst NM Θ Δρ Ψρ uskl_unit ψa ->
  (ψa = uskl_unit /\ Ψρ [=] empty) \/ rsubst_leaf NM Θ Δρ Ψρ uskl_unit ψa.
Proof.
  intros NM Θ Δρ Ψρ ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; exists α, Ψ''; rho_andsplit; try reflexivity; assumption.
Qed.

Lemma uskl_rsubst_var_l_inv : forall NM Θ Δρ Ψρ β ψa,
  uskl_rsubst NM Θ Δρ Ψρ (uskl_var_f β) ψa ->
  (ψa = uskl_var_f β /\ Ψρ [=] empty) \/ rsubst_leaf NM Θ Δρ Ψρ (uskl_var_f β) ψa.
Proof.
  intros NM Θ Δρ Ψρ β ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; exists α, Ψ''; rho_andsplit; try reflexivity; assumption.
Qed.

Lemma uskl_rsubst_ghost_l_inv : forall NM Θ Δρ Ψρ ψa,
  uskl_rsubst NM Θ Δρ Ψρ uskl_ghost ψa ->
  (ψa = uskl_ghost /\ Ψρ [=] empty) \/ rsubst_leaf NM Θ Δρ Ψρ uskl_ghost ψa.
Proof.
  intros NM Θ Δρ Ψρ ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; exists α, Ψ''; rho_andsplit; try reflexivity; assumption.
Qed.

Lemma uskl_rsubst_dot_ghost_l_inv : forall NM Θ Δρ Ψρ ψa,
  uskl_rsubst NM Θ Δρ Ψρ uskl_dot_ghost ψa ->
  (ψa = uskl_dot_ghost /\ Ψρ [=] empty) \/ rsubst_leaf NM Θ Δρ Ψρ uskl_dot_ghost ψa.
Proof.
  intros NM Θ Δρ Ψρ ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; exists α, Ψ''; rho_andsplit; try reflexivity; assumption.
Qed.

Lemma uskl_rsubst_univ_ghost_l_inv : forall NM Θ Δρ Ψρ R' ψa,
  uskl_rsubst NM Θ Δρ Ψρ (uskl_univ_ghost R') ψa ->
  (ψa = uskl_univ_ghost R' /\ Ψρ [=] empty)
  \/ rsubst_leaf NM Θ Δρ Ψρ (uskl_univ_ghost R') ψa
  \/ (exists R, ψa = uskl_univ_ghost R /\ uskl_rsubst NM Θ Δρ Ψρ R' R).
Proof.
  intros NM Θ Δρ Ψρ R' ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; left; exists α, Ψ''; rho_andsplit; try reflexivity; assumption.
  - right; right; exists R; split; [ reflexivity | assumption ].
Qed.

Lemma uskl_rsubst_dot_univ_ghost_l_inv : forall NM Θ Δρ Ψρ R' ψa,
  uskl_rsubst NM Θ Δρ Ψρ (uskl_dot_univ_ghost R') ψa ->
  (ψa = uskl_dot_univ_ghost R' /\ Ψρ [=] empty)
  \/ rsubst_leaf NM Θ Δρ Ψρ (uskl_dot_univ_ghost R') ψa
  \/ (exists R, ψa = uskl_dot_univ_ghost R /\ uskl_rsubst NM Θ Δρ Ψρ R' R).
Proof.
  intros NM Θ Δρ Ψρ R' ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; left; exists α, Ψ''; rho_andsplit; try reflexivity; assumption.
  - right; right; exists R; split; [ reflexivity | assumption ].
Qed.

Lemma uskl_rsubst_all_syn_l_inv : forall NM Θ Δρ Ψρ R' ψa,
  uskl_rsubst NM Θ Δρ Ψρ (uskl_all_syn R') ψa ->
  (ψa = uskl_all_syn R' /\ Ψρ [=] empty)
  \/ rsubst_leaf NM Θ Δρ Ψρ (uskl_all_syn R') ψa
  \/ (exists L R, ψa = uskl_all_syn R /\
        forall α, α `notin` L ->
          uskl_rsubst NM Θ Δρ Ψρ (open_uskl_wrt_uskl R' (uskl_var_f α))
                              (open_uskl_wrt_uskl R (uskl_var_f α))).
Proof.
  intros NM Θ Δρ Ψρ R' ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; left; exists α, Ψ''; rho_andsplit; try reflexivity; assumption.
  - right; right; exists L, R; split; [ reflexivity | eassumption ].
Qed.

Lemma uskl_rsubst_all_tag_l_inv : forall NM Θ Δρ Ψρ ε R' ψa,
  uskl_rsubst NM Θ Δρ Ψρ (uskl_all_tag ε R') ψa ->
  (ψa = uskl_all_tag ε R' /\ Ψρ [=] empty)
  \/ rsubst_leaf NM Θ Δρ Ψρ (uskl_all_tag ε R') ψa
  \/ (exists L R, ψa = uskl_all_tag ε R /\
        forall α, α `notin` L ->
          uskl_rsubst NM Θ Δρ Ψρ (open_uskl_wrt_uskl R' (uskl_var_f α))
                              (open_uskl_wrt_uskl R (uskl_var_f α))).
Proof.
  intros NM Θ Δρ Ψρ ε R' ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; left; exists α, Ψ''; rho_andsplit; try reflexivity; assumption.
  - right; right; exists L, R; split; [ reflexivity | eassumption ].
Qed.

Fixpoint pskl_shielded_ftv (P : pskl) : atoms :=
  match P with
  | pskl_unit => {}
  | pskl_var_b _ => {}
  | pskl_var_f _ => {}
  | pskl_arrow P1 P2 => pskl_shielded_ftv P1 `union` pskl_shielded_ftv P2
  | pskl_all_syn P0 => pskl_shielded_ftv P0
  | pskl_ghost => {}
  | pskl_univ_ghost P0 => ftvar_in_pskl P0
  end.

Lemma pskl_shielded_ftv_sub_ftv : forall P,
  pskl_shielded_ftv P [<=] ftvar_in_pskl P.
Proof. induction P; simpl; fsetdec. Qed.

Definition rsubst_fresh (Δρ : atoms) (Θ : aenv) (κ : metasubst) : Prop :=
  forall α0, α0 `in` Δρ ->
    binds α0 abind_tvar Θ /\
    (forall p, In p κ -> α0 `notin` ftvar_in_ptyp (snd p)) /\
    (forall α τ, binds α (abind_flex_mono_def τ) Θ ->
       α0 `notin` ftvar_in_ptyp τ).

Lemma rsubst_fresh_weaken_tvar : forall Δρ Θ κ β,
  rsubst_fresh Δρ Θ κ ->
  rsubst_fresh Δρ ((β ~ abind_tvar) ++ Θ) κ.
Proof.
  intros Δρ Θ κ β Hrf α0 Hα0.
  destruct (Hrf α0 Hα0) as (Hb & Hκ & Hdef).
  repeat split.
  - apply binds_app_3; exact Hb.
  - exact Hκ.
  - intros α τ Hbd. analyze_binds Hbd. eapply Hdef; eassumption.
Qed.

Lemma a_inc_image_ftv_dom : forall Θ0 κ Θ,
  κ ∷ Θ0 ⊑ Θ ->
  forall p, In p κ -> ftvar_in_ptyp (snd p) [<=] dom Θ.
Proof.
  intros Θ0 κ Θ H; induction H; intros p Hp; simpl in Hp.
  - contradiction.
  - destruct Hp as [<- | Hp];
      [ simpl; apply a_wf_ptyp_ftv_dom; assumption | eauto ].
  - destruct Hp as [<- | Hp];
      [ simpl; apply a_wf_ptyp_ftv_dom; assumption | eauto ].
  - pose proof (IHa_inc p Hp) as Hb.
    repeat rewrite dom_app. clear - Hb; fsetdec.
  - pose proof (IHa_inc p Hp) as Hb.
    repeat rewrite dom_app. clear - Hb; fsetdec.
  - pose proof (IHa_inc p Hp) as Hb.
    repeat rewrite dom_app. clear - Hb; fsetdec.
Qed.

Lemma rsubst_fresh_open_tvar : forall Δρ Θ0 Θ κ β,
  {{ ⊢ Θ }}a -> κ ∷ Θ0 ⊑ Θ -> β `notin` dom Θ ->
  rsubst_fresh Δρ Θ κ ->
  rsubst_fresh (add β Δρ) ((β ~ abind_tvar) ++ Θ) κ.
Proof.
  intros * Hwf Hκ Hβ Hfr γ Hγ.
  destruct (γ == β) as [-> | Hne].
  - repeat split.
    + unfold binds; left; reflexivity.
    + intros p Hp; pose proof (a_inc_image_ftv_dom Hκ p Hp) as Hd.
      clear - Hd Hβ; fsetdec.
    + intros α τ Hb. apply binds_flex_def_cons_tvar_inv in Hb.
      pose proof (a_wf_ptyp_ftv_dom (@a_wf_aenv_binds_def_wf Θ α τ Hwf Hb)) as Hd.
      clear - Hd Hβ; fsetdec.
  - apply (rsubst_fresh_weaken_tvar β Hfr).
    clear - Hγ Hne; fsetdec.
Qed.

Lemma ad_ppre_var_target_absent : forall Θ Δ Ψ P ψ,
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  forall α', ψ = uskl_var_f α' ->
  {{ ⊢ Θ }}a ->
  α' `in` Δ ->
  binds α' abind_tvar Θ ->
  (forall α τ, binds α (abind_flex_mono_def τ) Θ ->
     α' `notin` ftvar_in_ptyp τ) ->
  α' `notin` ftvar_in_pskl P ->
  False.
Proof.
  intros Θ Δ Ψ P ψ H; induction H;
    intros α00 Heq Hwf Hα0Δ HXb Hdef Hftv; try discriminate Heq.
  -
    inversion Heq; subst. simpl in Hftv. clear - Hftv; fsetdec.
  -
    subst ψ. simpl in H0. clear - H0 Hα0Δ; fsetdec.
  -
    simpl in Hftv. eapply IHad_partial_precise; eauto.
  -
    eapply IHad_partial_precise; eauto.
    pose proof (ptyp_to_pskl_ftv τ) as Hp.
    pose proof (Hdef _ _ H) as Hd. clear - Hp Hd; fsetdec.
  -
    inversion Heq; subst.
    pose proof (binds_unique _ _ _ _ _ H HXb (a_wf_aenv_uniq Hwf)) as Habs.
    discriminate Habs.
Qed.

Lemma ad_ppre_delta_var_inv : forall Θ Δ Ψ P ψ,
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  forall α', ψ = uskl_var_f α' ->
  {{ ⊢ Θ }}a ->
  α' `in` Δ ->
  binds α' abind_tvar Θ ->
  (forall α τ, binds α (abind_flex_mono_def τ) Θ ->
     α' `notin` ftvar_in_ptyp τ) ->
  α' `notin` pskl_shielded_ftv P ->
  P = pskl_var_f α' /\ Ψ [=] empty.
Proof.
  intros Θ Δ Ψ P ψ H; induction H;
    intros α0 Heq Hwf HαΔ HXb Hdef Hsh; try discriminate Heq.
  -
    inversion Heq; subst. split; [ reflexivity | assumption ].
  -
    exfalso. subst ψ. simpl in H0. clear - H0 HαΔ; fsetdec.
  -
    exfalso. simpl in Hsh.
    eapply ad_ppre_var_target_absent; eauto.
  -
    exfalso.
    eapply (ad_ppre_var_target_absent H0 Heq Hwf HαΔ HXb Hdef).
    pose proof (ptyp_to_pskl_ftv τ) as Hp.
    pose proof (Hdef _ _ H) as Hd. clear - Hp Hd; fsetdec.
  -
    exfalso. inversion Heq; subst.
    pose proof (binds_unique _ _ _ _ _ H HXb (a_wf_aenv_uniq Hwf)) as Habs.
    discriminate Habs.
Qed.

Lemma a_flex_cons : forall b bd Θ P, a_flex Θ P -> a_flex ((b ~ bd) ++ Θ) P.
Proof.
  intros b bd Θ P H; inversion H; subst;
    [ apply a_flex__var with (α := α)
    | apply a_flex__var_def with (α := α) (τ := τ) ];
    unfold binds; simpl; right; assumption.
Qed.

Lemma a_flex_strip_tvar : forall b Θ P,
  a_flex ((b ~ abind_tvar) ++ Θ) P -> a_flex Θ P.
Proof.
  intros b Θ P H; inversion H; subst;
    match goal with Hb : binds _ _ _ |- _ =>
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq Habs] | Hb'];
        [ discriminate Habs | ] end;
    [ apply a_flex__var with (α := α)
    | apply a_flex__var_def with (α := α) (τ := τ) ]; assumption.
Qed.

Lemma a_flex_tvar_app_mono : forall Ξ Θ Θ' α,
  (forall a, a_flex_tvar Θ a -> a_flex_tvar Θ' a) ->
  a_flex_tvar (Ξ ++ Θ) α -> a_flex_tvar (Ξ ++ Θ') α.
Proof.
  intros * Hm. rewrite !a_flex_tvar_app_iff. intuition auto.
Qed.

Lemma a_flex_app_weaken : forall Ξ Θ P, a_flex Θ P -> a_flex (Ξ ++ Θ) P.
Proof.
  intros Ξ Θ P H; inversion H; subst;
    [ apply a_flex__var with (α := α)
    | apply a_flex__var_def with (α := α) (τ := τ) ];
    apply binds_app_3; assumption.
Qed.

Lemma a_flex_app_anti : forall Ξ Θ Θ' P,
  (forall p, a_flex Θ' p -> a_flex Θ p) ->
  a_flex (Ξ ++ Θ') P -> a_flex (Ξ ++ Θ) P.
Proof.
  intros Ξ Θ Θ' P Hl H; inversion H; subst;
    match goal with Hb : binds ?a ?bd (Ξ ++ Θ') |- _ =>
      destruct (binds_app_1 _ _ _ _ _ Hb) as [HbΞ | HbΘ] end.
  - apply a_flex__var with (α := α); apply binds_app_2; exact HbΞ.
  - apply a_flex_app_weaken. apply Hl.
    apply a_flex__var with (α := α); exact HbΘ.
  - apply a_flex__var_def with (α := α) (τ := τ); apply binds_app_2; exact HbΞ.
  - apply a_flex_app_weaken. apply Hl.
    apply a_flex__var_def with (α := α) (τ := τ); exact HbΘ.
Qed.

Ltac solve_ctx_change_ih :=
  match goal with
  | IH : forall Th2, ftvar_in_aenv Th2 [<=] _ -> _ |- _ =>
      apply IH;
        [ match goal with Hf : ftvar_in_aenv _ [<=] _ |- _ =>
            simpl; clear - Hf; fsetdec end
        | intros α0 Hft; apply a_flex_tvar_weaken_app;
          match goal with Hm : forall a, a_flex_tvar _ a -> _ |- _ =>
            apply Hm; eapply a_flex_tvar_strip_tvar; exact Hft end
        | intros P0 Hf0; apply a_flex_cons;
          match goal with Hl : forall p, a_flex _ p -> _ |- _ =>
            apply Hl; eapply a_flex_strip_tvar; exact Hf0 end ]
  end.

Ltac solve_ctx_change_ih_here :=
  match goal with
  | IH : forall Th2, ftvar_in_aenv Th2 [<=] _ -> _ |- _ =>
      apply IH; assumption
  end.

Ltac solve_ctx_change_ih_app :=
  match goal with
  | IH : forall Th2, ftvar_in_aenv Th2 [<=] ftvar_in_aenv (?X ++ _) -> _ |- _ =>
      apply IH;
        [ match goal with Hf : ftvar_in_aenv _ [<=] _ |- _ =>
            rewrite ! ftvar_in_aenv_app; clear - Hf; fsetdec end
        | intros α0 Hft;
          match goal with Hm : forall a, a_flex_tvar _ a -> _ |- _ =>
            eapply a_flex_tvar_app_mono; [ exact Hm | exact Hft ] end
        | intros P0 Hf0;
          match goal with Hl : forall p, a_flex _ p -> _ |- _ =>
            eapply a_flex_app_anti; [ exact Hl | exact Hf0 ] end ]
  end.

Ltac solve_ctx_change_binder :=
  econstructor;
  [ match goal with
    | Hfr : _ `notin` _ , Hf : ftvar_in_aenv _ [<=] _ |- _ =>
        clear - Hfr Hf; fsetdec
    end
  | solve_ctx_change_ih ].

Lemma a_solve_sub_eq_ctx_change :
  (forall Θ m P P3 Ξ P', {{ Θ ⊢ₛ P ≼[ m ] P3 ⤳ Ξ ⨾ P' }}a ->
     forall Θ',
     ftvar_in_aenv Θ' [<=] ftvar_in_aenv Θ ->
     (forall α, a_flex_tvar Θ α -> a_flex_tvar Θ' α) ->
     (forall P0, a_flex Θ' P0 -> a_flex Θ P0) ->
     {{ Θ' ⊢ₛ P ≼[ m ] P3 ⤳ Ξ ⨾ P' }}a) /\
  (forall Θ P P3 Ξ P', {{ Θ ⊢ₑ P ∼ P3 ⤳ Ξ ⨾ P' }}a ->
     forall Θ',
     ftvar_in_aenv Θ' [<=] ftvar_in_aenv Θ ->
     (forall α, a_flex_tvar Θ α -> a_flex_tvar Θ' α) ->
     (forall P0, a_flex Θ' P0 -> a_flex Θ P0) ->
     {{ Θ' ⊢ₑ P ∼ P3 ⤳ Ξ ⨾ P' }}a).
Proof.
  apply a_solve_sub_eq_mutind; intros;

    try solve [ solve_ctx_change_binder ];
    try solve
      [ match goal with
        | Hfr : ?b `notin` _ |- {{ _ ⊢ₛ _ ≼[ _ ] pskl_all_syn _ ⤳ _ ⨾ _ }}a =>
            apply a_solve_sub__forall_r with (β := b); [ | | | ];
            [ assumption
            | assumption
            | match goal with Hf : ftvar_in_aenv _ [<=] _ |- _ =>
                clear - Hfr Hf; fsetdec end
            | solve_ctx_change_ih ]
        end ];

    try solve
      [ econstructor;
        [ solve_ctx_change_ih_here
        | solve_ctx_change_ih_app ] ];
    try solve
      [ match goal with
        | Hb : a_flex_tvar _ _, Hnf : a_non_flex _ _,
          Hng : nonghost_pskl _,
          Hgu : a_guess_mono _ _ _ _,
          Hf : ftvar_in_aenv _ [<=] _,
          Hmono : forall a, a_flex_tvar _ a -> _,
          Hfl : forall p, a_flex _ p -> _ |- _ =>
            destruct Hnf as [Hlc Hnf'];
            apply a_solve_eq__flex_r;
              [ apply Hmono; exact Hb
              | split; [ exact Hlc | intro Hf0; exact (Hnf' (Hfl _ Hf0)) ]
              | exact Hng
              | eapply a_guess_mono_ctx_shrink; eassumption ]
        end ];

    try solve [ econstructor; eauto ].
Qed.

Lemma a_solve_eq_strengthen_tvar : forall β Θ0 P P3 Ξ P',
  {{ ((β ~ abind_tvar) ++ Θ0) ⊢ₑ P ∼ P3 ⤳ Ξ ⨾ P' }}a ->
  {{ Θ0 ⊢ₑ P ∼ P3 ⤳ Ξ ⨾ P' }}a.
Proof.
  intros β Θ0 P P3 Ξ P' H.
  eapply (proj2 a_solve_sub_eq_ctx_change); [ exact H | | | ].
  - simpl. fsetdec.
  - intros α Hft. eapply a_flex_tvar_strip_tvar; exact Hft.
  - intros P0 Hf. apply (a_flex_cons β abind_tvar); exact Hf.
Qed.

Lemma ad_refine_syn_ghost_sskl : forall Θ Δ Qh Q,
  {{ Θ ⨟ Δ ⊢ᵣ Qh ⊳ Q }}ad ->
  Qh = bskl_ghost ->
  lc_bskl Q ->
  is_sskl Q.
Proof.
  intros Θ Δ Qh Q H; induction H; intros Heq Hlc; try discriminate Heq.
  -
    apply is_sskl_pskl_to_bskl_syn.
    rewrite <- (bskl_to_pskl_pskl_to_bskl_syn P).
    apply lc_bskl_to_pskl; exact Hlc.
  -
    auto with fresco.
Qed.

Lemma ad_pat_consis_sskl_tags : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  {{ ⊢ Θ }}a ->
  is_sskl Q ->
  Ψ [=] empty.
Proof.
  intros Ψ Θ R Q H; induction H; intros Hwf Hsk;
    try solve [ assumption | inversion Hsk ].
  -
    inversion Hsk; subst.
    specialize (IHad_pat_consis1 Hwf ltac:(assumption)).
    specialize (IHad_pat_consis2 Hwf ltac:(assumption)).
    fsetdec.
  -
    inversion Hsk; subst.
    match goal with HskB : forall α, α `notin` ?L0 -> is_sskl _ |- _ =>
      pick fresh α for (L `union` L0 `union` dom Θ);
      apply (H0 α ltac:(solve_notin_auto));
      [ apply a_wf_aenv__tvar; [ fsetdec | exact Hwf ]
      | apply HskB; fsetdec ]
    end.
  -
    inversion Hsk; subst.
    match goal with HskB : forall α, α `notin` ?L0 -> is_sskl _ |- _ =>
      pick fresh α for (L `union` L0 `union` dom Θ);
      apply (H0 α ltac:(solve_notin_auto));
      [ apply a_wf_aenv__tvar; [ fsetdec | exact Hwf ]
      | apply HskB; fsetdec ]
    end.
  -
    inversion Hsk; subst. apply IHad_pat_consis; assumption.
  -
    inversion Hsk; subst. apply IHad_pat_consis; assumption.
  -
    apply IHad_pat_consis; assumption.
  -
    apply IHad_pat_consis; assumption.
  -
    apply IHad_pat_consis; [ assumption | ].
    unfold ptyp_to_bskl_syn.
    apply is_sskl_pskl_to_bskl_syn.
    apply ptyp_to_pskl_lc.
    eapply a_wf_ptyp_lc.
    eapply a_wf_aenv_binds_def_wf; eassumption.
Qed.

Lemma pskl_shielded_ftv_open_rec_lower : forall P P' k,
  pskl_shielded_ftv P [<=]
  pskl_shielded_ftv (open_pskl_wrt_pskl_rec k P' P).
Proof.
  induction P; intros P' k; simpl; try fsetdec.
  - pose proof (IHP1 P' k); pose proof (IHP2 P' k); fsetdec.
  - apply IHP.
  - pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_rec_lower P P' k); fsetdec.
Qed.

Lemma pskl_shielded_ftv_open_rec_upper : forall P P' k,
  pskl_shielded_ftv (open_pskl_wrt_pskl_rec k P' P) [<=]
  pskl_shielded_ftv P `union` ftvar_in_pskl P'.
Proof.
  induction P; intros P' k; simpl; try fsetdec.
  -
    destruct (lt_eq_lt_dec n k) as [[Hlt | Heq] | Hgt]; simpl;
      try fsetdec.
    pose proof (pskl_shielded_ftv_sub_ftv P'); fsetdec.
  - pose proof (IHP1 P' k); pose proof (IHP2 P' k); fsetdec.
  - apply IHP.
  - pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_rec_upper P P' k); fsetdec.
Qed.

Lemma pskl_shielded_ftv_open_lower : forall P P',
  pskl_shielded_ftv P [<=]
  pskl_shielded_ftv (open_pskl_wrt_pskl P P').
Proof. intros; apply pskl_shielded_ftv_open_rec_lower. Qed.

Lemma pskl_shielded_ftv_open_upper : forall P P',
  pskl_shielded_ftv (open_pskl_wrt_pskl P P') [<=]
  pskl_shielded_ftv P `union` ftvar_in_pskl P'.
Proof. intros; apply pskl_shielded_ftv_open_rec_upper. Qed.

Lemma pskl_shielded_ftv_ptyp_to_pskl : forall A,
  pskl_shielded_ftv (ptyp_to_pskl A) [=] {}.
Proof. induction A; simpl; fsetdec. Qed.

Lemma msubst_pskl_shielded_avoid : forall κ P α',
  (forall p, In p κ -> α' `notin` ftvar_in_ptyp (snd p)) ->
  α' `notin` pskl_shielded_ftv P ->
  α' `notin` pskl_shielded_ftv (msubst_pskl κ P).
Proof.
  intros κ P α' Hav.
  induction P as [ | n | β | Pa IHa Pb IHb | Pall IHall | | Pt IHt ];
    intros Hni Hα; simpl in *.
  - fsetdec.
  - fsetdec.
  -
    pose proof (pskl_shielded_ftv_ptyp_to_pskl (msubst_lookup κ β)) as He.
    clear - He Hα; fsetdec.
  - apply union_1 in Hα; destruct Hα as [Hα | Hα];
      [ apply IHa | apply IHb ];
      solve [ clear - Hni; fsetdec | exact Hα ].
  - apply IHall; eassumption.
  - fsetdec.
  -
    revert Hα. apply msubst_pskl_ftv_avoid; eassumption.
Qed.

Lemma msubst_pskl_var_inv : forall κ Pi α',
  (forall p, In p κ -> α' `notin` ftvar_in_ptyp (snd p)) ->
  msubst_pskl κ Pi = pskl_var_f α' ->
  Pi = pskl_var_f α'.
Proof.
  intros κ Pi α' Hav Heq.
  destruct Pi as [ | n | β | | | | ]; simpl in Heq; try discriminate Heq.
  f_equal.
  assert (Hα : α' `in` ftvar_in_ptyp (msubst_lookup κ β)).
  { pose proof (ftvar_ptyp_to_pskl (msubst_lookup κ β)) as Hp.
    rewrite Heq in Hp. simpl in Hp. clear - Hp; fsetdec. }
  eapply msubst_lookup_ftv_avoid; eassumption.
Qed.

Lemma a_solve_eq_ghost_subject_inv : forall Θ P Ξ P',
  {{ Θ ⊢ₑ pskl_ghost ∼ P ⤳ Ξ ⨾ P' }}a ->
  Ξ = nil /\ P' = P.
Proof.
  intros Θ P Ξ P' H; inversion H; subst; try solve [ split; reflexivity ];
    try solve [ match goal with H0 : nonghost_pskl pskl_ghost |- _ =>
                  inversion H0 end ];
    inv_guarded_ghost.
Qed.

Lemma uskl_rsubst_arrow_r_inv : forall NM Θ Δρ Ψρ R' ψ1 ψ2,
  uskl_rsubst NM Θ Δρ Ψρ R' (uskl_arrow ψ1 ψ2) ->
  exists R1' R2' Ψ1 Ψ2,
    R' = uskl_arrow R1' R2' /\
    uskl_rsubst NM Θ Δρ Ψ1 R1' ψ1 /\ uskl_rsubst NM Θ Δρ Ψ2 R2' ψ2 /\
    Ψρ [=] Ψ1 `union` Ψ2.
Proof.
  intros NM Θ Δρ Ψρ R' ψ1 ψ2 H; inversion H; subst.
  -
    match goal with Hlc : lc_uskl (uskl_arrow _ _) |- _ =>
      inversion Hlc; subst end.
    exists ψ1, ψ2, empty, empty; rho_andsplit;
      [ reflexivity
      | apply ursubst__refl; [ assumption | clear; fsetdec ]
      | apply ursubst__refl; [ assumption | clear; fsetdec ]
      | clear - H1; fsetdec ].
  - exists R1', R2', Ψ1, Ψ2; rho_andsplit;
      try reflexivity; assumption.
Qed.

Lemma uskl_rsubst_univ_ghost_r_inv : forall NM Θ Δρ Ψρ R' ψ,
  uskl_rsubst NM Θ Δρ Ψρ R' (uskl_univ_ghost ψ) ->
  exists R0, R' = uskl_univ_ghost R0 /\ uskl_rsubst NM Θ Δρ Ψρ R0 ψ.
Proof.
  intros NM Θ Δρ Ψρ R' ψ H; inversion H; subst.
  - match goal with Hlc : lc_uskl (uskl_univ_ghost _) |- _ =>
      inversion Hlc; subst end.
    exists ψ; split;
      [ reflexivity | apply ursubst__refl; assumption ].
  - exists R'0; split; [ reflexivity | assumption ].
Qed.

Lemma uskl_rsubst_dot_univ_ghost_r_inv : forall NM Θ Δρ Ψρ R' ψ,
  uskl_rsubst NM Θ Δρ Ψρ R' (uskl_dot_univ_ghost ψ) ->
  exists R0, R' = uskl_dot_univ_ghost R0 /\ uskl_rsubst NM Θ Δρ Ψρ R0 ψ.
Proof.
  intros NM Θ Δρ Ψρ R' ψ H; inversion H; subst.
  - match goal with Hlc : lc_uskl (uskl_dot_univ_ghost _) |- _ =>
      inversion Hlc; subst end.
    exists ψ; split;
      [ reflexivity | apply ursubst__refl; assumption ].
  - exists R'0; split; [ reflexivity | assumption ].
Qed.

Lemma uskl_rsubst_all_syn_r_inv : forall NM Θ Δρ Ψρ R' ψ,
  uskl_rsubst NM Θ Δρ Ψρ R' (uskl_all_syn ψ) ->
  exists L R0, R' = uskl_all_syn R0 /\
    forall α, α `notin` L ->
      uskl_rsubst NM Θ Δρ Ψρ (open_uskl_wrt_uskl R0 (uskl_var_f α))
                          (open_uskl_wrt_uskl ψ (uskl_var_f α)).
Proof.
  intros NM Θ Δρ Ψρ R' ψ H; inversion H; subst.
  - match goal with Hlc : lc_uskl (uskl_all_syn _) |- _ =>
      inversion Hlc; subst end.
    exists empty, ψ; split; [ reflexivity | ].
    intros α Hα; apply ursubst__refl; [ auto | assumption ].
  - exists L, R'0; split; [ reflexivity | eassumption ].
Qed.

Lemma uskl_rsubst_all_tag_r_inv : forall NM Θ Δρ Ψρ R' ε ψ,
  uskl_rsubst NM Θ Δρ Ψρ R' (uskl_all_tag ε ψ) ->
  exists L R0, R' = uskl_all_tag ε R0 /\
    forall α, α `notin` L ->
      uskl_rsubst NM Θ Δρ Ψρ (open_uskl_wrt_uskl R0 (uskl_var_f α))
                          (open_uskl_wrt_uskl ψ (uskl_var_f α)).
Proof.
  intros NM Θ Δρ Ψρ R' ε ψ H; inversion H; subst.
  - match goal with Hlc : lc_uskl (uskl_all_tag _ _) |- _ =>
      inversion Hlc; subst end.
    exists empty, ψ; split; [ reflexivity | ].
    intros α Hα; apply ursubst__refl; [ auto | assumption ].
  - exists L, R'0; split; [ reflexivity | eassumption ].
Qed.

Lemma uskl_rsubst_is_dskl : forall NM Θ Δρ Ψρ R' R,
  uskl_rsubst NM Θ Δρ Ψρ R' R ->
  is_dskl R ->
  is_dskl R'.
Proof.
  intros NM Θ Δρ Ψρ R' R H; induction H; intros Ht.
  - exact Ht.
  -
    inversion H0; assumption.
  - inversion Ht; subst; apply is_dskl__arrow; auto.
  -  inversion Ht.
  -
    inversion Ht; subst.
    match goal with Hb : forall α, α `notin` ?L1 -> is_dskl _ |- _ =>
      apply is_dskl__all_tag with (L := L `union` L1); intros α Hα;
      apply H0; [ clear - Hα; solve_notin | apply Hb; clear - Hα; solve_notin ]
    end.
  -  inversion Ht.
  - inversion Ht; subst; apply is_dskl__dot_univ_ghost; auto.
Qed.

Lemma uskl_rsubst_ftv_subject_bound : forall NM Θ Δρ Ψρ R' R,
  uskl_rsubst NM Θ Δρ Ψρ R' R ->
  ftvar_in_uskl R' [<=] ftvar_in_uskl R `union` dom Θ.
Proof.
  intros NM Θ Δρ Ψρ R' R H; induction H; cbn [ftvar_in_uskl];
    try solve [ clear; fsetdec | clear - IHuskl_rsubst; fsetdec
              | clear - IHuskl_rsubst1 IHuskl_rsubst2; fsetdec ].
  -
    pose proof (a_wf_pskl_ftv_dom H1) as Hd.

    rewrite ftvar_in_pskl_uskl_to_pskl in Hd. clear - Hd; fsetdec.
  -
    pick fresh α for (L `union` ftvar_in_uskl R' `union` ftvar_in_uskl R).
    pose proof (H0 α ltac:(clear - Fr; solve_notin)) as Hα.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R' (uskl_var_f α)).
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R (uskl_var_f α)).
    cbn [ftvar_in_uskl] in *. clear - Hα H1 H2 Fr. fsetdec.
  -
    pick fresh α for (L `union` ftvar_in_uskl R' `union` ftvar_in_uskl R).
    pose proof (H0 α ltac:(clear - Fr; solve_notin)) as Hα.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R' (uskl_var_f α)).
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R (uskl_var_f α)).
    cbn [ftvar_in_uskl] in *. clear - Hα H1 H2 Fr. fsetdec.
Qed.

Lemma uskl_rsubst_ftv_apart : forall NM Θ Δρ Ψρ R' R,
  uskl_rsubst NM Θ Δρ Ψρ R' R ->
  (ftvar_in_uskl R) ∩ Δρ [=] empty ->
  ftvar_in_uskl R' [<=] ftvar_in_uskl R.
Proof.
  intros NM Θ Δρ Ψρ R' R H; induction H; intros Hap; cbn [ftvar_in_uskl] in *;
    try solve [ clear; fsetdec
              | apply IHuskl_rsubst; clear - Hap; fsetdec
              |
                pose proof (IHuskl_rsubst1 ltac:(clear - Hap; solve_notin_auto));
                pose proof (IHuskl_rsubst2 ltac:(clear - Hap; solve_notin_auto));
                clear - H2 H3; fsetdec ].
  -
    exfalso. clear - H Hap; fsetdec.
  -
    pick fresh α for (L `union` Δρ `union` ftvar_in_uskl R'
                        `union` ftvar_in_uskl R).
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R' (uskl_var_f α)) as Hlo.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R (uskl_var_f α)) as Hup.
    cbn [ftvar_in_uskl] in Hup.
    pose proof (H0 α ltac:(clear - Fr; solve_notin)
                  ltac:(clear - Hap Hup Fr; solve_notin_auto)) as Hα.
    clear - Hα Hlo Hup Fr; fsetdec.
  -
    pick fresh α for (L `union` Δρ `union` ftvar_in_uskl R'
                        `union` ftvar_in_uskl R).
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R' (uskl_var_f α)) as Hlo.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R (uskl_var_f α)) as Hup.
    cbn [ftvar_in_uskl] in Hup.
    pose proof (H0 α ltac:(clear - Fr; solve_notin)
                  ltac:(clear - Hap Hup Fr; solve_notin_auto)) as Hα.
    clear - Hα Hlo Hup Fr; fsetdec.
Qed.

Lemma uskl_rsubst_weaken : forall NM Θ Δρ Ψρ R' R,
  uskl_rsubst NM Θ Δρ Ψρ R' R ->
  forall Θ', (forall x b, binds x b Θ -> binds x b Θ') ->
  uskl_rsubst NM Θ' Δρ Ψρ R' R.
Proof.
  intros NM Θ Δρ Ψρ R' R H; induction H; intros Θ' Hmon.
  - apply ursubst__refl; assumption.
  - eapply ursubst__leaf; [ exact H | exact H0 | | exact H2 ].
    eapply a_wf_pskl_weaken; eassumption.
  - eapply ursubst__arrow; eauto.
  - eapply ursubst__all_syn with (L := L); eauto.
  - eapply ursubst__all_tag with (L := L); eauto.
  - apply ursubst__univ_ghost; eauto.
  - apply ursubst__dot_univ_ghost; eauto.
Qed.

Lemma ad_partial_precise_strengthen_tvar_mid : forall Θfull Δ Ψ P ψ,
  {{ Θfull ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  forall α1 Θ1 Θ0,
  Θfull = Θ1 ++ (α1 ~ abind_tvar) ++ Θ0 ->
  {{ (Θ1 ++ Θ0) ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad.
Proof.
  intros Θfull Δ Ψ P ψ H; induction H; intros α1 Θ1 Θ0 Heq; subst.
  - apply ad_ppre__unit; assumption.
  - apply ad_ppre__var; assumption.
  - eapply ad_ppre__arrow;
      [ apply (IHad_partial_precise1 α1 Θ1 Θ0 eq_refl)
      | apply (IHad_partial_precise2 α1 Θ1 Θ0 eq_refl)
      | assumption ].
  - eapply ad_ppre__forall with (L := L);
      [ intros α Hα;
        apply (H0 α Hα α1 ((α ~ abind_tvar) ++ Θ1) Θ0 eq_refl)
      | assumption ].
  - apply ad_ppre__ghost; assumption.
  - apply ad_ppre__univ_ghost_remove.
    apply (IHad_partial_precise α1 Θ1 Θ0 eq_refl).
  - eapply ad_ppre__univ_ghost_fill with (L := L).
    intros α Hα.
    apply (H0 α Hα α1 ((α ~ abind_tvar) ++ Θ1) Θ0 eq_refl).
  - apply ad_ppre__univ_ghost_keep.
    apply (IHad_partial_precise α1 Θ1 Θ0 eq_refl).
  - eapply ad_ppre__flex_l;
      [ eapply binds_strip_mid;
        [ exact H | intro Habs; inversion Habs ]
      | apply (IHad_partial_precise α1 Θ1 Θ0 eq_refl) ].
  - eapply ad_ppre__flex_r;
      [ eapply binds_strip_mid;
        [ exact H | intro Habs; inversion Habs ]
      | apply (IHad_partial_precise α1 Θ1 Θ0 eq_refl) ].
Qed.

Lemma ad_partial_precise_strengthen_tvar : forall α1 Θ0 Δ Ψ P ψ,
  {{ ((α1 ~ abind_tvar) ++ Θ0) ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  {{ Θ0 ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad.
Proof.
  intros α1 Θ0 Δ Ψ P ψ H.
  exact (@ad_partial_precise_strengthen_tvar_mid _ _ _ _ _ H α1 nil Θ0 eq_refl).
Qed.

Lemma binds_mid_to_front : forall x (b b0 : abind) (Ξ Θ : aenv) β,
  binds x b (Ξ ++ (β ~ b0) ++ Θ) -> binds x b ((β ~ b0) ++ Ξ ++ Θ).
Proof.
  unfold binds; intros x b b0 Ξ Θ β H.
  rewrite !in_app_iff in *; simpl in *. tauto.
Qed.

Lemma a_wf_pskl_all_of_one_at : forall Θ Δ P β,
  {{ ((β ~ abind_tvar) ++ Θ) ⨟ (add β Δ) ⊢ₚₛ
     (open_pskl_wrt_pskl P (pskl_var_f β)) }}a ->
  β `notin` ftvar_in_pskl P ->
  {{ Θ ⨟ Δ ⊢ₚₛ (pskl_all_syn P) }}a.
Proof.
  intros Θ Δ P β H HβP.
  apply a_wf_pskl__all with (L := add β (ftvar_in_pskl P `union` Δ)).
  intros α Hα.
  pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β)) as Hupβ.
  pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f α)) as Hupα.
  simpl in Hupβ, Hupα.
  assert (Hr : {{ ((α ~ abind_tvar) ++ Θ) ⨟ (add α (remove β (add β Δ))) ⊢ₚₛ
                  (subst_pskl_in_pskl (pskl_var_f α) β
                     (open_pskl_wrt_pskl P (pskl_var_f β))) }}a).
  { eapply a_wf_pskl_rename_bound; [ exact H | | | | ].
    - intros γ Hγ Hne. apply a_binds_tvar_cons_tvar.
      destruct (a_binds_tvar_cons_tvar_inv Hγ) as [-> | Hγ'];
        [ contradiction | right; exact Hγ' ].
    - apply a_binds_tvar_cons_tvar. left; reflexivity.
    - clear; fsetdec.
    - clear - Hα Hupβ; fsetdec. }
  rewrite <- (subst_pskl_in_pskl_intro β P (pskl_var_f α) HβP) in Hr.
  eapply a_wf_pskl_delta_mono; [ exact Hr | ].
  intros γ Hγ Hγin.
  assert (γ <> β) by (intro; subst; clear - Hγ Hupα Hα HβP; fsetdec).
  clear - Hγin H0. fsetdec.
Qed.

Lemma a_wf_pskl_cons_tvar_fresh : forall Θ Δ P β,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  β `notin` ftvar_in_pskl P ->
  {{ ((β ~ abind_tvar) ++ Θ) ⨟ (add β Δ) ⊢ₚₛ P }}a.
Proof.
  intros Θ Δ P β H Hβ.
  eapply a_wf_pskl_delta_mono.
  - eapply a_wf_pskl_tvar_mono; [ exact H | ].
    intros γ Hγ. apply a_binds_tvar_cons_tvar. right; exact Hγ.
  - intros γ Hγ Hin.
    assert (γ <> β) by (intro; subst; contradiction).
    clear - Hin H0. fsetdec.
Qed.

Lemma a_wf_pskl_ghost_free_delta : forall Θ Δ0 P,
  {{ Θ ⨟ Δ0 ⊢ₚₛ P }}a ->
  pskl_ghost_free P ->
  forall Δ, {{ Θ ⨟ Δ ⊢ₚₛ P }}a.
Proof.
  intros Θ Δ0 P H; induction H; intros Hgf Δ'; simpl in Hgf;
    try contradiction.
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var; assumption.
  - destruct Hgf. apply a_wf_pskl__arrow; auto.
  - apply a_wf_pskl__all with (L := L). intros α Hα.
    apply H0; [ exact Hα | apply pskl_ghost_free_open; exact Hgf ].
Qed.

Lemma a_wf_pskl_shielded_dom : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a -> pskl_shielded_ftv P [<=] dom Θ.
Proof.
  intros Θ Δ P H; induction H; cbn [pskl_shielded_ftv];
    try solve [ clear; fsetdec | clear - IHa_wf_pskl1 IHa_wf_pskl2; fsetdec ].
  -
    pick fresh α for (L `union` dom Θ `union` ftvar_in_pskl P `union` Δ).
    pose proof (H0 α ltac:(clear - Fr; solve_notin_auto)) as Hb.
    pose proof (pskl_shielded_ftv_open_lower P (pskl_var_f α)) as Hlo.
    pose proof (pskl_shielded_ftv_sub_ftv P) as Hsf.
    simpl in Hb.
    assert (HαP : α `notin` ftvar_in_pskl P) by (clear - Fr; solve_notin_auto).
    clear - Hb Hlo Hsf HαP; fsetdec.
  -
    pose proof (a_wf_pskl_ftv_dom H0) as Hd.
    intros γ Hγ.
    assert (Hγd : γ `in` dom (aenv_minus Θ Δ)) by (clear - Hd Hγ; fsetdec).
    destruct (@dom_aenv_minus γ Θ Δ Hγd) as [Hγ' _]. exact Hγ'.
Qed.

Lemma list_app_assoc : forall (A : Type) (X Y Z : list A),
  (X ++ Y) ++ Z = X ++ (Y ++ Z).
Proof. intros A X Y Z; induction X as [| p X IH]; simpl; f_equal; auto. Qed.

Notation aenv_app_assoc := (@list_app_assoc (atom * abind)).

Lemma a_wf_pskl_app_weaken : forall Ξ Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a -> {{ (Ξ ++ Θ) ⨟ Δ ⊢ₚₛ P }}a.
Proof.
  intros Ξ Θ Δ P H.
  eapply a_wf_pskl_weaken; [ | exact H ].
  intros x b Hb. apply binds_app_3; exact Hb.
Qed.

Lemma a_guess_mono_wf_pskl : forall Θ P Ξ A,
  a_guess_mono Θ P Ξ A ->
  forall Δ, {{ Θ ⨟ Δ ⊢ₚₛ P }}a -> {{ (Ξ ++ Θ) ⨟ Δ ⊢ₚₛ (ptyp_to_pskl A) }}a.
Proof.
  intros Θ P Ξ A H; induction H; intros Δ Hwf; cbn [ptyp_to_pskl].
  -
    simpl. apply a_wf_pskl__var. right. left.
    unfold binds; simpl; auto.
  -
    destruct (a_wf_pskl_univ_ghost_inv Hwf) as [_ Hwf0].
    apply (a_wf_pskl_ghost_free_delta (IHa_guess_mono empty Hwf0)).
    apply ptyp_to_pskl_ghost_free.
  -
    simpl. exact Hwf.
  - simpl. apply a_wf_pskl__unit.
  -
    inversion Hwf; subst.
    apply a_wf_pskl__arrow.
    + eapply a_wf_pskl_weaken;
        [ | exact (IHa_guess_mono1 Δ ltac:(assumption)) ].
      intros x b Hb.
      destruct (binds_app_1 _ _ _ _ _ Hb) as [HbΞ | HbΘ];
        [ apply binds_app_2; apply binds_app_2; exact HbΞ
        | apply binds_app_3; exact HbΘ ].
    + eapply a_wf_pskl_weaken;
        [ | exact (IHa_guess_mono2 Δ ltac:(assumption)) ].
      intros x b Hb.
      destruct (binds_app_1 _ _ _ _ _ Hb) as [HbΞ | HbΘ];
        [ apply binds_app_2; apply binds_app_3; exact HbΞ
        | apply binds_app_3; exact HbΘ ].
  -
    apply (@a_wf_pskl_all_of_one_at (Ξ ++ Θ) Δ
             (ptyp_to_pskl (close_ptyp_wrt_ptyp β A)) β).
    + rewrite <- ptyp_to_pskl_open.
      rewrite open_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp.
      eapply a_wf_pskl_weaken;
        [ intros x b Hb; eapply binds_mid_to_front; exact Hb | ].
      apply IHa_guess_mono.
      apply a_wf_pskl_all_inv_at; [ exact Hwf | clear - H; fsetdec ].
    + pose proof (ftvar_ptyp_to_pskl (close_ptyp_wrt_ptyp β A)) as Hco.
      pose proof (ftvar_in_ptyp_close_ptyp_wrt_ptyp A β) as Hcl.
      clear - Hco Hcl; fsetdec.
Qed.

Lemma a_solve_eq_wf_gen : forall Θ P P0 Ξ P',
  {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a ->
  forall Δ,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  {{ Θ ⨟ Δ ⊢ₚₛ P0 }}a ->
  Δ ∩ dom Ξ [=] empty ->
  {{ (Ξ ++ Θ) ⨟ Δ ⊢ₚₛ P' }}a.
Proof.
  intros Θ P P0 Ξ P' H; induction H; intros Δ HwfP HwfQ HΔΞ;

    try solve [ cbn [app]; apply a_wf_pskl__unit
              | cbn [app]; exact HwfP
              | cbn [app]; exact HwfQ ].
  -
    eapply a_guess_mono_wf_pskl; eassumption.
  -
    inversion HwfP; subst; inversion HwfQ; subst.
    rewrite dom_app in HΔΞ.
    rewrite aenv_app_assoc.
    apply a_wf_pskl__arrow.
    + eapply a_wf_pskl_weaken;
        [ | exact (IHa_solve_eq1 Δ ltac:(assumption) ltac:(assumption)
                     ltac:(clear - HΔΞ; fsetdec)) ].
      intros x b Hb.
      destruct (binds_app_1 _ _ _ _ _ Hb) as [HbΞ | HbΘ];
        [ apply binds_app_3; apply binds_app_2; exact HbΞ
        | apply binds_app_3; apply binds_app_3; exact HbΘ ].
    + apply IHa_solve_eq2;
        [ apply a_wf_pskl_app_weaken; assumption
        | apply a_wf_pskl_app_weaken; assumption
        | clear - HΔΞ; fsetdec ].
  -
    assert (HβΞ : β `notin` dom Ξ)
      by (eapply a_solve_eq_generated_apart_binder; eassumption).
    apply (@a_wf_pskl_all_of_one_at (Ξ ++ Θ) Δ (close_pskl_wrt_pskl β P') β).
    + rewrite open_pskl_wrt_pskl_close_pskl_wrt_pskl.
      eapply a_wf_pskl_weaken;
        [ intros x b Hb; eapply binds_mid_to_front; exact Hb | ].
      apply IHa_solve_eq;
        [ apply a_wf_pskl_all_inv_at; [ eassumption | clear - H; fsetdec ]
        | apply a_wf_pskl_all_inv_at; [ eassumption | clear - H; fsetdec ]
        | clear - HΔΞ HβΞ; fsetdec ].
    + pose proof (ftvar_in_pskl_close_pskl_wrt_pskl P' β) as Hcl.
      clear - Hcl; fsetdec.
  -
    destruct (a_wf_pskl_univ_ghost_inv HwfP) as [HgP HwfP0].
    destruct (a_wf_pskl_univ_ghost_inv HwfQ) as [HgQ HwfQ0].
    assert (Hw0 : {{ (Ξ ++ Θ) ⨟ empty ⊢ₚₛ P' }}a)
      by (apply IHa_solve_eq; [ exact HwfP0 | exact HwfQ0 | clear; fsetdec ]).
    apply a_wf_pskl__univ_ghost.
    + eapply (proj2 a_solve_sub_eq_guarded);
        eauto using a_wf_pskl_lc.
    + eapply a_wf_pskl_tvar_mono_ftv; [ exact Hw0 | ].
      intros γ Hγ Hb. apply a_binds_tvar_aenv_minus. split; [ exact Hb | ].
      pose proof (a_solve_eq_ftv H) as Hft.
      inversion HwfP; subst. inversion HwfQ; subst.
      assert (HnP : γ `in` ftvar_in_pskl P -> γ `notin` Δ).
      { intros Hin.
        match goal with
        | Hb0 : {{ aenv_minus _ _ ⨟ _ ⊢ₚₛ P }}a |- _ =>
            pose proof (a_wf_pskl_ftv_binds Hb0) as Hx
        end.
        specialize (Hx γ Hin). apply a_binds_tvar_aenv_minus in Hx.
        apply Hx. }
      assert (HnQ : γ `in` ftvar_in_pskl Q -> γ `notin` Δ).
      { intros Hin.
        match goal with
        | Hb0 : {{ aenv_minus _ _ ⨟ _ ⊢ₚₛ Q }}a |- _ =>
            pose proof (a_wf_pskl_ftv_binds Hb0) as Hx
        end.
        specialize (Hx γ Hin). apply a_binds_tvar_aenv_minus in Hx.
        apply Hx. }
      destruct (AtomSetProperties.In_dec γ (ftvar_in_pskl P)) as [HiP | HiP];
        [ exact (HnP HiP) | ].
      destruct (AtomSetProperties.In_dec γ (ftvar_in_pskl Q)) as [HiQ | HiQ];
        [ exact (HnQ HiQ) | ].
      clear - Hγ Hft HiP HiQ HΔΞ. fsetdec.
  -
    assert (HβΞ : β `notin` dom Ξ)
      by (eapply a_solve_eq_generated_apart_binder; eassumption).
    apply (@a_wf_pskl_all_of_one_at (Ξ ++ Θ) Δ (close_pskl_wrt_pskl β P') β).
    + rewrite open_pskl_wrt_pskl_close_pskl_wrt_pskl.
      eapply a_wf_pskl_weaken;
        [ intros x b Hb; eapply binds_mid_to_front; exact Hb | ].
      apply IHa_solve_eq;
        [ apply a_wf_pskl_cons_tvar_fresh;
            [ exact HwfP | simpl; clear - H; fsetdec ]
        | apply a_wf_pskl_all_inv_at; [ exact HwfQ | clear - H; fsetdec ]
        | clear - HΔΞ HβΞ; fsetdec ].
    + pose proof (ftvar_in_pskl_close_pskl_wrt_pskl P' β) as Hcl.
      clear - Hcl; fsetdec.
  -
    apply IHa_solve_eq;
      [ apply a_wf_pskl_univ_ghost_body; exact HwfP | exact HwfQ | exact HΔΞ ].
  -
    assert (HβΞ : β `notin` dom Ξ)
      by (eapply a_solve_eq_generated_apart_binder; eassumption).
    apply (@a_wf_pskl_all_of_one_at (Ξ ++ Θ) Δ (close_pskl_wrt_pskl β P') β).
    + rewrite open_pskl_wrt_pskl_close_pskl_wrt_pskl.
      eapply a_wf_pskl_weaken;
        [ intros x b Hb; eapply binds_mid_to_front; exact Hb | ].
      apply IHa_solve_eq;
        [ apply a_wf_pskl_all_inv_at; [ exact HwfP | clear - H; fsetdec ]
        | apply a_wf_pskl_cons_tvar_fresh;
            [ exact HwfQ | simpl; clear - H; fsetdec ]
        | clear - HΔΞ HβΞ; fsetdec ].
    + pose proof (ftvar_in_pskl_close_pskl_wrt_pskl P' β) as Hcl.
      clear - Hcl; fsetdec.
  -
    apply IHa_solve_eq;
      [ exact HwfP | apply a_wf_pskl_univ_ghost_body; exact HwfQ | exact HΔΞ ].
Qed.

Lemma a_solve_eq_wf : forall Θ P P0 Ξ P',
  {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a ->
  {{ Θ ⨟ empty ⊢ₚₛ P }}a ->
  {{ Θ ⨟ empty ⊢ₚₛ P0 }}a ->
  {{ (Ξ ++ Θ) ⨟ empty ⊢ₚₛ P' }}a.
Proof.
  intros * H HwfP HwfQ.
  eapply a_solve_eq_wf_gen; [ exact H | exact HwfP | exact HwfQ | ].
  clear; fsetdec.
Qed.

Lemma pskl_to_bskl_inh_arrow_inv : forall P Q1 Q2,
  pskl_to_bskl_inh P = bskl_arrow Q1 Q2 ->
  exists P1 P2, P = pskl_arrow P1 P2 /\
    pskl_to_bskl_inh P1 = Q1 /\ pskl_to_bskl_inh P2 = Q2.
Proof.
  intros P Q1 Q2 H; destruct P; simpl in H; try discriminate.
  inversion H; subst. exists P1, P2; repeat split; reflexivity.
Qed.

Lemma ad_refine_inh_unit_ppre : forall Θ Δr Qlhs Qrhs,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δr ⊢ᵣ Qlhs ⊳ Qrhs }}ad ->
  Qrhs = bskl_unit ->
  forall P' Δ, Qlhs = pskl_to_bskl_inh P' ->
  {{ Θ ⨟ Δ ⊢ˢ P' ⊑ᵖ[ empty ] uskl_unit }}ad.
Proof.
  intros Θ Δr Qlhs Qrhs Hwf H; induction H; intros HR P' Δo Heq;
    try discriminate HR; subst.
  -
    destruct P'; simpl in Heq; try discriminate Heq.
    apply ad_ppre__unit. fsetdec.
  -
    destruct P'; simpl in Heq; try discriminate Heq.
    apply ad_ppre__ghost; [ fsetdec | simpl; fsetdec ].
  -
    destruct P'; simpl in Heq; try discriminate Heq.
    inversion Heq; subst.
    apply ad_ppre__univ_ghost_remove. eapply IHad_refine_syn; eauto.
  -
    destruct P'; simpl in Heq; try discriminate Heq.
    inversion Heq; subst.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    eapply ad_ppre__flex_l; [ eassumption | ].
    apply (IHad_refine_syn Hwf eq_refl (ptyp_to_pskl τ) Δo).
    symmetry. apply ptyp_to_bskl_inh_syn_eq; assumption.
Qed.

Lemma msubst_pskl_tvar_id : forall Θ0 κ Θ α,
  {{ ⊢ Θ0 }}a ->
  κ ∷ Θ0 ⊑ Θ ->
  binds α abind_tvar Θ0 ->
  msubst_pskl κ (pskl_var_f α) = pskl_var_f α.
Proof.
  intros Θ0 κ Θ α Hwf Hinc Hb.
  simpl. rewrite msubst_lookup_notin; [ reflexivity | ].
  intros Hin. pose proof (a_inc_dom_flex Hinc Hin) as Hfl.
  pose proof (a_wf_aenv_uniq Hwf) as Huniq.
  destruct Hfl as [Hbf | [τ Hbf]];
    pose proof (binds_unique _ _ _ _ _ Hb Hbf Huniq) as Hc; discriminate Hc.
Qed.

Lemma ad_refine_syn_rigid_var_nonvar_absurd : forall Θr Δr β Q,
  {{ Θr ⨟ Δr ⊢ᵣ (bskl_var_f β) ⊳ Q }}ad ->
  forall Θfull, (forall x b, binds x b Θr -> binds x b Θfull) ->
  uniq Θfull ->
  binds β abind_tvar Θfull ->
  (forall β0, Q <> bskl_var_f β0) ->
  False.
Proof.
  intros Θr Δr β Q H; inversion H; subst; intros Θfull Hmon Hu Hb Hnv.
  - eapply Hnv; reflexivity.
  - match goal with Hbd : binds _ (abind_flex_mono_def _) _ |- _ =>
      pose proof (Hmon _ _ Hbd) as Hbd';
      pose proof (binds_unique _ _ _ _ _ Hb Hbd' Hu) as Hc;
      discriminate Hc end.
  - eapply Hnv; reflexivity.
Qed.

Lemma ad_ppre_unit_tags_empty : forall Θ Δ P Ψ,
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] uskl_unit }}ad -> Ψ [=] empty.
Proof.
  intros Θ Δ P Ψ H; remember uskl_unit as u eqn:Hu.
  induction H; try discriminate Hu; subst; auto.
Qed.

Lemma a_solve_eq_unit : forall n Θ0 Θ κ Δ Ψi Pi P0,
  size_pskl Pi + size_pskl P0 <= n ->
  {{ ⊢ Θ }}a -> {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a -> {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  κ ∷ Θ0 ⊑ Θ ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] uskl_unit }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ bskl_unit }}ad ->
  exists Pa, {{ Θ0 ⊢ₑ Pi ∼ P0 ⤳ nil ⨾ Pa }}a /\
             {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pa) ⊑ᵖ[ Ψi ] uskl_unit }}ad.
Proof.
  induction n; intros Θ0 Θ κ Δ Ψi Pi P0 Hn
    HwfΘ HwfΘ0 HwfPi HwfP0 Hκ Hpre Hrefine.
  { pose proof (size_pskl_min Pi); pose proof (size_pskl_min P0); lia. }
  pose proof (ad_ppre_unit_tags_empty Hpre) as HΨi.
  destruct Pi as [ | nb | α | Pi1 Pi2 | Pib | | Pi' ].
  -
    destruct P0 as [ | nb0 | α | P0a P0b | P0b | | P0' ].
    +
      exists pskl_unit; split;
        [ apply a_solve_eq__unit | simpl; apply ad_ppre__unit; exact HΨi ].
    +  inversion HwfP0.
    +
      inversion HwfP0; subst;
      match goal with H : a_binds_tvar α _ |- _ => rename H into Habt end.
      destruct Habt as [Hrig | [Hfm | [τ Hfd]]].
      *
        exfalso.
        assert (Hmid : msubst_pskl κ (pskl_var_f α) = pskl_var_f α)
          by (eapply msubst_pskl_tvar_id; eauto).
        rewrite Hmid in Hrefine; simpl in Hrefine.
        eapply (ad_refine_syn_rigid_var_nonvar_absurd Hrefine);
          [ intros x b Hb; exact Hb | apply a_wf_aenv_uniq; exact HwfΘ
          | eapply a_inc_binds_tvar; eauto | intros β0 Hcc; discriminate Hcc ].
      *
        exists pskl_unit; split.
        -- apply a_solve_eq__flex_r with (A := ptyp_unit);
             [ left; exact Hfm
             | split; [ constructor | intros Hf; inversion Hf ]
             | apply nonghost_pskl__unit
             | apply a_guess_mono__unit ].
        -- simpl. apply ad_ppre__unit. exact HΨi.
      *
        exists pskl_unit; split.
        -- apply a_solve_eq__flex_r with (A := ptyp_unit);
             [ right; exists τ; exact Hfd
             | split; [ constructor | intros Hf; inversion Hf ]
             | apply nonghost_pskl__unit
             | apply a_guess_mono__unit ].
        -- simpl. apply ad_ppre__unit. exact HΨi.
    +
      simpl in Hrefine; inversion Hrefine.
    +
      simpl in Hrefine; inversion Hrefine.
    +
      exists pskl_unit; split; [ apply a_solve_eq__ghost_r | exact Hpre ].
    +
      simpl in Hrefine. inversion Hrefine; subst.
      destruct (a_wf_pskl_univ_ghost_inv HwfP0) as [_ HwfP0t].
      match goal with
      | Href' : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ P0') ⊳ bskl_unit }}ad,
        HwfP0' : {{ _ ⨟ _ ⊢ₚₛ P0' }}a |- _ =>
        destruct (IHn Θ0 Θ κ Δ Ψi pskl_unit P0'
                    ltac:(simpl in Hn; simpl; lia)
                    HwfΘ HwfΘ0 HwfPi HwfP0' Hκ Hpre Href')
          as [Pa [Hsolve Hprec]]
      end.
      exists Pa; split;
        [ apply a_solve_eq__univ_ghost_r_guarded; [ constructor | exact Hsolve ]
        | exact Hprec ].
  -  inversion HwfPi.
  -
    exists (pskl_var_f α); split; [ apply a_solve_eq__var | exact Hpre ].
  -  simpl in Hpre; inversion Hpre.
  -  simpl in Hpre; inversion Hpre.
  -
    exists P0; split;
      [ apply a_solve_eq__ghost_l
      | eapply ad_partial_precise_psi_cong;
          [ eapply ad_refine_inh_unit_ppre;
              [ exact HwfΘ | exact Hrefine | reflexivity | reflexivity ]
          | clear - HΨi; fsetdec ] ].
  -
    simpl in Hpre. inversion Hpre; subst.
    inversion HwfPi; subst. rewrite aenv_minus_empty in *.
    destruct P0 as [ | nb0 | α | P0a P0b | P0b | | P0' ].
    +
      match goal with
      | Hpre' : {{ _ ⨟ _ ⊢ˢ msubst_pskl κ Pi' ⊑ᵖ[ _ ] uskl_unit }}ad,
        HwfPi' : {{ _ ⨟ _ ⊢ₚₛ Pi' }}a |- _ =>
        destruct (IHn Θ0 Θ κ Δ Ψi Pi' pskl_unit
                    ltac:(simpl in Hn; simpl; lia)
                    HwfΘ HwfΘ0 HwfPi' HwfP0 Hκ Hpre' Hrefine)
          as [Pa [Hsolve Hprec]]
      end.
      exists Pa; split;
        [ apply a_solve_eq__univ_ghost_l_guarded; [ constructor | exact Hsolve ]
        | exact Hprec ].
    +  inversion HwfP0.
    +
      match goal with
      | Hpre' : {{ _ ⨟ _ ⊢ˢ msubst_pskl κ Pi' ⊑ᵖ[ _ ] uskl_unit }}ad,
        HwfPi' : {{ _ ⨟ _ ⊢ₚₛ Pi' }}a |- _ =>
        destruct (IHn Θ0 Θ κ Δ Ψi Pi' (pskl_var_f α)
                    ltac:(simpl in Hn; simpl; lia)
                    HwfΘ HwfΘ0 HwfPi' HwfP0 Hκ Hpre' Hrefine)
          as [Pa [Hsolve Hprec]]
      end.
      exists Pa; split;
        [ apply a_solve_eq__univ_ghost_l_guarded; [ constructor | exact Hsolve ]
        | exact Hprec ].
    +  simpl in Hrefine; inversion Hrefine.
    +  simpl in Hrefine; inversion Hrefine.
    +
      exists (pskl_univ_ghost Pi'); split; [ apply a_solve_eq__ghost_r | exact Hpre ].
    +
      simpl in Hrefine. inversion Hrefine; subst.
      inversion HwfP0; subst. rewrite aenv_minus_empty in *.
      match goal with
      | Hpre' : {{ _ ⨟ _ ⊢ˢ msubst_pskl κ Pi' ⊑ᵖ[ _ ] uskl_unit }}ad,
        Href' : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ P0') ⊳ bskl_unit }}ad,
        HwfPi' : {{ _ ⨟ _ ⊢ₚₛ Pi' }}a,
        HwfP0' : {{ _ ⨟ _ ⊢ₚₛ P0' }}a |- _ =>
        destruct (IHn Θ0 Θ κ Δ Ψi Pi' P0'
                    ltac:(simpl in Hn; simpl; lia)
                    HwfΘ HwfΘ0 HwfPi' HwfP0' Hκ Hpre' Href')
          as [Pa [Hsolve Hprec]]
      end.
      exists (pskl_univ_ghost Pa); split;
        [ apply a_solve_eq__univ_ghost_both; exact Hsolve
        | simpl; apply ad_ppre__univ_ghost_remove; exact Hprec ].
Qed.

Lemma a_inc_lookup_flex_ftv_dom : forall Θ0 κ Θ α,
  κ ∷ Θ0 ⊑ Θ ->
  a_flex_tvar Θ0 α ->
  ftvar_in_ptyp (msubst_lookup κ α) [<=] dom Θ.
Proof.
  intros Θ0 κ Θ α Hinc; induction Hinc; intros Hf; simpl in *.
  - destruct Hf as [Hb | (τx & Hb)]; inversion Hb.
  - destruct (α == α0) as [-> | Hne];
      [ eapply a_wf_ptyp_ftv_dom; eassumption | ].
    apply IHHinc.
    destruct Hf as [Hb | (τx & Hb)];
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq _] | Hb'];
      solve [ exfalso; apply Hne; exact Heq
            | left; exact Hb' | right; exists τx; exact Hb' ].
  - destruct (α == α0) as [-> | Hne];
      [ eapply a_wf_ptyp_ftv_dom; eassumption | ].
    apply IHHinc.
    destruct Hf as [Hb | (τx & Hb)];
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq _] | Hb'];
      solve [ exfalso; apply Hne; exact Heq
            | left; exact Hb' | right; exists τx; exact Hb' ].
  -
    assert (Hf' : a_flex_tvar Θ α)
      by (destruct Hf as [Hb | (τx & Hb)];
          destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
          solve [ discriminate Hc | left; exact Hb' | right; exists τx; exact Hb' ]).
    pose proof (IHHinc Hf') as Hd.
    assert (Hdom : dom Θ' [<=] dom (Ξ ++ (x ~ abind_var_typ A') ++ Θ'))
      by (repeat rewrite dom_app; clear; simpl; fsetdec).
    clear - Hd Hdom; fsetdec.
  - assert (Hf' : a_flex_tvar Θ α)
      by (destruct Hf as [Hb | (τx & Hb)];
          destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
          solve [ discriminate Hc | left; exact Hb' | right; exists τx; exact Hb' ]).
    pose proof (IHHinc Hf') as Hd.
    assert (Hdom : dom Θ' [<=] dom (Ξ ++ (x ~ abind_var_skl P') ++ Θ'))
      by (repeat rewrite dom_app; clear; simpl; fsetdec).
    clear - Hd Hdom; fsetdec.
  - assert (Hf' : a_flex_tvar Θ α)
      by (destruct Hf as [Hb | (τx & Hb)];
          destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
          solve [ discriminate Hc | left; exact Hb' | right; exists τx; exact Hb' ]).
    pose proof (IHHinc Hf') as Hd.
    assert (Hdom : dom Θ' [<=] dom (Ξ ++ (α0 ~ abind_tvar) ++ Θ'))
      by (repeat rewrite dom_app; clear; simpl; fsetdec).
    clear - Hd Hdom; fsetdec.
Qed.

Inductive a_def_chain (Θ : aenv) : ptyp -> ptyp -> Prop :=
| a_def_chain_refl : forall τ, a_def_chain Θ τ τ
| a_def_chain_step : forall α τd τe,
    binds α (abind_flex_mono_def τd) Θ ->
    a_def_chain Θ τd τe ->
    a_def_chain Θ (ptyp_var_f α) τe.

Lemma a_def_chain_trans : forall Θ τ1 τ2 τ3,
  a_def_chain Θ τ1 τ2 ->
  a_def_chain Θ τ2 τ3 ->
  a_def_chain Θ τ1 τ3.
Proof.
  intros Θ τ1 τ2 τ3 H1; revert τ3; induction H1; intros τ3 H2; auto.
  eapply a_def_chain_step; eauto.
Qed.

Lemma mono_ptyp_wf_to_pskl_wf : forall τ Θ,
  a_wf_ptyp Θ τ -> mono_ptyp τ ->
  forall Δ, {{ Θ ⨟ Δ ⊢ₚₛ (ptyp_to_pskl τ) }}a.
Proof.
  intros τ Θ Hwf Hm; revert Hwf; induction Hm; intros Hwf Δ; simpl.
  - apply a_wf_pskl__unit.
  - inversion Hwf; subst. apply a_wf_pskl__var; auto.
  - inversion Hwf; subst. apply a_wf_pskl__arrow; auto.
Qed.

Lemma ad_ppre_mono_refl : forall Θ Δ τ,
  mono_ptyp τ ->
  {{ Θ ⨟ Δ ⊢ˢ (ptyp_to_pskl τ) ⊑ᵖ[ empty ] (ptyp_to_uskl_syn τ) }}ad.
Proof.
  intros Θ Δ τ Hm; induction Hm;
    cbn [ptyp_to_pskl ptyp_to_uskl_syn].
  - apply ad_ppre__unit. clear; fsetdec.
  - apply ad_ppre__var. clear; fsetdec.
  - apply ad_ppre__arrow with (Ψ1 := empty) (Ψ2 := empty);
      [ auto | auto | clear; fsetdec ].
Qed.

Lemma ad_ppre_mono_tags_empty : forall Θ Δ P ψ Ψ,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  forall τ, ψ = ptyp_to_uskl_syn τ -> mono_ptyp τ ->
  Ψ [=] empty.
Proof.
  intros Θ Δ P ψ Ψ HwfΘ H; induction H; intros τu Hequ Hmu.
  -  assumption.
  -  assumption.
  -
    symmetry in Hequ.
    destruct (ptyp_to_uskl_syn_arrow_inv _ Hequ)
      as (τ1 & τ2 & -> & Heq1 & Heq2).
    assert (Hm1 : mono_ptyp τ1) by (inversion Hmu; assumption).
    assert (Hm2 : mono_ptyp τ2) by (inversion Hmu; assumption).
    pose proof (IHad_partial_precise1 HwfΘ τ1 Heq1 Hm1) as He1.
    pose proof (IHad_partial_precise2 HwfΘ τ2 Heq2 Hm2) as He2.
    clear - H1 He1 He2; fsetdec.
  -
    exfalso; eapply ptyp_to_uskl_syn_all_tag_absurd; symmetry; exact Hequ.
  -  assumption.
  -
    eapply IHad_partial_precise; eauto.
  -
    exfalso; eapply ptyp_to_uskl_syn_all_tag_absurd; symmetry; exact Hequ.
  -
    exfalso; eapply ptyp_to_uskl_syn_dot_univ_ghost_absurd; symmetry; exact Hequ.
  -
    eapply IHad_partial_precise; eauto.
  -
    symmetry in Hequ.
    apply ptyp_to_uskl_syn_var_inv in Hequ; subst.
    eapply IHad_partial_precise;
      [ exact HwfΘ | reflexivity | eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

Lemma ad_ppre_flexdef_target_unfold : forall Θ Δ Ψ P ψ,
  {{ ⊢ Θ }}a ->
  delta_def_fresh Δ Θ ->
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  forall α τd, ψ = uskl_var_f α ->
  binds α (abind_flex_mono_def τd) Θ ->
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τd) }}ad.
Proof.
  intros Θ Δ Ψ P ψ HwfΘ Hdf H; induction H; intros α0 τd Heq Hbd;
    try discriminate Heq.
  -
    inversion Heq; subst.
    eapply ad_ppre__flex_l; [ exact Hbd | ].
    eapply ad_partial_precise_psi_cong;
      [ apply ad_ppre_mono_refl;
          eapply a_wf_aenv_binds_def_mono; eauto
      | clear - H; fsetdec ].
  -
    apply ad_ppre__ghost; [ assumption | ].
    rewrite ftvar_ptyp_to_uskl_syn.
    apply inter_empty_pointwise.
    intros y Hy. eapply Hdf; eauto.
  -
    apply ad_ppre__univ_ghost_remove. eauto.
  -
    eapply ad_ppre__flex_l; eauto.
  -
    inversion Heq; subst.
    pose proof (binds_unique _ _ _ _ _ H Hbd (a_wf_aenv_uniq HwfΘ)) as Hc.
    inversion Hc; subst. assumption.
Qed.

Lemma ad_refine_flexdef_target_unfold : forall Θ Δr Q' Q,
  {{ ⊢ Θ }}a ->
  delta_def_fresh Δr Θ ->
  {{ Θ ⨟ Δr ⊢ᵣ Q' ⊳ Q }}ad ->
  forall α τd, Q = bskl_var_f α ->
  binds α (abind_flex_mono_def τd) Θ ->
  {{ Θ ⨟ Δr ⊢ᵣ Q' ⊳ (ptyp_to_bskl_syn τd) }}ad.
Proof.
  intros Θ Δr Q' Q HwfΘ Hdf H; induction H; intros α0 τd Heq Hbd;
    try discriminate Heq.
  -
    inversion Heq; subst.
    eapply ad_refine_syn__flex_l; [ exact Hbd | ].
    apply ad_refine_syn_mono_refl.
    eapply a_wf_aenv_binds_def_mono; eauto.
  -
    destruct P; simpl in Heq; try discriminate Heq.
    unfold ptyp_to_bskl_syn.
    apply ad_refine_syn__ghost.
    rewrite ftvar_ptyp_to_pskl.
    apply inter_empty_pointwise.
    intros y Hy. eapply Hdf; eauto.
  -
    apply ad_refine_syn_univ_ghost_remove_intro. eauto.
  -
    eapply ad_refine_syn__flex_l; eauto.
  -
    inversion Heq; subst.
    pose proof (binds_unique _ _ _ _ _ H Hbd (a_wf_aenv_uniq HwfΘ)) as Hc.
    inversion Hc; subst. assumption.
Qed.

Lemma ad_ppre_chain_unfold : forall Θ τ τe,
  a_def_chain Θ τ τe ->
  {{ ⊢ Θ }}a ->
  forall Δ Ψ P,
  delta_def_fresh Δ Θ ->
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τ) }}ad ->
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τe) }}ad.
Proof.
  intros Θ τ τe Hc; induction Hc; intros HwfΘ Δ Ψ P Hdf Hpre; auto.
  apply IHHc; auto.
  eapply ad_ppre_flexdef_target_unfold;
    [ exact HwfΘ | exact Hdf | exact Hpre | reflexivity | exact H ].
Qed.

Lemma ad_ppre_chain_fold : forall Θ τ τe,
  a_def_chain Θ τ τe ->
  forall Δ Ψ P,
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τe) }}ad ->
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τ) }}ad.
Proof.
  intros Θ τ τe Hc; induction Hc; intros Δ Ψ P Hpre; auto.
  simpl. eapply ad_ppre__flex_r; eauto.
Qed.

Lemma ad_refine_chain_unfold : forall Θ τ τe,
  a_def_chain Θ τ τe ->
  {{ ⊢ Θ }}a ->
  forall Δr Q,
  {{ Θ ⨟ Δr ⊢ᵣ Q ⊳ (ptyp_to_bskl_syn τ) }}ad ->
  delta_def_fresh Δr Θ ->
  {{ Θ ⨟ Δr ⊢ᵣ Q ⊳ (ptyp_to_bskl_syn τe) }}ad.
Proof.
  intros Θ τ τe Hc; induction Hc; intros HwfΘ Δr Q Href Hdf; auto.
  apply IHHc; auto.
  eapply ad_refine_flexdef_target_unfold;
    [ exact HwfΘ | exact Hdf | exact Href | reflexivity | exact H ].
Qed.

Lemma ad_ppre_unit_subject_chain_inv : forall Θ Δ Ψ P ψ,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  P = pskl_unit ->
  forall τ, ψ = ptyp_to_uskl_syn τ -> mono_ptyp τ ->
  a_def_chain Θ τ ptyp_unit /\ Ψ [=] empty.
Proof.
  intros Θ Δ Ψ P ψ HwfΘ H; induction H; intros HeqS τu Hequ Hmu;
    try discriminate HeqS.
  -
    symmetry in Hequ. apply ptyp_to_uskl_syn_unit_inv in Hequ; subst.
    split; [ apply a_def_chain_refl | assumption ].
  -
    symmetry in Hequ. apply ptyp_to_uskl_syn_var_inv in Hequ; subst.
    assert (Hmd : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    destruct (IHad_partial_precise HwfΘ eq_refl τ eq_refl Hmd) as [Hc HΨ].
    split; [ eapply a_def_chain_step; eauto | assumption ].
Qed.

Lemma ad_ppre_arrow_subject_chain_inv : forall Θ Δ Ψ P ψ,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  forall P1 P2, P = pskl_arrow P1 P2 ->
  forall τ, ψ = ptyp_to_uskl_syn τ -> mono_ptyp τ ->
  exists τ1 τ2 Ψ1 Ψ2,
    a_def_chain Θ τ (ptyp_arrow τ1 τ2) /\
    mono_ptyp τ1 /\ mono_ptyp τ2 /\
    {{ Θ ⨟ Δ ⊢ˢ P1 ⊑ᵖ[ Ψ1 ] (ptyp_to_uskl_syn τ1) }}ad /\
    {{ Θ ⨟ Δ ⊢ˢ P2 ⊑ᵖ[ Ψ2 ] (ptyp_to_uskl_syn τ2) }}ad /\
    Ψ [=] Ψ1 `union` Ψ2.
Proof.
  intros Θ Δ Ψ P ψ HwfΘ H; induction H; intros S1' S2' HeqS τu Hequ Hmu;
    try discriminate HeqS.
  -
    inversion HeqS; subst.
    symmetry in Hequ.
    destruct (ptyp_to_uskl_syn_arrow_inv _ Hequ)
      as (τ1 & τ2 & -> & Heq1 & Heq2).
    subst.
    assert (Hm1 : mono_ptyp τ1) by (inversion Hmu; assumption).
    assert (Hm2 : mono_ptyp τ2) by (inversion Hmu; assumption).
    exists τ1, τ2, Ψ1, Ψ2.
    repeat (split; [ solve [ apply a_def_chain_refl | assumption ] | ]).
    assumption.
  -
    symmetry in Hequ. apply ptyp_to_uskl_syn_var_inv in Hequ; subst.
    assert (Hmd : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    destruct (IHad_partial_precise HwfΘ S1' S2' eq_refl τ eq_refl Hmd)
      as (τ1 & τ2 & Ψ1 & Ψ2 & Hc & Hm1 & Hm2 & Hp1 & Hp2 & HΨ).
    exists τ1, τ2, Ψ1, Ψ2.
    repeat (split; [ solve [ eapply a_def_chain_step; eauto | assumption ] | ]).
    assumption.
Qed.

Lemma ad_ppre_univ_ghost_subject_chain_inv : forall Θ Δ Ψ P ψ,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  forall P0, P = pskl_univ_ghost P0 ->
  forall τ, ψ = ptyp_to_uskl_syn τ -> mono_ptyp τ ->
  exists τe,
    a_def_chain Θ τ τe /\ mono_ptyp τe /\
    {{ Θ ⨟ Δ ⊢ˢ P0 ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τe) }}ad.
Proof.
  intros Θ Δ Ψ P ψ HwfΘ H; induction H; intros S0' HeqS τu Hequ Hmu;
    try discriminate HeqS.
  -
    inversion HeqS; subst.
    exists τu. split; [ apply a_def_chain_refl | split; assumption ].
  -
    exfalso; eapply ptyp_to_uskl_syn_all_tag_absurd; symmetry; exact Hequ.
  -
    exfalso; eapply ptyp_to_uskl_syn_dot_univ_ghost_absurd; symmetry; exact Hequ.
  -
    symmetry in Hequ. apply ptyp_to_uskl_syn_var_inv in Hequ; subst.
    assert (Hmd : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    destruct (IHad_partial_precise HwfΘ S0' eq_refl τ eq_refl Hmd)
      as (τe & Hc & Hme & Hp).
    exists τe. split; [ eapply a_def_chain_step; eauto | split; assumption ].
Qed.

Lemma ad_ppre_allsyn_subject_mono_absurd : forall Θ Δ Ψ P ψ,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  forall P0, P = pskl_all_syn P0 ->
  forall τ, ψ = ptyp_to_uskl_syn τ -> mono_ptyp τ ->
  False.
Proof.
  intros Θ Δ Ψ P ψ HwfΘ H; induction H; intros S0' HeqS τu Hequ Hmu;
    try discriminate HeqS.
  -
    eapply ptyp_to_uskl_syn_all_tag_absurd; symmetry; exact Hequ.
  -
    symmetry in Hequ. apply ptyp_to_uskl_syn_var_inv in Hequ; subst.
    eapply IHad_partial_precise;
      [ exact HwfΘ | reflexivity | reflexivity
      | eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

Lemma ad_refine_univ_ghost_lhs_chain_inv : forall Θ Δr Q' Q,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δr ⊢ᵣ Q' ⊳ Q }}ad ->
  forall Qb, Q' = bskl_univ_ghost Qb ->
  forall τ, Q = ptyp_to_bskl_syn τ -> mono_ptyp τ ->
  exists τe,
    a_def_chain Θ τ τe /\ mono_ptyp τe /\
    {{ Θ ⨟ Δr ⊢ᵣ Qb ⊳ (ptyp_to_bskl_syn τe) }}ad.
Proof.
  intros Θ Δr Q' Q HwfΘ H; induction H; intros Qb' HeqL τu Hequ Hmu;
    try discriminate HeqL.
  -
    inversion HeqL; subst.
    exists τu. split; [ apply a_def_chain_refl | split; assumption ].
  -
    exfalso; eapply ptyp_to_bskl_syn_all_syn_mono_absurd;
      [ exact Hmu | symmetry; exact Hequ ].
  -
    exfalso; eapply ptyp_to_bskl_syn_univ_ghost_absurd; symmetry; exact Hequ.
  -
    symmetry in Hequ. apply ptyp_to_bskl_syn_var_inv in Hequ; subst.
    assert (Hmd : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    destruct (IHad_refine_syn HwfΘ Qb' eq_refl τ eq_refl Hmd)
      as (τe & Hc & Hme & Hr).
    exists τe. split; [ eapply a_def_chain_step; eauto | split; assumption ].
Qed.

Lemma ad_refine_allinh_lhs_mono_absurd : forall Θ Δr Q' Q,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δr ⊢ᵣ Q' ⊳ Q }}ad ->
  forall Qb, Q' = bskl_all_inh Qb ->
  forall τ, Q = ptyp_to_bskl_syn τ -> mono_ptyp τ ->
  False.
Proof.
  intros Θ Δr Q' Q HwfΘ H; induction H; intros Qb' HeqL τu Hequ Hmu;
    try discriminate HeqL.
  -
    eapply ptyp_to_bskl_syn_all_inh_absurd; symmetry; exact Hequ.
  -
    symmetry in Hequ. apply ptyp_to_bskl_syn_var_inv in Hequ; subst.
    eapply IHad_refine_syn;
      [ exact HwfΘ | reflexivity | reflexivity
      | eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

Lemma ad_refine_inh_ghost_ppre : forall Θ Δr Q' Q,
  {{ ⊢ Θ }}a ->
  Δr [=] empty ->
  {{ Θ ⨟ Δr ⊢ᵣ Q' ⊳ Q }}ad ->
  forall P' τ, Q' = pskl_to_bskl_inh P' -> Q = ptyp_to_bskl_syn τ ->
  mono_ptyp τ ->
  a_wf_ptyp Θ τ ->
  forall Δ Ψ, delta_def_fresh Δ Θ ->
  {{ Θ ⨟ Δ ⊢ˢ pskl_ghost ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τ) }}ad ->
  {{ Θ ⨟ Δ ⊢ˢ P' ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τ) }}ad.
Proof.
  intros Θ Δr Q' Q HwfΘ HΔr H; induction H;
    intros P' τu HeqL HeqQ Hmu Hwτ Δo Ψo Hdf Hhp.
  -
    destruct P'; simpl in HeqL; try discriminate HeqL.
    symmetry in HeqQ; apply ptyp_to_bskl_syn_unit_inv in HeqQ; subst.
    assert (HΨ : Ψo [=] empty)
      by (eapply ad_ppre_mono_tags_empty;
            [ exact HwfΘ | exact Hhp | reflexivity | exact Hmu ]).
    simpl. apply ad_ppre__unit. exact HΨ.
  -
    destruct P'; simpl in HeqL; try discriminate HeqL.
    inversion HeqL; subst.
    symmetry in HeqQ; apply ptyp_to_bskl_syn_var_inv in HeqQ.
    inversion HeqQ; subst.
    assert (HΨ : Ψo [=] empty)
      by (eapply ad_ppre_mono_tags_empty;
            [ exact HwfΘ | exact Hhp | reflexivity | exact Hmu ]).
    simpl. apply ad_ppre__var. exact HΨ.
  -
    symmetry in HeqQ.
    destruct (ptyp_to_bskl_syn_arrow_inv _ HeqQ)
      as (τ1 & τ2 & -> & Heq1 & Heq2).
    destruct (pskl_to_bskl_inh_arrow_inv _ (eq_sym HeqL))
      as (Pb1 & Pb2 & -> & HeqPb1 & HeqPb2).
    assert (Hm1 : mono_ptyp τ1) by (inversion Hmu; assumption).
    assert (Hm2 : mono_ptyp τ2) by (inversion Hmu; assumption).
    simpl in Hhp.
    inversion Hhp; subst.
    +
      match goal with
      | HΨe : Ψo [=] empty |- _ => rename HΨe into HPsiE
      end.
      match goal with
      | Hint : _ ∩ _ [=] empty |- _ => rename Hint into HInt
      end.
      rewrite ftvar_ptyp_to_uskl_syn in HInt.
      simpl in HInt.
      assert (Hhp1 : {{ Θ ⨟ Δo ⊢ˢ pskl_ghost ⊑ᵖ[ empty ] (ptyp_to_uskl_syn τ1) }}ad)
        by (apply ad_ppre__ghost;
              [ clear; fsetdec
              | rewrite ftvar_ptyp_to_uskl_syn;
                clear - HInt; fsetdec ]).
      assert (Hhp2 : {{ Θ ⨟ Δo ⊢ˢ pskl_ghost ⊑ᵖ[ empty ] (ptyp_to_uskl_syn τ2) }}ad)
        by (apply ad_ppre__ghost;
              [ clear; fsetdec
              | rewrite ftvar_ptyp_to_uskl_syn;
                clear - HInt; fsetdec ]).
      simpl.
      apply ad_ppre__arrow with (Ψ1 := empty) (Ψ2 := empty);
        [ eapply IHad_refine_syn1;
            [ exact HwfΘ | exact HΔr | reflexivity
            | reflexivity | exact Hm1 | inversion Hwτ; assumption
            | exact Hdf | exact Hhp1 ]
        | eapply IHad_refine_syn2;
            [ exact HwfΘ | exact HΔr | reflexivity
            | reflexivity | exact Hm2 | inversion Hwτ; assumption
            | exact Hdf | exact Hhp2 ]
        | clear - HPsiE; fsetdec ].
  -
    exfalso; eapply ptyp_to_bskl_syn_all_inh_absurd; symmetry; exact HeqQ.
  -
    destruct P'; simpl in HeqL; try discriminate HeqL.
    exact Hhp.
  -
    destruct P'; simpl in HeqL; try discriminate HeqL.
    inversion HeqL; subst.
    apply ad_ppre__univ_ghost_remove.
    eapply IHad_refine_syn; eauto.
  -
    exfalso; eapply ptyp_to_bskl_syn_all_syn_mono_absurd;
      [ exact Hmu | symmetry; exact HeqQ ].
  -
    exfalso; eapply ptyp_to_bskl_syn_univ_ghost_absurd; symmetry; exact HeqQ.
  -
    destruct P'; simpl in HeqL; try discriminate HeqL.
    inversion HeqL; subst.
    eapply ad_ppre__flex_l; [ eassumption | ].
    assert (Hmα : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; eauto).
    eapply IHad_refine_syn;
      [ exact HwfΘ | exact HΔr
      | symmetry; apply ptyp_to_bskl_inh_syn_eq; exact Hmα
      | reflexivity | exact Hmu | exact Hwτ | exact Hdf | exact Hhp ].
  -
    symmetry in HeqQ; apply ptyp_to_bskl_syn_var_inv in HeqQ; subst.
    assert (HmX : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; eauto).
    simpl in Hhp.
    assert (Hhp' : {{ Θ ⨟ Δo ⊢ˢ pskl_ghost ⊑ᵖ[ Ψo ] (ptyp_to_uskl_syn τ) }}ad).
    { inversion Hhp; subst.
      -
        apply ad_ppre__ghost; [ assumption | ].
        rewrite ftvar_ptyp_to_uskl_syn.
        apply inter_empty_pointwise.
        intros y Hy. eapply Hdf; eauto.
      -
        match goal with
        | Hb2 : binds _ (abind_flex_mono_def _) _ |- _ =>
            pose proof (binds_unique _ _ _ _ _ Hb2 H
                          (a_wf_aenv_uniq HwfΘ)) as Hcc;
            inversion Hcc; subst; assumption
        end. }
    simpl.
    eapply ad_ppre__flex_r; [ eassumption | ].
    eapply IHad_refine_syn;
      [ exact HwfΘ | exact HΔr | reflexivity
      | reflexivity | exact HmX
      | eapply a_wf_aenv_binds_def_wf; eauto
      | exact Hdf | exact Hhp' ].
Qed.

Lemma a_def_chain_wf : forall Θ τ τe,
  a_def_chain Θ τ τe -> {{ ⊢ Θ }}a -> a_wf_ptyp Θ τ -> a_wf_ptyp Θ τe.
Proof.
  intros Θ τ τe Hc; induction Hc; intros Hwf Hp; auto.
  apply IHHc; [ exact Hwf | ].
  eapply a_wf_aenv_binds_def_wf; eauto.
Qed.

Lemma a_def_chain_rigid_var_inv : forall Θ α τe,
  a_def_chain Θ (ptyp_var_f α) τe ->
  {{ ⊢ Θ }}a ->
  binds α abind_tvar Θ ->
  τe = ptyp_var_f α.
Proof.
  intros Θ α τe Hc HwfΘ Hrig.
  inversion Hc as [ | α0 τd τe0 Hb Hc0 ]; subst; [ reflexivity | ].
  exfalso.
  pose proof (binds_unique _ _ _ _ _ Hrig Hb (a_wf_aenv_uniq HwfΘ)) as Hcc.
  discriminate Hcc.
Qed.

Lemma a_binds_tvar_strengthen_kit : forall Θ Θw α,
  uniq Θ ->
  (forall x b, binds x b Θw -> binds x b Θ) ->
  a_binds_tvar α Θ ->
  α `in` dom Θw ->
  a_binds_tvar α Θw.
Proof.
  intros Θ Θw α Hu Hmon Hbt Hin.
  apply binds_In_inv in Hin. destruct Hin as [b Hb].
  assert (Hb' : binds α b Θ) by (apply Hmon; exact Hb).
  destruct Hbt as [Hr | [Hf | (τ & Hd)]].
  - pose proof (binds_unique _ _ _ _ _ Hb' Hr Hu) as ->.
    left; exact Hb.
  - pose proof (binds_unique _ _ _ _ _ Hb' Hf Hu) as ->.
    right; left; exact Hb.
  - pose proof (binds_unique _ _ _ _ _ Hb' Hd Hu) as ->.
    right; right; exists τ; exact Hb.
Qed.

Lemma a_wf_ptyp_mono_strengthen_dom : forall Θ Θw τ,
  {{ ⊢ Θ }}a ->
  (forall x b, binds x b Θw -> binds x b Θ) ->
  mono_ptyp τ ->
  a_wf_ptyp Θ τ ->
  ftvar_in_ptyp τ [<=] dom Θw ->
  a_wf_ptyp Θw τ.
Proof.
  intros Θ Θw τ HwfΘ Hmon Hm Hwf Hsub.
  apply mono_ptyp_wf; [ exact Hm | ].
  intros α Hα.
  eapply a_binds_tvar_strengthen_kit;
    [ apply a_wf_aenv_uniq; exact HwfΘ
    | exact Hmon
    | eapply a_wf_ptyp_ftv_tvarish; eassumption
    | clear - Hsub Hα; fsetdec ].
Qed.

Lemma a_def_chain_wf_at : forall Θ Θw τ τe,
  a_def_chain Θ τ τe ->
  {{ ⊢ Θw }}a ->
  (forall α τ0, binds α (abind_flex_mono_def τ0) Θ ->
     binds α (abind_flex_mono_def τ0) Θw) ->
  a_wf_ptyp Θw τ ->
  a_wf_ptyp Θw τe.
Proof.
  intros Θ Θw τ τe Hc; induction Hc; intros Hwf Hdefs Hp; auto.
  apply IHHc; [ exact Hwf | exact Hdefs | ].
  eapply a_wf_aenv_binds_def_wf; [ exact Hwf | apply Hdefs; eassumption ].
Qed.

Lemma a_def_chain_ftv_at : forall Θ Θw Δ τ τe,
  a_def_chain Θ τ τe ->
  {{ ⊢ Θw }}a ->
  (forall α τ0, binds α (abind_flex_mono_def τ0) Θ ->
     binds α (abind_flex_mono_def τ0) Θw) ->
  ftvar_in_ptyp τ [<=] dom Θw `union` Δ ->
  ftvar_in_ptyp τe [<=] dom Θw `union` Δ.
Proof.
  intros Θ Θw Δ τ τe Hc; induction Hc; intros HwfΘw Hdefs Hft; [ exact Hft | ].
  apply IHHc; [ exact HwfΘw | exact Hdefs | ].
  assert (Hb : binds α (abind_flex_mono_def τd) Θw)
    by (apply Hdefs; assumption).
  assert (Hd : ftvar_in_ptyp τd [<=] dom Θw)
    by (eapply a_wf_aenv_def_ftv_dom; eassumption).
  clear - Hd; fsetdec.
Qed.

Lemma ppre_ghost_payload_wf : forall Θ Θw Δ Ψ τ,
  {{ ⊢ Θ }}a -> {{ ⊢ Θw }}a ->
  (forall x b, binds x b Θw -> binds x b Θ) ->
  (forall α τ0, binds α (abind_flex_mono_def τ0) Θ ->
     binds α (abind_flex_mono_def τ0) Θw) ->
  mono_ptyp τ -> a_wf_ptyp Θ τ ->
  ftvar_in_ptyp τ [<=] dom Θw `union` Δ ->
  {{ Θ ⨟ Δ ⊢ˢ pskl_ghost ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τ) }}ad ->
  a_wf_ptyp Θw τ.
Proof.
  intros Θ Θw Δ Ψ τ HwfΘ HwfΘw Hmon Hdefs Hm Hwf Hft Hpre.
  inversion Hpre; subst.
  -
    assert (Hap : ftvar_in_ptyp τ ∩ Δ [=] empty).
    { match goal with Hd : Δ ∩ ftvar_in_uskl _ [=] empty |- _ =>
        rewrite ftvar_ptyp_to_uskl_syn in Hd; clear - Hd; fsetdec
      end. }
    eapply a_wf_ptyp_mono_strengthen_dom;
      [ exact HwfΘ | exact Hmon | exact Hm | exact Hwf
      | clear - Hft Hap; fsetdec ].
  -
    destruct τ; simpl in *; try discriminate.
    match goal with Heq : uskl_var_f _ = ptyp_to_uskl_syn _ |- _ =>
      cbn [ptyp_to_uskl_syn] in Heq; inversion Heq; subst end.
    apply a_wf_ptyp__var. right; right.
    match goal with Hb : binds _ (abind_flex_mono_def ?τ0) Θ |- _ =>
      exists τ0; apply Hdefs; exact Hb end.
Qed.

Lemma a_def_chain_wf_or_rigid : forall Θ Θw τ τe,
  a_def_chain Θ τ τe ->
  {{ ⊢ Θ }}a ->
  {{ ⊢ Θw }}a ->
  (forall α τ0, binds α (abind_flex_mono_def τ0) Θ ->
     binds α (abind_flex_mono_def τ0) Θw) ->
  (a_wf_ptyp Θw τ \/ (exists α0, τ = ptyp_var_f α0 /\ binds α0 abind_tvar Θ)) ->
  (a_wf_ptyp Θw τe \/
     (exists α0, τe = ptyp_var_f α0 /\ binds α0 abind_tvar Θ)).
Proof.
  intros Θ Θw τ τe Hc HwfΘ HwfΘw Hdefs [Hw | (α0 & Heq & Hrig)].
  - left. eapply a_def_chain_wf_at; eassumption.
  - subst τ. rewrite (a_def_chain_rigid_var_inv Hc HwfΘ Hrig).
    right. exists α0. split; [ reflexivity | exact Hrig ].
Qed.

Lemma a_guess_ty_witness_mono_gen : forall n Θ0 Θ Θw κ Δ Ψi τ Pi,
  size_pskl Pi <= n ->
  {{ ⊢ Θ }}a ->
  {{ ⊢ Θw }}a ->
  (forall x b, binds x b Θw -> binds x b Θ) ->
  (forall α τ0, binds α (abind_flex_mono_def τ0) Θ ->
     binds α (abind_flex_mono_def τ0) Θw) ->
  {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a ->
  mono_ptyp τ ->
  a_wf_ptyp Θ τ ->
  ftvar_in_ptyp τ [<=] dom Θw `union` Δ ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (ptyp_to_uskl_syn τ) }}ad ->
  forall L, exists (Ξ : aenv) (A : ptyp) (κ' : metasubst),
    (forall Θg, ftvar_in_aenv Θg [<=] L -> a_guess_mono Θg Pi Ξ A) /\
    all_flex_mono Ξ /\
    uniq Ξ /\
    keys κ' = keys Ξ /\
    (forall α, α `in` dom Ξ -> α `notin` L) /\
    Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κ' /\
    {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κ' ++ κ) (ptyp_to_pskl A))
            ⊑ᵖ[ Ψi ] (ptyp_to_uskl_syn τ) }}ad.
Proof.
  induction n as [ | n IH ];
    intros Θ0 Θ Θw κ Δ Ψi τ Pi Hsz HwfΘ HwfΘw Hmon Hdefs HwfPi Hmτ Hwfτ Hftτ Hpre L.
  { exfalso. pose proof (size_pskl_min Pi) as Hm. clear - Hsz Hm. lia. }
  destruct Pi as [ | nb | α | Pi1 Pi2 | Pib | | Pi' ].
  -
    exists nil, ptyp_unit, nil.
    split; [ intros Θg _; apply a_guess_mono__unit | ].
    split; [ apply Forall_nil | ].
    split; [ apply uniq_nil | ].
    split; [ reflexivity | ].
    split; [ intros α0 Hα0; cbn in Hα0; exfalso; clear - Hα0; fsetdec | ].
    split; [ apply Forall_nil | ].
    cbn [app ptyp_to_pskl msubst_pskl] in *. exact Hpre.
  -  inversion HwfPi.
  -
    exists nil, (ptyp_var_f α), nil.
    split; [ intros Θg _; apply a_guess_mono__var | ].
    split; [ apply Forall_nil | ].
    split; [ apply uniq_nil | ].
    split; [ reflexivity | ].
    split; [ intros α0 Hα0; cbn in Hα0; exfalso; clear - Hα0; fsetdec | ].
    split; [ apply Forall_nil | ].
    cbn [app ptyp_to_pskl]. exact Hpre.
  -
    cbn in Hsz.
    assert (HwfPi1 : {{ Θ0 ⨟ empty ⊢ₚₛ Pi1 }}a) by (inversion HwfPi; assumption).
    assert (HwfPi2 : {{ Θ0 ⨟ empty ⊢ₚₛ Pi2 }}a) by (inversion HwfPi; assumption).
    cbn [msubst_pskl] in Hpre.
    destruct (ad_ppre_arrow_subject_chain_inv HwfΘ Hpre eq_refl eq_refl Hmτ)
      as (τ1 & τ2 & Ψ1 & Ψ2 & Hc & Hm1 & Hm2 & Hp1 & Hp2 & HΨ).
    assert (Hwfar : a_wf_ptyp Θ (ptyp_arrow τ1 τ2))
      by (eapply a_def_chain_wf; eassumption).
    assert (Hftar : ftvar_in_ptyp (ptyp_arrow τ1 τ2) [<=] dom Θw `union` Δ)
      by (eapply a_def_chain_ftv_at; eassumption).
    cbn [ftvar_in_ptyp] in Hftar.
    assert (Hwf1 : a_wf_ptyp Θ τ1) by (inversion Hwfar; assumption).
    assert (Hwf2 : a_wf_ptyp Θ τ2) by (inversion Hwfar; assumption).
    assert (Hft1 : ftvar_in_ptyp τ1 [<=] dom Θw `union` Δ)
      by (clear - Hftar; fsetdec).
    assert (Hft2 : ftvar_in_ptyp τ2 [<=] dom Θw `union` Δ)
      by (clear - Hftar; fsetdec).
    destruct (IH Θ0 Θ Θw κ Δ Ψ1 τ1 Pi1 ltac:(lia) HwfΘ HwfΘw Hmon Hdefs
                HwfPi1 Hm1 Hwf1 Hft1 Hp1
                (L `union` ftvar_in_pskl Pi1 `union` ftvar_in_pskl Pi2))
      as (Ξ1 & A1 & κa & Hgu1 & Hfm1 & Hu1 & Hk1 & Hfr1 & HF1 & Hpr1).
    destruct (IH Θ0 Θ Θw κ Δ Ψ2 τ2 Pi2 ltac:(lia) HwfΘ HwfΘw Hmon Hdefs
                HwfPi2 Hm2 Hwf2 Hft2 Hp2
                (L `union` ftvar_in_pskl Pi1 `union` ftvar_in_pskl Pi2
                   `union` dom Ξ1))
      as (Ξ2 & A2 & κb & Hgu2 & Hfm2 & Hu2 & Hk2 & Hfr2 & HF2 & Hpr2).
    assert (Hdκa : dom κa [=] dom Ξ1) by (apply keys_eq_dom; exact Hk1).
    assert (Hdκb : dom κb [=] dom Ξ2) by (apply keys_eq_dom; exact Hk2).
    assert (HA1 : ftvar_in_pskl (ptyp_to_pskl A1)
                  [<=] ftvar_in_pskl Pi1 `union` dom Ξ1).
    { assert (Hb : ftvar_in_ptyp A1 [<=] ftvar_in_pskl Pi1 `union` dom Ξ1)
        by (eapply a_guess_mono_ftv; apply (Hgu1 nil); simpl; fsetdec).
      pose proof (ptyp_to_pskl_ftv A1) as Hc1. clear - Hb Hc1; fsetdec. }
    assert (HA2 : ftvar_in_pskl (ptyp_to_pskl A2)
                  [<=] ftvar_in_pskl Pi2 `union` dom Ξ2).
    { assert (Hb : ftvar_in_ptyp A2 [<=] ftvar_in_pskl Pi2 `union` dom Ξ2)
        by (eapply a_guess_mono_ftv; apply (Hgu2 nil); simpl; fsetdec).
      pose proof (ptyp_to_pskl_ftv A2) as Hc2. clear - Hb Hc2; fsetdec. }
    assert (Hdisj : disjoint Ξ1 Ξ2).
    { unfold disjoint. intros α0 Hα0.
      assert (Hin2 : α0 `in` dom Ξ2) by (clear - Hα0; fsetdec).
      specialize (Hfr2 α0 Hin2). clear - Hα0 Hfr2; fsetdec. }
    assert (Heq1 : msubst_pskl (κa ++ κb ++ κ) (ptyp_to_pskl A1)
                   = msubst_pskl (κa ++ κ) (ptyp_to_pskl A1)).
    { apply msubst_pskl_mid_skip. intros α0 Hα0.
      assert (Hin2 : α0 `in` dom Ξ2) by (clear - Hα0 Hdκb; fsetdec).
      specialize (Hfr2 α0 Hin2). clear - Hfr2 HA1; fsetdec. }
    assert (Heq2 : msubst_pskl (nil ++ κa ++ (κb ++ κ)) (ptyp_to_pskl A2)
                   = msubst_pskl (nil ++ (κb ++ κ)) (ptyp_to_pskl A2)).
    { apply msubst_pskl_mid_skip. intros α0 Hα0.
      assert (Hin1 : α0 `in` dom Ξ1) by (clear - Hα0 Hdκa; fsetdec).
      specialize (Hfr1 α0 Hin1).
      assert (Hne : α0 `notin` dom Ξ2)
        by (clear - Hin1 Hdisj; unfold disjoint in Hdisj; fsetdec).
      clear - Hfr1 Hne HA2; fsetdec. }
    cbn [app] in Heq2.
    exists (Ξ1 ++ Ξ2), (ptyp_arrow A1 A2), (κa ++ κb).
    split; [ intros Θg Hsub; apply a_guess_mono__arrow;
             [ apply Hgu1 | apply Hgu2 ]; clear - Hsub; fsetdec | ].
    split; [ apply all_flex_mono_app; assumption | ].
    split; [ clear - Hu1 Hu2 Hdisj; solve_uniq | ].
    split; [ rewrite ! keys_app; rewrite Hk1, Hk2; reflexivity | ].
    split; [ intros α0 Hα0; rewrite dom_app in Hα0;
             destruct (union_1 Hα0) as [Hin1 | Hin2];
               [ specialize (Hfr1 α0 Hin1); clear - Hfr1; fsetdec
               | specialize (Hfr2 α0 Hin2); clear - Hfr2; fsetdec ] | ].
    split; [ apply Forall_app; split; assumption | ].

    eapply ad_ppre_chain_fold; [ exact Hc | ].
    rewrite list_app_assoc. cbn [ptyp_to_pskl msubst_pskl ptyp_to_uskl_syn].
    rewrite Heq1, Heq2.
    apply ad_ppre__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2); eassumption.
  -
    exfalso.
    cbn [msubst_pskl] in Hpre.
    eapply ad_ppre_allsyn_subject_mono_absurd;
      [ exact HwfΘ | exact Hpre | reflexivity | reflexivity | exact Hmτ ].
  -

    destruct (atom_fresh L) as [α1 Hα1].
    cbn [msubst_pskl] in Hpre.
    assert (Hwfw : a_wf_ptyp Θw τ)
      by (eapply ppre_ghost_payload_wf;
            [ exact HwfΘ | exact HwfΘw | exact Hmon | exact Hdefs
            | exact Hmτ | exact Hwfτ | exact Hftτ | exact Hpre ]).
    assert (HΨi : Ψi [=] empty)
      by (eapply ad_ppre_mono_tags_empty;
            [ exact HwfΘ | exact Hpre | reflexivity | exact Hmτ ]).
    exists ((α1 ~ abind_flex_mono) ++ nil), (ptyp_var_f α1),
           ((α1, τ) :: nil).
    split; [ intros Θg Hsub; apply a_guess_mono__ghost;
             clear - Hsub Hα1; fsetdec | ].
    split; [ apply Forall_cons; [ reflexivity | apply Forall_nil ] | ].
    split; [ solve_uniq | ].
    split; [ reflexivity | ].
    split; [ intros α0 Hα0; simpl in Hα0;
             assert (Heq : α0 = α1) by (clear - Hα0; fsetdec);
             subst α0; exact Hα1 | ].
    split; [ apply Forall_cons;
             [ split; eassumption | apply Forall_nil ] | ].
    cbn [app ptyp_to_pskl msubst_pskl msubst_lookup].
    destruct (α1 == α1) as [_ | Hne]; [ | contradiction ].
    eapply ad_partial_precise_psi_cong;
      [ apply ad_ppre_mono_refl; exact Hmτ
      | clear - HΨi; fsetdec ].
  -
    cbn in Hsz.
    assert (HwfPi' : {{ Θ0 ⨟ empty ⊢ₚₛ Pi' }}a) by (exact (proj2 (a_wf_pskl_univ_ghost_inv HwfPi))).
    cbn [msubst_pskl] in Hpre.
    destruct (ad_ppre_univ_ghost_subject_chain_inv HwfΘ Hpre eq_refl eq_refl Hmτ)
      as (τe & Hc & Hme & Hp').
    assert (Hwfe : a_wf_ptyp Θ τe)
      by (eapply a_def_chain_wf; eassumption).
    assert (Hfte : ftvar_in_ptyp τe [<=] dom Θw `union` Δ)
      by (eapply a_def_chain_ftv_at; eassumption).
    destruct (IH Θ0 Θ Θw κ Δ Ψi τe Pi' ltac:(lia) HwfΘ HwfΘw Hmon Hdefs
                HwfPi' Hme Hwfe Hfte Hp' L)
      as (Ξ0 & A0 & κ0 & Hgu & Hfm & Hu & Hk & Hfr & HF & Hpr).
    exists Ξ0, A0, κ0.
    split; [ intros Θg Hsub; apply a_guess_mono__univ_ghost;
             apply Hgu; exact Hsub | ].
    split; [ exact Hfm | ].
    split; [ exact Hu | ].
    split; [ exact Hk | ].
    split; [ exact Hfr | ].
    split; [ exact HF | ].
    eapply ad_ppre_chain_fold; eassumption.
Qed.

Lemma a_guess_ty_witness_mono : forall n Θ0 Θ Θw κ Δ Ψi τ Pi,
  size_pskl Pi <= n ->
  {{ ⊢ Θ }}a ->
  {{ ⊢ Θw }}a ->
  (forall x b, binds x b Θw -> binds x b Θ) ->
  (forall α τ0, binds α (abind_flex_mono_def τ0) Θ ->
     binds α (abind_flex_mono_def τ0) Θw) ->
  {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a ->
  mono_ptyp τ ->
  a_wf_ptyp Θw τ ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (ptyp_to_uskl_syn τ) }}ad ->
  forall L, exists (Ξ : aenv) (A : ptyp) (κ' : metasubst),
    (forall Θg, ftvar_in_aenv Θg [<=] L -> a_guess_mono Θg Pi Ξ A) /\
    all_flex_mono Ξ /\
    uniq Ξ /\
    keys κ' = keys Ξ /\
    (forall α, α `in` dom Ξ -> α `notin` L) /\
    Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κ' /\
    {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κ' ++ κ) (ptyp_to_pskl A))
            ⊑ᵖ[ Ψi ] (ptyp_to_uskl_syn τ) }}ad.
Proof.
  intros n Θ0 Θ Θw κ Δ Ψi τ Pi Hsz HwfΘ HwfΘw Hmon Hdefs HwfPi Hmτ Hwfτ Hpre L.
  eapply a_guess_ty_witness_mono_gen;
    [ exact Hsz | exact HwfΘ | exact HwfΘw | exact Hmon | exact Hdefs
    | exact HwfPi | exact Hmτ
    | eapply a_wf_ptyp_weaken; eassumption
    |
      pose proof (a_wf_ptyp_ftv_dom Hwfτ) as Hd; clear - Hd; fsetdec
    | exact Hpre ].
Qed.

Lemma a_solve_sub_ctx_exchange : forall β1 β2 (Θ : aenv) m P Q Ξ P',
  {{ ((β1 ~ abind_tvar) ++ (β2 ~ abind_tvar) ++ Θ) ⊢ₛ P ≼[ m ] Q
     ⤳ Ξ ⨾ P' }}a ->
  {{ ((β2 ~ abind_tvar) ++ (β1 ~ abind_tvar) ++ Θ) ⊢ₛ P ≼[ m ] Q
     ⤳ Ξ ⨾ P' }}a.
Proof.
  intros * H.
  eapply (proj1 a_solve_sub_eq_ctx_change); [ exact H | | | ].
  - simpl. fsetdec.
  - intros α0 Hf. unfold a_flex_tvar, binds in *; simpl in *.
    destruct Hf as [Hb | [τ Hb]]; [ left | right; exists τ ]; tauto.
  - intros P0 Hf. inversion Hf; subst;
      match goal with
      | Hb : binds _ _ _ |- _ =>
          unfold binds in Hb; simpl in Hb;
          destruct Hb as [E | [E | HbIn]];
          [ discriminate E | discriminate E | ]
      end;
      [ apply a_flex__var | eapply a_flex__var_def ];
      unfold binds; simpl; right; right; exact HbIn.
Qed.

Arguments a_solve_sub_ctx_exchange {β1 β2 Θ m P Q Ξ P'}.

Lemma uskl_rsubst_clean_eq : forall NM Θ Δρ Ψρ R' R,
  uskl_rsubst NM Θ Δρ Ψρ R' R ->
  (ftvar_in_uskl R) ∩ Δρ [=] empty ->
  R' = R /\ Ψρ [=] empty.
Proof.
  intros NM Θ Δρ Ψρ R' R H; induction H; intros Hclean.
  - split; [ reflexivity | assumption ].
  -
    exfalso. simpl in Hclean.
    match goal with Hα : α `in` Δρ |- _ => clear - Hα Hclean; fsetdec end.
  -
    simpl in Hclean.
    destruct IHuskl_rsubst1 as [-> HΨ1]; [ clear - Hclean; fsetdec | ].
    destruct IHuskl_rsubst2 as [-> HΨ2]; [ clear - Hclean; fsetdec | ].
    split; [ reflexivity | ].
    match goal with HΨ : Ψρ [=] union _ _ |- _ =>
      clear - HΨ HΨ1 HΨ2; fsetdec end.
  -
    simpl in Hclean.
    pick fresh α for
      (L `union` Δρ `union` ftvar_in_uskl R' `union` ftvar_in_uskl R).
    destruct (H0 α ltac:(solve_notin_auto)) as [Heq HΨ].
    { pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R (uskl_var_f α)).
      simpl in *. clear - Hclean H1 Fr. fsetdec. }
    split; [ | exact HΨ ].
    f_equal.
    apply open_uskl_wrt_uskl_inj with (α1 := α);
      [ clear - Fr; fsetdec | clear - Fr; fsetdec | exact Heq ].
  -
    simpl in Hclean.
    pick fresh α for
      (L `union` Δρ `union` ftvar_in_uskl R' `union` ftvar_in_uskl R).
    destruct (H0 α ltac:(solve_notin_auto)) as [Heq HΨ].
    { pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R (uskl_var_f α)).
      simpl in *. clear - Hclean H1 Fr. fsetdec. }
    split; [ | exact HΨ ].
    f_equal.
    apply open_uskl_wrt_uskl_inj with (α1 := α);
      [ clear - Fr; fsetdec | clear - Fr; fsetdec | exact Heq ].
  -
    simpl in Hclean.
    destruct IHuskl_rsubst as [-> HΨ]; [ exact Hclean | ].
    split; [ reflexivity | exact HΨ ].
  -
    simpl in Hclean.
    destruct IHuskl_rsubst as [-> HΨ]; [ exact Hclean | ].
    split; [ reflexivity | exact HΨ ].
Qed.

Lemma uskl_rsubst_mono_target : forall NM Θ Δρ Ψρ ψsub ψa τ,
  uskl_rsubst NM Θ Δρ Ψρ ψsub ψa ->
  ψsub = ptyp_to_uskl_syn τ -> mono_ptyp τ ->
  exists τa, ψa = ptyp_to_uskl_syn τa /\ mono_ptyp τa.
Proof.
  intros NM Θ Δρ Ψρ ψsub ψa τ H. revert τ.
  induction H; intros τ Heq Hm.
  -  exists τ; split; eassumption.
  -
    exists (ptyp_var_f α); split; [ reflexivity | apply mono_ptyp__var ].
  -
    destruct τ; simpl in Heq; try discriminate Heq.
    inversion Heq; subst.
    inversion Hm; subst.
    destruct (IHuskl_rsubst1 _ eq_refl ltac:(assumption)) as (τa1 & -> & Hm1).
    destruct (IHuskl_rsubst2 _ eq_refl ltac:(assumption)) as (τa2 & -> & Hm2).
    exists (ptyp_arrow τa1 τa2); split;
      [ reflexivity | apply mono_ptyp__arrow; assumption ].
  -
    exfalso. destruct τ; simpl in Heq; try discriminate Heq. inversion Hm.
  -  exfalso. destruct τ; simpl in Heq; discriminate Heq.
  -   exfalso. destruct τ; simpl in Heq; discriminate Heq.
  -  exfalso. destruct τ; simpl in Heq; discriminate Heq.
Qed.

Lemma uskl_rsubst_ftv_target_bound : forall NM Θ Δρ Ψρ R' R,
  uskl_rsubst NM Θ Δρ Ψρ R' R ->
  ftvar_in_uskl R [<=] ftvar_in_uskl R' `union` Δρ.
Proof.
  intros NM Θ Δρ Ψρ R' R H; induction H; simpl; try fsetdec.
  -
    pick fresh α for
      (L `union` ftvar_in_uskl R' `union` ftvar_in_uskl R).
    pose proof (H0 α ltac:(clear - Fr; solve_notin_auto)) as Hα.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f α)).
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R' (uskl_var_f α)).
    simpl in *. clear - Hα H1 H2 Fr. fsetdec.
  -
    pick fresh α for
      (L `union` ftvar_in_uskl R' `union` ftvar_in_uskl R).
    pose proof (H0 α ltac:(clear - Fr; solve_notin_auto)) as Hα.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f α)).
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R' (uskl_var_f α)).
    simpl in *. clear - Hα H1 H2 Fr. fsetdec.
Qed.

Lemma a_wf_pskl_all_inv_empty : forall Θ P,
  {{ Θ ⨟ empty ⊢ₚₛ (pskl_all_syn P) }}a ->
  exists L, forall α, α `notin` L ->
    {{ ((α ~ abind_tvar) ++ Θ) ⨟ empty ⊢ₚₛ
         (open_pskl_wrt_pskl P (pskl_var_f α)) }}a.
Proof.
  intros Θ P H.
  destruct (a_wf_pskl_all_inv H) as [L Hb].
  exists L. intros α Hα.
  eapply a_wf_pskl_delta_mono.
  - apply Hb; exact Hα.
  - intros β _ Hβ. clear - Hβ; fsetdec.
Qed.

Lemma ad_partial_precise_msubst_all_tag_inv : forall NM Θ Δ Ψ Ψt κ P ε ψ Lt,
  {{ ⊢ Θ }}a ->
  msubst_lc κ ->
  (forall α, α `notin` Lt ->
     a_tags_sort NM Ψt (open_uskl_wrt_uskl ψ (uskl_var_f α))) ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ (pskl_all_syn P)) ⊑ᵖ[ Ψ ]
       (uskl_all_tag ε ψ) }}ad ->
  exists L Ψ0,
    (forall α, α `notin` L ->
       {{ Θ ⨟ (add α Δ) ⊢ˢ
         (msubst_pskl κ (open_pskl_wrt_pskl P (pskl_var_f α)))
         ⊑ᵖ[ Ψ0 ] (open_uskl_wrt_uskl ψ (uskl_var_f α)) }}ad) /\
    Ψ [=] add ε Ψ0 /\ Ψ0 [<=] Ψt.
Proof.
  intros NM Θ Δ Ψ Ψt κ P ε ψ Lt Hwf Hlcκ Htags H.
  simpl in H.
  inversion H as [ | | | L Θ1 Δ1 Ψ1 Ψ0 ε1 P1 ψ1 Hb HΨ | | | | | | ]; subst.
  assert (Hfam : forall α, α `notin` L `union` dom κ ->
            {{ Θ ⨟ (add α Δ) ⊢ˢ
              (msubst_pskl κ (open_pskl_wrt_pskl P (pskl_var_f α)))
              ⊑ᵖ[ Ψ0 ] (open_uskl_wrt_uskl ψ (uskl_var_f α)) }}ad).
  { intros α Hα.
    rewrite msubst_pskl_open_lc.
    - eapply ad_partial_precise_strengthen_tvar. apply Hb. solve_notin_auto.
    - exact Hlcκ.
    - solve_notin_auto. }
  exists (L `union` dom κ), Ψ0.
  refine (conj Hfam (conj HΨ _)).
  pick fresh α for (L `union` dom κ `union` Lt).
  eapply ad_partial_precise_tags_sub.
  - exact Hwf.
  - apply Hfam. solve_notin_auto.
  - apply a_tags_sort_d_tags with (NM := NM). apply Htags. solve_notin_auto.
Qed.
