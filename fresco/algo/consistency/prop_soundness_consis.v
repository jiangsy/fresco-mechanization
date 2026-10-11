(** Appendix B (consistency-proofs.tex), "Soundness of Consistency".

    The paper augments a solution to a consistency problem with four
    components (⊴, declarative consistency, and the two refinement
    directions), and proves the theorem "by mutual induction on the
    algorithmic consistency derivation together with the two auxiliary
    judgements of variable unification and assignment"
    (consistency-proofs.tex:1562).  Accordingly:

    - [a_unify_consis_sound]: the MUTUAL soundness bundle over
      [a_unify] + [a_consis] (the corrected [Flex-Flex-Assign] recurses
      into consistency, so the two judgments are mutually inductive).
      [a_assign] stays below the cycle (the mech reads Assign-Assign as
      continuing the assignment, cf. algo/def_rules.v) — its lemmas
      ([a_assign_sound], [a_assign_preserves_wf/_inv], ...) are plain
      inductions consumed by the bundle's FlexL/FlexR cases.
    - [a_consistag_sound_aux]: the DECORATED main induction
      (lemma:sound-decorated-consistency), a plain induction above the
      bundle — [a_consistag] is not in the recursion cycle; its Flex
      case consumes the bundle's [a_unify_sound].
    - [ad_pat_consis_refine_syn_mono] / [ad_pat_consis_refine_pskl_mono]:
      the paper's "since flexible variables do not depend on the rigid
      type variables in Δ" steps — a consistency derivation against a
      MONOTYPE painting yields both refinement components (FlexL/FlexR/
      Flex cases of part 1).
    - [ad_pat_consis_fold_def_q_mono]: Q-side (painted-side) definition
      folding at monotypes, the missing mirror of
      [ad_pat_consis_fold_def]. *)

Require Import src.fresco.algo_decl.prop_ctx_mono.
Require Import src.fresco.algo_decl.prop_consistency.
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
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo_decl.prop_stability.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo_decl.prop_refinement.
Require Import src.fresco.algo.consistency.prop_consis_monotype_equiv.
(* cluster 4: [a_consis_decorate] moved downstream, into §10 there *)
Require Import src.fresco.algo.consistency.prop_consis_rename.

Set Implicit Arguments.

(* ===================================================================== *)
(*  Monotype paintings                                                    *)
(* ===================================================================== *)

(** Painted skeletons of monotypes: no quantifiers, no ghosts. *)
Inductive mono_bskl : bskl -> Prop :=
| mono_bskl__unit  : mono_bskl bskl_unit
| mono_bskl__var   : forall α, mono_bskl (bskl_var_f α)
| mono_bskl__arrow : forall Q1 Q2,
    mono_bskl Q1 -> mono_bskl Q2 -> mono_bskl (bskl_arrow Q1 Q2).

Lemma mono_ptyp_to_bskl_syn : forall τ,
  mono_ptyp τ -> mono_bskl (ptyp_to_bskl_syn τ).
Proof.
  induction 1; unfold ptyp_to_bskl_syn in *; simpl; constructor; auto.
Qed.

Lemma mono_bskl_inh_syn : forall P,
  mono_bskl (pskl_to_bskl_inh P) ->
  pskl_to_bskl_syn P = pskl_to_bskl_inh P.
Proof.
  induction P; intros Hm; simpl in *; try reflexivity;
    inversion Hm; subst; f_equal; auto.
Qed.

(** Erasure is a left inverse of the syn-painted monotype embedding. *)
Lemma uskl_to_pskl_ptyp : forall A,
  uskl_to_pskl (ptyp_to_uskl_syn A) = ptyp_to_pskl A.
Proof.
  intros. rewrite <- pskl_to_uskl_ptyp. apply uskl_to_pskl_pskl_to_uskl.
Qed.

(* ===================================================================== *)
(*  Consistency at a monotype painting implies both refinements          *)
(*  (the paper's since-flexible-variables-do-not-depend-on-the-rigid-    *)
(*   type-variables-in-Δ steps, part 1 cases Flex / FlexL / FlexR)       *)
(* ===================================================================== *)

(** Skeleton wf survives removing a rigid entry the skeleton avoids
    (the [abind_tvar] instance of [a_wf_pskl_strip_mid]). *)
Lemma a_wf_pskl_strip_tvar : forall Θ1 α Θ2 Δ P,
  a_wf_pskl (Θ1 ++ (α ~ abind_tvar) ++ Θ2) Δ P ->
  α `notin` ftvar_in_pskl P ->
  a_wf_pskl (Θ1 ++ Θ2) Δ P.
Proof.
  intros * H Hfr. eapply a_wf_pskl_strip_mid; eauto.
Qed.

(* ===================================================================== *)
(*  Renaming the opened binder (∀-case crux 2: the coloured witness is    *)
(*  obtained at ONE fresh variable and transported to every cofinite      *)
(*  instance).  Helper layer: embeddings vs substitution / free vars.     *)
(* ===================================================================== *)

Lemma a_binds_tvar_insert_mid : forall y Θ1 (e : list (atom * abind)) Θ0,
  a_binds_tvar y (Θ1 ++ Θ0) ->
  a_binds_tvar y (Θ1 ++ e ++ Θ0).
Proof.
  intros * [Hb | [Hb | [τ Hb]]];
    [ left | right; left | right; right; exists τ ];
    auto using binds_weaken.
Qed.

(** Free variables of the paintings/readings are those of the skeleton. *)
Lemma ftvar_in_bskl_syn : forall P,
  ftvar_in_bskl (pskl_to_bskl_syn P) [=] ftvar_in_pskl P.
Proof.
  induction P; simpl; try fsetdec.
Qed.

Lemma ftvar_in_bskl_inh : forall P,
  ftvar_in_bskl (pskl_to_bskl_inh P) [=] ftvar_in_pskl P.
Proof.
  induction P; simpl; try fsetdec.
Qed.

(** Variable renaming commutes with the paintings. *)
Lemma subst_var_bskl_syn : forall P α α',
  subst_bskl_in_bskl (bskl_var_f α') α (pskl_to_bskl_syn P)
  = pskl_to_bskl_syn (subst_pskl_in_pskl (pskl_var_f α') α P).
Proof.
  induction P; intros; simpl; f_equal; auto.
  destruct (eq_var α α0); reflexivity.
Qed.

Lemma subst_var_bskl_inh : forall P α α',
  subst_bskl_in_bskl (bskl_var_f α') α (pskl_to_bskl_inh P)
  = pskl_to_bskl_inh (subst_pskl_in_pskl (pskl_var_f α') α P).
Proof.
  induction P; intros; simpl; f_equal; auto.
  destruct (eq_var α α0); reflexivity.
Qed.

(** Renaming a FREE variable [α] (not in Δ) to [β] (not in Δ): the
    context map may change arbitrarily as long as it keeps every other
    rigid-ish entry and binds [β]. *)
Lemma a_wf_pskl_rename_free : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  forall Θ' α β,
  (forall γ, a_binds_tvar γ Θ -> γ <> α -> a_binds_tvar γ Θ') ->
  a_binds_tvar β Θ' ->
  α `notin` Δ -> β `notin` Δ ->
  {{ Θ' ⨟ Δ ⊢ₚₛ (subst_pskl_in_pskl (pskl_var_f β) α P) }}a.
Proof.
  intros Θ Δ P H; induction H; intros Θ' α0 β Hm Hβ HαΔ HβΔ; simpl.
  - apply a_wf_pskl__unit.
  - destruct_if as [->|Hne]; apply a_wf_pskl__var; auto.
  - apply a_wf_pskl__arrow; auto.
  - apply a_wf_pskl__all
      with (L := L `union` singleton α0 `union` singleton β `union` Δ).
    intros α Hα.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hα; fsetdec | apply lc_pskl_var_f ].
    apply H0; [ clear - Hα; fsetdec | | | clear - Hα HαΔ; fsetdec
              | clear - Hα HβΔ; fsetdec ].
    + intros γ Hγ Hne. apply a_binds_tvar_cons_tvar.
      destruct (a_binds_tvar_cons_tvar_inv Hγ) as [-> | Hb]; auto.
    + apply a_binds_tvar_cons_tvar. auto.
  - apply a_wf_pskl__ghost.
  - apply a_wf_pskl__univ_ghost; [ apply guarded_pskl_subst_var; exact H | ].
    apply IHa_wf_pskl; [ | | clear; fsetdec | clear; fsetdec ].
    + intros γ Hγ Hne. apply a_binds_tvar_aenv_minus in Hγ as [Hγ HγΔ].
      apply a_binds_tvar_aenv_minus. auto.
    + apply a_binds_tvar_aenv_minus. auto.
Qed.

(** Renaming a variable [α] that the context binds AND Δ records (an
    opened ∀-binder) to a fresh [β]: [α] cannot occur under a ∀◇ (whose
    body is checked away from Δ), so the ∀◇ bodies are untouched. *)
Lemma a_wf_pskl_rename_bound : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  forall Θ' α β,
  (forall γ, a_binds_tvar γ Θ -> γ <> α -> a_binds_tvar γ Θ') ->
  a_binds_tvar β Θ' ->
  α `in` Δ ->
  β `notin` ftvar_in_pskl P ->
  {{ Θ' ⨟ (add β (remove α Δ)) ⊢ₚₛ
     (subst_pskl_in_pskl (pskl_var_f β) α P) }}a.
Proof.
  intros Θ Δ P H; induction H; intros Θ' α0 β Hm Hβ HαΔ HβP; simpl in *.
  - apply a_wf_pskl__unit.
  - destruct_if as [->|Hne]; apply a_wf_pskl__var; auto.
  - apply a_wf_pskl__arrow; [ apply IHa_wf_pskl1 | apply IHa_wf_pskl2 ];
      auto; clear - HβP; fsetdec.
  - apply a_wf_pskl__all
      with (L := L `union` singleton α0 `union` singleton β).
    intros α Hα.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hα; fsetdec | apply lc_pskl_var_f ].
    eapply a_wf_pskl_delta_mono; [ apply H0 | ].
    + clear - Hα; fsetdec.
    + intros γ Hγ Hne. apply a_binds_tvar_cons_tvar.
      destruct (a_binds_tvar_cons_tvar_inv Hγ) as [-> | Hb]; auto.
    + apply a_binds_tvar_cons_tvar. auto.
    + clear - HαΔ; fsetdec.
    + pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f α))
        as Hup. simpl in Hup. clear - Hup HβP Hα. fsetdec.
    + intros γ _ Hγ. clear - Hγ Hα. fsetdec.
  - apply a_wf_pskl__ghost.
  - assert (HαP : α0 `notin` ftvar_in_pskl P).
    { intros Hin.
      apply (a_wf_pskl_ftv_binds H0) in Hin.
      apply a_binds_tvar_aenv_minus in Hin as [_ Hc]. auto. }
    rewrite (subst_pskl_in_pskl_fresh_eq P (pskl_var_f β) α0 HαP).
    apply a_wf_pskl__univ_ghost; [ exact H | ].
    eapply a_wf_pskl_tvar_mono_ftv; [ exact H0 | ].
    intros γ Hγ Hb. apply a_binds_tvar_aenv_minus in Hb as [Hb HγΔ].
    apply a_binds_tvar_aenv_minus. split.
    + apply Hm; auto. intros ->. auto.
    + assert (Hγβ : γ <> β) by (intros ->; auto). clear - HγΔ Hγβ. fsetdec.
Qed.

(** Renaming a rigid context entry in skeleton well-formedness. *)
Lemma a_wf_pskl_rename_tvar : forall Θ1 α Θ0 Δ P β,
  a_wf_pskl (Θ1 ++ (α ~ abind_tvar) ++ Θ0) Δ P ->
  α `notin` Δ ->
  β `notin` Δ ->
  a_wf_pskl (Θ1 ++ (β ~ abind_tvar) ++ Θ0) Δ
    (subst_pskl_in_pskl (pskl_var_f β) α P).
Proof.
  intros * H HαΔ HβΔ.
  eapply a_wf_pskl_rename_free; [ exact H | | | exact HαΔ | exact HβΔ ].
  - intros γ Hγ Hne.
    apply (@a_binds_tvar_insert_mid γ Θ1 (β ~ abind_tvar) Θ0).
    eapply a_binds_tvar_strip_mid; eauto;
      try (intro Hc; inversion Hc; subst; congruence);
      try (intros τ0 Hc; inversion Hc).
  - unfold a_binds_tvar. left.
    unfold binds. apply in_or_app. right. left. reflexivity.
Qed.

(** Case-split every renaming decision in the goal; contradictory
    branches close by congruence. *)
Ltac destruct_var_eqs :=
  repeat destruct_if; subst; try congruence.

(** Renaming the opened binder in Θ-level skeleton consistency. *)
Lemma ad_pat_consis_rename_tvar : forall Ψ Θ1 α Θ0 R Q β',
  ad_pat_consis Ψ (Θ1 ++ (α ~ abind_tvar) ++ Θ0) R Q ->
  α `notin` dom (Θ1 ++ Θ0) ->
  (forall β τ, binds β (abind_flex_mono_def τ) (Θ1 ++ Θ0) ->
     α `notin` ftvar_in_ptyp τ) ->
  ad_pat_consis Ψ (Θ1 ++ (β' ~ abind_tvar) ++ Θ0)
    (subst_uskl_in_uskl (uskl_var_f β') α R)
    (subst_bskl_in_bskl (bskl_var_f β') α Q).
Proof.
  intros * H.
  remember (Θ1 ++ (α ~ abind_tvar) ++ Θ0) as Θfull eqn:HeqΘ.
  revert Θ1 HeqΘ.
  induction H; intros Θ1 ->; intros Hdom Hdefs; simpl.
  - (* unit *)
    apply ad_pat_consis__unit; auto.
  - (* var *)
    destruct_var_eqs.
    + apply ad_pat_consis__var; auto.
      unfold a_binds_tvar. left.
      unfold binds. apply in_or_app. right. left. reflexivity.
    + apply ad_pat_consis__var; auto.
      apply (@a_binds_tvar_insert_mid α0 Θ1 (β' ~ abind_tvar) Θ0).
      eapply a_binds_tvar_strip_mid; eauto;
        try (intro Hc; inversion Hc; subst; congruence);
        try (intros τ0 Hc; inversion Hc).
  - (* arrow *)
    eapply ad_pat_consis__arrow; eauto.
  - (* forall_inh_tagged *)
    eapply ad_pat_consis__forall_inh_tagged
      with (L := L `union` singleton α); eauto.
    intros α0 Hα0.
    assert (Hαx : α <> α0) by fsetdec.
    rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
      auto using lc_uskl_var_f.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
    assert (HXL : α0 `notin` L) by fsetdec.
    apply (H0 α0 HXL ((α0 ~ abind_tvar) ++ Θ1)); auto.
    all: try (simpl; repeat rewrite dom_app in *; fsetdec).
    all: intros β τ Hb;
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | eauto ].
  - (* forall_inh_untagged *)
    eapply ad_pat_consis__forall_inh_untagged
      with (L := L `union` singleton α); eauto.
    intros α0 Hα0.
    assert (Hαx : α <> α0) by fsetdec.
    rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
      auto using lc_uskl_var_f.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
    assert (HXL : α0 `notin` L) by fsetdec.
    apply (H0 α0 HXL ((α0 ~ abind_tvar) ++ Θ1)); auto.
    all: try (simpl; repeat rewrite dom_app in *; fsetdec).
    all: intros β τ Hb;
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | eauto ].
  - (* forall_syn_tagged *)
    eapply ad_pat_consis__forall_syn_tagged
      with (L := L `union` singleton α); eauto.
    intros α0 Hα0.
    assert (Hαx : α <> α0) by fsetdec.
    rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
      auto using lc_uskl_var_f.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
    assert (HXL : α0 `notin` L) by fsetdec.
    apply (H0 α0 HXL ((α0 ~ abind_tvar) ++ Θ1)); auto.
    all: try (simpl; repeat rewrite dom_app in *; fsetdec).
    all: intros β τ Hb;
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | eauto ].
  - (* forall_syn *)
    eapply ad_pat_consis__forall_syn
      with (L := L `union` singleton α); eauto.
    intros α0 Hα0.
    assert (Hαx : α <> α0) by fsetdec.
    rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
      auto using lc_uskl_var_f.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
    assert (HXL : α0 `notin` L) by fsetdec.
    apply (H0 α0 HXL ((α0 ~ abind_tvar) ++ Θ1)); auto.
    all: try (simpl; repeat rewrite dom_app in *; fsetdec).
    all: intros β τ Hb;
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | eauto ].
  - (* ghostg *)
    apply ad_pat_consis__ghostg; auto.
  - (* dot_univ_ghost *)
    apply ad_pat_consis__dot_univ_ghost; auto.
  - (* ghost *)
    rewrite subst_var_bskl_inh.
    apply ad_pat_consis__ghost; auto.
  - (* univ_ghost *)
    apply ad_pat_consis__univ_ghost; auto.
  - (* univ_ghost_inh *)
    apply ad_pat_consis__univ_ghost_inh
      with (L := L `union` singleton α).
    intros α0 Hα0.
    assert (Hαx : α <> α0) by fsetdec.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
    assert (HXL : α0 `notin` L) by fsetdec.
    apply (H0 α0 HXL ((α0 ~ abind_tvar) ++ Θ1)); auto.
    all: try (simpl; repeat rewrite dom_app in *; fsetdec).
    all: intros β τ Hb;
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | eauto ].
  - (* univ_ghost_drop *)
    apply ad_pat_consis__univ_ghost_drop; auto.
  - (* flex_l *)
    assert (Hb' : binds α0 (abind_flex_mono_def τ) (Θ1 ++ Θ0)).
    { eapply binds_strip_mid; eauto. intro Hc; inversion Hc. }
    assert (Hαne : α0 <> α).
    { intro; subst. apply binds_In in Hb'. fsetdec. }
    assert (Hfr : α `notin` ftvar_in_uskl (ptyp_to_uskl_syn τ)).
    { rewrite ftvar_ptyp_to_uskl_syn. eauto. }
    destruct_var_eqs.
    eapply ad_pat_consis__flex_l
      with (τ := τ);
      [ apply (@binds_weaken abind α0 (abind_flex_mono_def τ)
                 Θ1 (β' ~ abind_tvar) Θ0); auto | ].
    rewrite <- (subst_uskl_in_uskl_fresh_eq
                  (ptyp_to_uskl_syn τ) (uskl_var_f β') α Hfr).
    auto.
  - (* flex_r *)
    assert (Hb' : binds α0 (abind_flex_mono_def τ) (Θ1 ++ Θ0)).
    { eapply binds_strip_mid; eauto. intro Hc; inversion Hc. }
    assert (Hαne : α0 <> α).
    { intro; subst. apply binds_In in Hb'. fsetdec. }
    assert (Hfr : α `notin` ftvar_in_bskl (ptyp_to_bskl_syn τ)).
    { rewrite ftvar_ptyp_to_bskl_syn. eauto. }
    destruct_var_eqs.
    eapply ad_pat_consis__flex_r
      with (τ := τ);
      [ apply (@binds_weaken abind α0 (abind_flex_mono_def τ)
                 Θ1 (β' ~ abind_tvar) Θ0); auto | ].
    rewrite <- (subst_bskl_in_bskl_fresh_eq
                  (ptyp_to_bskl_syn τ) (bskl_var_f β') α Hfr).
    auto.
Qed.

(* --------------------------------------------------------------------- *)
(*  Δ-side renaming                                                       *)
(* --------------------------------------------------------------------- *)

(** Δ-side renaming: the ∀-cases obtain their per-instance refinement
    components by renaming the one-fresh-α witness, in Δ AND in the
    context at once (the ∀ rule records its binder in both).  [α] lives
    in Δ, so the ghost fills avoid it and are untouched; [β'] avoids the
    right-hand side, hence every fill (a fill is a sub-skeleton of the
    right-hand side), so the grown Δ still misses them.  The context map
    only has to carry the flexible definitions. *)
Lemma ad_refine_syn_rename_gen : forall Θ Δ Q Q',
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad ->
  forall Θ' α β',
  α `in` Δ ->
  β' `notin` ftvar_in_bskl Q' ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     binds β (abind_flex_mono_def τ) Θ' /\ β <> α /\
     α `notin` ftvar_in_ptyp τ /\ β' `notin` ftvar_in_ptyp τ) ->
  {{ Θ' ⨟ (add β' Δ) ⊢ᵣ (subst_bskl_in_bskl (bskl_var_f β') α Q)
       ⊳ (subst_bskl_in_bskl (bskl_var_f β') α Q') }}ad.
Proof.
  intros * H; induction H; intros Θ' α0 β' HαΔ Hβ Hdefs; simpl in *.
  - (* unit *)
    apply ad_refine_syn__unit.
  - (* var *)
    destruct_var_eqs; apply ad_refine_syn__var.
  - (* arrow *)
    apply ad_refine_syn_arrow_intro;
      [ apply IHad_refine_syn1 | apply IHad_refine_syn2 ];
      auto; clear - Hβ; fsetdec.
  - (* all *)
    apply ad_refine_syn_all_intro
      with (L := L `union` singleton α0 `union` singleton β').
    intros α Hα.
    assert (Hαx : α0 <> α) by (clear - Hα; fsetdec).
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
    apply ad_refine_syn_delta_mono with (Δ0 := add β' (add α Δ));
      [ | clear; fsetdec ].
    apply H1; [ clear - Hα; fsetdec | clear - HαΔ; fsetdec | | ].
    + pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q' (bskl_var_f α))
        as Hup. simpl in Hup. clear - Hup Hβ Hα. fsetdec.
    + intros β τ Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
        [ discriminate | ].
      destruct (Hdefs β τ Hb') as [Hb'' Hrest].
      split; [ unfold binds; right; exact Hb'' | exact Hrest ].
  (* [P] is the ghost rule's OWN fill binder ([ad_refine_syn__ghost]),
     auto-bound by the induction — not this lemma's Q'. *)
  - (* ghost: the fill avoids α (it is in Δ) and β' (it is the right side) *)
    assert (Hfr : α0 `notin` ftvar_in_pskl P)
      by (clear - H HαΔ; fsetdec).
    rewrite subst_var_bskl_syn.
    rewrite (subst_pskl_in_pskl_fresh_eq P (pskl_var_f β') α0 Hfr).
    rewrite ftvar_in_bskl_syn in Hβ.
    apply ad_refine_syn__ghost. clear - H Hβ; fsetdec.
  - (* univ_ghost_remove *)
    apply ad_refine_syn_univ_ghost_remove_intro; auto.
  - (* univ_ghost_fill *)
    apply ad_refine_syn_univ_ghost_fill_intro
      with (L := L `union` singleton α0 `union` singleton β').
    intros α Hα.
    assert (Hαx : α0 <> α) by (clear - Hα; fsetdec).
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
    replace (bskl_univ_ghost (subst_bskl_in_bskl (bskl_var_f β') α0 Q))
      with (subst_bskl_in_bskl (bskl_var_f β') α0 (bskl_univ_ghost Q))
      by reflexivity.
    apply H1; [ clear - Hα; fsetdec | exact HαΔ | | ].
    + pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q' (bskl_var_f α))
        as Hup. simpl in Hup. clear - Hup Hβ Hα. fsetdec.
    + intros β τ Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
        [ discriminate | ].
      destruct (Hdefs β τ Hb') as [Hb'' Hrest].
      split; [ unfold binds; right; exact Hb'' | exact Hrest ].
  - (* univ_ghost_keep *)
    apply ad_refine_syn_univ_ghost_keep_intro; auto.
  - (* flex_l *)
    destruct (Hdefs α τ H) as [Hb' [Hαne [Hατ Hβτ]]].
    assert (Hfr : α0 `notin` ftvar_in_bskl (ptyp_to_bskl_syn τ))
      by (rewrite ftvar_ptyp_to_bskl_syn; exact Hατ).
    destruct_var_eqs.
    apply ad_refine_syn__flex_l with (τ := τ); [ exact Hb' | ].
    rewrite <- (subst_bskl_in_bskl_fresh_eq
                  (ptyp_to_bskl_syn τ) (bskl_var_f β') α0 Hfr).
    auto.
  - (* flex_r *)
    destruct (Hdefs α τ H) as [Hb' [Hαne [Hατ Hβτ]]].
    assert (Hfr : α0 `notin` ftvar_in_bskl (ptyp_to_bskl_syn τ))
      by (rewrite ftvar_ptyp_to_bskl_syn; exact Hατ).
    destruct_var_eqs.
    apply ad_refine_syn__flex_r with (τ := τ); [ exact Hb' | ].
    rewrite <- (subst_bskl_in_bskl_fresh_eq
                  (ptyp_to_bskl_syn τ) (bskl_var_f β') α0 Hfr).
    apply IHad_refine_syn; auto.
    rewrite ftvar_ptyp_to_bskl_syn. exact Hβτ.
Qed.

Lemma ad_refine_pskl_rename_gen : forall Θ Δ P P',
  {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ P' }}ad ->
  forall Θ' α β',
  α `in` Δ ->
  β' `notin` ftvar_in_pskl P' ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     binds β (abind_flex_mono_def τ) Θ' /\ β <> α /\
     α `notin` ftvar_in_ptyp τ /\ β' `notin` ftvar_in_ptyp τ) ->
  {{ Θ' ⨟ (add β' Δ) ⊢ᵣₚ (subst_pskl_in_pskl (pskl_var_f β') α P)
       ⊳ (subst_pskl_in_pskl (pskl_var_f β') α P') }}ad.
Proof.
  intros * H; induction H; intros Θ' α0 β' HαΔ Hβ Hdefs; simpl in *.
  - (* unit *)
    apply ad_refine_pskl__unit.
  - (* var *)
    destruct_var_eqs; apply ad_refine_pskl__var.
  - (* arrow *)
    apply ad_refine_pskl__arrow;
      [ apply IHad_refine_pskl1 | apply IHad_refine_pskl2 ];
      auto; clear - Hβ; fsetdec.
  - (* all *)
    apply ad_refine_pskl__all
      with (L := L `union` singleton α0 `union` singleton β').
    intros α Hα.
    assert (Hαx : α0 <> α) by (clear - Hα; fsetdec).
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      auto using lc_pskl_var_f.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      auto using lc_pskl_var_f.
    apply ad_refine_pskl_delta_mono with (Δ0 := add β' (add α Δ));
      [ | clear; fsetdec ].
    apply H0; [ clear - Hα; fsetdec | clear - HαΔ; fsetdec | | ].
    + pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P' (pskl_var_f α))
        as Hup. simpl in Hup. clear - Hup Hβ Hα. fsetdec.
    + intros β τ Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
        [ discriminate | ].
      destruct (Hdefs β τ Hb') as [Hb'' Hrest].
      split; [ unfold binds; right; exact Hb'' | exact Hrest ].
  - (* ghost *)
    assert (Hfr : α0 `notin` ftvar_in_pskl P')
      by (clear - H HαΔ; fsetdec).
    rewrite (subst_pskl_in_pskl_fresh_eq P' (pskl_var_f β') α0 Hfr).
    apply ad_refine_pskl__ghost. clear - H Hβ; fsetdec.
  - (* univ_ghost_remove *)
    apply ad_refine_pskl__univ_ghost_remove; auto.
  - (* univ_ghost_fill *)
    apply ad_refine_pskl__univ_ghost_fill
      with (L := L `union` singleton α0 `union` singleton β').
    intros α Hα.
    assert (Hαx : α0 <> α) by (clear - Hα; fsetdec).
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      auto using lc_pskl_var_f.
    replace (pskl_univ_ghost (subst_pskl_in_pskl (pskl_var_f β') α0 P))
      with (subst_pskl_in_pskl (pskl_var_f β') α0 (pskl_univ_ghost P))
      by reflexivity.
    apply H0; [ clear - Hα; fsetdec | exact HαΔ | | ].
    + pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P' (pskl_var_f α))
        as Hup. simpl in Hup. clear - Hup Hβ Hα. fsetdec.
    + intros β τ Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
        [ discriminate | ].
      destruct (Hdefs β τ Hb') as [Hb'' Hrest].
      split; [ unfold binds; right; exact Hb'' | exact Hrest ].
  - (* univ_ghost_keep *)
    apply ad_refine_pskl__univ_ghost_keep; auto.
  - (* flex_l *)
    destruct (Hdefs α τ H) as [Hb' [Hαne [Hατ Hβτ]]].
    assert (Hfr : α0 `notin` ftvar_in_pskl (ptyp_to_pskl τ))
      by (rewrite ftvar_ptyp_to_pskl; exact Hατ).
    destruct_var_eqs.
    apply ad_refine_pskl__flex_l with (τ := τ); [ exact Hb' | ].
    rewrite <- (subst_pskl_in_pskl_fresh_eq
                  (ptyp_to_pskl τ) (pskl_var_f β') α0 Hfr).
    auto.
  - (* flex_r *)
    destruct (Hdefs α τ H) as [Hb' [Hαne [Hατ Hβτ]]].
    assert (Hfr : α0 `notin` ftvar_in_pskl (ptyp_to_pskl τ))
      by (rewrite ftvar_ptyp_to_pskl; exact Hατ).
    destruct_var_eqs.
    apply ad_refine_pskl__flex_r with (τ := τ); [ exact Hb' | ].
    rewrite <- (subst_pskl_in_pskl_fresh_eq
                  (ptyp_to_pskl τ) (pskl_var_f β') α0 Hfr).
    apply IHad_refine_pskl; auto.
    rewrite ftvar_ptyp_to_pskl. exact Hβτ.
Qed.

(** The fixed-context instance.  [β'] must avoid the right-hand side and
    the context's definitions (otherwise a fill or a looked-up definition
    could mention it while the renamed Δ forbids it). *)
Lemma ad_refine_syn_rename : forall Θ Δ α Q Q' β',
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad ->
  α `in` Δ ->
  α `notin` dom Θ ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     α `notin` ftvar_in_ptyp τ) ->
  β' `notin` ftvar_in_bskl Q' ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     β' `notin` ftvar_in_ptyp τ) ->
  {{ Θ ⨟ (add β' Δ) ⊢ᵣ (subst_bskl_in_bskl (bskl_var_f β') α Q)
       ⊳ (subst_bskl_in_bskl (bskl_var_f β') α Q') }}ad.
Proof.
  intros * H HαΔ Hdom Hdefs Hβ Hdefsβ.
  eapply ad_refine_syn_rename_gen; [ exact H | exact HαΔ | exact Hβ | ].
  intros β τ Hb. repeat split; eauto.
  intros Heq; subst. apply binds_In in Hb. fsetdec.
Qed.

(* --------------------------------------------------------------------- *)
(*  Consistency against a MONOTYPE painting yields both refinements (the  *)
(*  flex cases of the main induction).  The ghost rule's Δ-condition is   *)
(*  inherited from the painted side and the context's definitions (the    *)
(*  problem invariant: no flexible variable depends on Δ1/Δ2).            *)
(* --------------------------------------------------------------------- *)

Lemma ad_pat_consis_refine_syn_mono : forall Ψ Θ R Q,
  ad_pat_consis Ψ Θ R Q ->
  {{ ⊢ Θ }}a ->
  mono_bskl Q ->
  forall Δ,
  Δ ∩ ftvar_in_bskl Q [=] empty ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     Δ ∩ ftvar_in_ptyp τ [=] empty) ->
  {{ Θ ⨟ Δ ⊢ᵣ (pskl_to_bskl_inh (uskl_to_pskl R)) ⊳ Q }}ad.
Proof.
  intros Ψ Θ R Q H Hwf; induction H; intros HmQ Δ HΔQ HΔdefs; simpl;
    try solve [ inversion HmQ ].
  - (* unit *)
    apply ad_refine_syn__unit.
  - (* var (rigid) *)
    apply ad_refine_syn__var.
  - (* arrow *)
    inversion HmQ; subst.
    simpl in HΔQ.
    apply ad_refine_syn_arrow_intro;
      [ apply IHad_pat_consis1 | apply IHad_pat_consis2 ];
      auto; clear - HΔQ; fsetdec.
  - (* ghost *)
    rewrite <- (mono_bskl_inh_syn P HmQ).
    apply ad_refine_syn__ghost; rewrite <- ftvar_in_bskl_inh; auto.
  - (* univ_ghost_drop *)
    apply ad_refine_syn_univ_ghost_remove_intro; auto.
  - (* flex_l *)
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    apply ad_refine_syn__flex_l with (τ := τ); [ exact H | ].
    specialize (IHad_pat_consis Hwf HmQ Δ HΔQ HΔdefs).
    rewrite uskl_to_pskl_ptyp in IHad_pat_consis.
    rewrite (ptyp_to_bskl_inh_syn_eq Hmτ) in IHad_pat_consis.
    exact IHad_pat_consis.
  - (* flex_r *)
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    apply ad_refine_syn__flex_r with (τ := τ); [ exact H | ].
    apply IHad_pat_consis; auto using mono_ptyp_to_bskl_syn;
      rewrite ftvar_ptyp_to_bskl_syn; eauto.
Qed.

Lemma ad_pat_consis_refine_pskl_mono : forall Ψ Θ R Q,
  ad_pat_consis Ψ Θ R Q ->
  {{ ⊢ Θ }}a ->
  mono_bskl Q ->
  forall Δ,
  Δ ∩ ftvar_in_bskl Q [=] empty ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     Δ ∩ ftvar_in_ptyp τ [=] empty) ->
  {{ Θ ⨟ Δ ⊢ᵣₚ (uskl_to_pskl R) ⊳ (bskl_to_pskl Q) }}ad.
Proof.
  intros Ψ Θ R Q H Hwf; induction H; intros HmQ Δ HΔQ HΔdefs; simpl;
    try solve [ inversion HmQ ].
  - (* unit *)
    apply ad_refine_pskl__unit.
  - (* var (rigid) *)
    apply ad_refine_pskl__var.
  - (* arrow *)
    inversion HmQ; subst.
    simpl in HΔQ.
    apply ad_refine_pskl__arrow;
      [ apply IHad_pat_consis1 | apply IHad_pat_consis2 ];
      auto; clear - HΔQ; fsetdec.
  - (* ghost *)
    rewrite bskl_to_pskl_pskl_to_bskl_inh.
    apply ad_refine_pskl__ghost; rewrite <- ftvar_in_bskl_inh; auto.
  - (* univ_ghost_drop *)
    apply ad_refine_pskl__univ_ghost_remove; auto.
  - (* flex_l *)
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    apply ad_refine_pskl__flex_l with (τ := τ); [ exact H | ].
    specialize (IHad_pat_consis Hwf HmQ Δ HΔQ HΔdefs).
    rewrite uskl_to_pskl_ptyp in IHad_pat_consis.
    exact IHad_pat_consis.
  - (* flex_r *)
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    apply ad_refine_pskl__flex_r with (τ := τ); [ exact H | ].
    specialize (IHad_pat_consis Hwf (mono_ptyp_to_bskl_syn Hmτ) Δ).
    rewrite (bskl_to_pskl_ptyp_to_bskl_syn τ) in IHad_pat_consis.
    apply IHad_pat_consis; auto;
      rewrite ftvar_ptyp_to_bskl_syn; eauto.
Qed.

(* --------------------------------------------------------------------- *)
(*  Θ-side renaming (ForallSyn/UnivGhost1 cases: the univ_ghost_fill-shaped  *)
(*  components keep the binder rigid in the context, so the per-instance  *)
(*  transport renames the Θ entry).                                       *)
(* --------------------------------------------------------------------- *)

Lemma ad_refine_syn_rename_ctx_gen : forall Θ1 α Θ0 Δ Q Q' β',
  {{ (Θ1 ++ (α ~ abind_tvar) ++ Θ0) ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad ->
  α `notin` dom (Θ1 ++ Θ0) ->
  (forall β τ, binds β (abind_flex_mono_def τ) (Θ1 ++ Θ0) ->
     α `notin` ftvar_in_ptyp τ) ->
  β' `notin` Δ ->
  {{ (Θ1 ++ (β' ~ abind_tvar) ++ Θ0) ⨟ Δ ⊢ᵣ
    (subst_bskl_in_bskl (bskl_var_f β') α Q)
    ⊳ (subst_bskl_in_bskl (bskl_var_f β') α Q') }}ad.
Proof.
  intros * H.
  remember (Θ1 ++ (α ~ abind_tvar) ++ Θ0) as Θfull eqn:HeqΘ.
  revert Θ1 HeqΘ.
  induction H; intros Θ1 ->; intros Hdom Hdefs HβΔ; simpl.
  - (* unit *)
    apply ad_refine_syn__unit.
  - (* var *)
    destruct_var_eqs; apply ad_refine_syn__var.
  - (* arrow *)
    apply ad_refine_syn_arrow_intro; auto.
  - (* all *)
    apply ad_refine_syn_all_intro
      with (L := L `union` singleton α `union` singleton β').
    intros α0 Hα0.
    assert (Hαx : α <> α0) by (clear - Hα0; fsetdec).
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
    assert (Hα0L : α0 `notin` L) by (clear - Hα0; fsetdec).
    apply (H1 α0 Hα0L ((α0 ~ abind_tvar) ++ Θ1)); auto.
    all: try (simpl; repeat rewrite dom_app in *; clear - Hdom Hαx HβΔ Hα0;
              fsetdec).
    all: intros β τ Hb;
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | eauto ].
  - (* ghost *)
    rewrite subst_var_bskl_syn.
    apply ad_refine_syn__ghost.
    pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                  P (pskl_var_f β') α) as Hup.
    simpl in Hup. clear - H HβΔ Hup. fsetdec.
  - (* univ_ghost_remove *)
    apply ad_refine_syn_univ_ghost_remove_intro; auto.
  - (* univ_ghost_fill *)
    apply ad_refine_syn_univ_ghost_fill_intro
      with (L := L `union` singleton α).
    intros α0 Hα0.
    assert (Hαx : α <> α0) by fsetdec.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
    replace (bskl_univ_ghost (subst_bskl_in_bskl (bskl_var_f β') α Q))
      with (subst_bskl_in_bskl (bskl_var_f β') α (bskl_univ_ghost Q))
      by reflexivity.
    apply (H1 α0 ltac:(auto) ((α0 ~ abind_tvar) ++ Θ1)); auto.
    all: try (simpl; repeat rewrite dom_app in *; fsetdec).
    all: intros β τ Hb;
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | eauto ].
  - (* univ_ghost_keep *)
    apply ad_refine_syn_univ_ghost_keep_intro; auto.
  - (* flex_l *)
    assert (Hb' : binds α0 (abind_flex_mono_def τ) (Θ1 ++ Θ0)).
    { eapply binds_strip_mid; eauto. intro Hc; inversion Hc. }
    assert (Hαne : α0 <> α).
    { intro; subst. apply binds_In in Hb'. fsetdec. }
    assert (Hfr : α `notin` ftvar_in_bskl (ptyp_to_bskl_syn τ)).
    { rewrite ftvar_ptyp_to_bskl_syn. eauto. }
    destruct_var_eqs.
    apply ad_refine_syn__flex_l with (τ := τ);
      [ apply (@binds_weaken abind α0 (abind_flex_mono_def τ)
                 Θ1 (β' ~ abind_tvar) Θ0); auto | ].
    rewrite <- (subst_bskl_in_bskl_fresh_eq
                  (ptyp_to_bskl_syn τ) (bskl_var_f β') α Hfr).
    auto.
  - (* flex_r *)
    assert (Hb' : binds α0 (abind_flex_mono_def τ) (Θ1 ++ Θ0)).
    { eapply binds_strip_mid; eauto. intro Hc; inversion Hc. }
    assert (Hαne : α0 <> α).
    { intro; subst. apply binds_In in Hb'. fsetdec. }
    assert (Hfr : α `notin` ftvar_in_bskl (ptyp_to_bskl_syn τ)).
    { rewrite ftvar_ptyp_to_bskl_syn. eauto. }
    destruct_var_eqs.
    apply ad_refine_syn__flex_r with (τ := τ);
      [ apply (@binds_weaken abind α0 (abind_flex_mono_def τ)
                 Θ1 (β' ~ abind_tvar) Θ0); auto | ].
    rewrite <- (subst_bskl_in_bskl_fresh_eq
                  (ptyp_to_bskl_syn τ) (bskl_var_f β') α Hfr).
    auto.
Qed.

Lemma ad_refine_pskl_rename_ctx_gen : forall Θ1 α Θ0 Δ P P' β',
  {{ (Θ1 ++ (α ~ abind_tvar) ++ Θ0) ⨟ Δ ⊢ᵣₚ P ⊳ P' }}ad ->
  α `notin` dom (Θ1 ++ Θ0) ->
  (forall β τ, binds β (abind_flex_mono_def τ) (Θ1 ++ Θ0) ->
     α `notin` ftvar_in_ptyp τ) ->
  β' `notin` Δ ->
  {{ (Θ1 ++ (β' ~ abind_tvar) ++ Θ0) ⨟ Δ ⊢ᵣₚ
    (subst_pskl_in_pskl (pskl_var_f β') α P)
    ⊳ (subst_pskl_in_pskl (pskl_var_f β') α P') }}ad.
Proof.
  intros * H.
  remember (Θ1 ++ (α ~ abind_tvar) ++ Θ0) as Θfull eqn:HeqΘ.
  revert Θ1 HeqΘ.
  induction H; intros Θ1 ->; intros Hdom Hdefs HβΔ; simpl.
  - (* unit *)
    apply ad_refine_pskl__unit.
  - (* var *)
    destruct_var_eqs; apply ad_refine_pskl__var.
  - (* arrow *)
    apply ad_refine_pskl__arrow; auto.
  - (* all *)
    apply ad_refine_pskl__all
      with (L := L `union` singleton α `union` singleton β').
    intros α0 Hα0.
    assert (Hαx : α <> α0) by (clear - Hα0; fsetdec).
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      auto using lc_pskl_var_f.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      auto using lc_pskl_var_f.
    assert (Hα0L : α0 `notin` L) by (clear - Hα0; fsetdec).
    apply (H0 α0 Hα0L ((α0 ~ abind_tvar) ++ Θ1)); auto.
    all: try (simpl; repeat rewrite dom_app in *; clear - Hdom Hαx HβΔ Hα0;
              fsetdec).
    all: intros β τ Hb;
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | eauto ].
  - (* ghost *)
    apply ad_refine_pskl__ghost.
    pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                  P' (pskl_var_f β') α) as Hup.
    simpl in Hup. clear - H HβΔ Hup. fsetdec.
  - (* univ_ghost_remove *)
    apply ad_refine_pskl__univ_ghost_remove; auto.
  - (* univ_ghost_fill *)
    apply ad_refine_pskl__univ_ghost_fill
      with (L := L `union` singleton α).
    intros α0 Hα0.
    assert (Hαx : α <> α0) by fsetdec.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      auto using lc_pskl_var_f.
    replace (pskl_univ_ghost (subst_pskl_in_pskl (pskl_var_f β') α P))
      with (subst_pskl_in_pskl (pskl_var_f β') α (pskl_univ_ghost P))
      by reflexivity.
    apply (H0 α0 ltac:(auto) ((α0 ~ abind_tvar) ++ Θ1)); auto.
    all: try (simpl; repeat rewrite dom_app in *; fsetdec).
    all: intros β τ Hb;
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | eauto ].
  - (* univ_ghost_keep *)
    apply ad_refine_pskl__univ_ghost_keep; auto.
  - (* flex_l *)
    assert (Hb' : binds α0 (abind_flex_mono_def τ) (Θ1 ++ Θ0)).
    { eapply binds_strip_mid; eauto. intro Hc; inversion Hc. }
    assert (Hαne : α0 <> α).
    { intro; subst. apply binds_In in Hb'. fsetdec. }
    assert (Hfr : α `notin` ftvar_in_pskl (ptyp_to_pskl τ)).
    { rewrite ftvar_ptyp_to_pskl. eauto. }
    destruct_var_eqs.
    apply ad_refine_pskl__flex_l with (τ := τ);
      [ apply (@binds_weaken abind α0 (abind_flex_mono_def τ)
                 Θ1 (β' ~ abind_tvar) Θ0); auto | ].
    rewrite <- (subst_pskl_in_pskl_fresh_eq
                  (ptyp_to_pskl τ) (pskl_var_f β') α Hfr).
    auto.
  - (* flex_r *)
    assert (Hb' : binds α0 (abind_flex_mono_def τ) (Θ1 ++ Θ0)).
    { eapply binds_strip_mid; eauto. intro Hc; inversion Hc. }
    assert (Hαne : α0 <> α).
    { intro; subst. apply binds_In in Hb'. fsetdec. }
    assert (Hfr : α `notin` ftvar_in_pskl (ptyp_to_pskl τ)).
    { rewrite ftvar_ptyp_to_pskl. eauto. }
    destruct_var_eqs.
    apply ad_refine_pskl__flex_r with (τ := τ);
      [ apply (@binds_weaken abind α0 (abind_flex_mono_def τ)
                 Θ1 (β' ~ abind_tvar) Θ0); auto | ].
    rewrite <- (subst_pskl_in_pskl_fresh_eq
                  (ptyp_to_pskl τ) (pskl_var_f β') α Hfr).
    auto.
Qed.

(* ===================================================================== *)
(*  The part-1 problem invariants and their preservation                  *)
(*                                                                        *)
(*  The paper's augmented solution requires that no flexible variables    *)
(*  in Θ depend on variables in Δ1 and Δ2, and the induction needs it     *)
(*  PRESERVED by every unifyvar/assignvar step.  Preservation rests on    *)
(*  the positional discipline of the algorithm: the Δ-variables are the   *)
(*  derivation's own head-openings, so they sit above every non-rigid     *)
(*  entry ([flex_above_free]); Assign-SkipRigid's occurs condition then   *)
(*  witnesses that assignment payloads avoid them, and Assign-SolveM's    *)
(*  used-name freshness keeps the guessed names off them.                 *)
(* ===================================================================== *)

(** No definition mentions a Δ-variable. *)
Definition no_flex_dep (Δ : atoms) (Θ : aenv) : Prop :=
  forall β τ, binds β (abind_flex_mono_def τ) Θ ->
  Δ ∩ ftvar_in_ptyp τ [=] empty.

(** Δ-names sit above (and differ from) every non-rigid entry. *)
Definition flex_above_free (Δ : atoms) (Θ : aenv) : Prop :=
  forall Θ1 β (b : abind) Θ2, Θ = Θ1 ++ (β, b) :: Θ2 ->
  b <> abind_tvar ->
  Δ ∩ (add β (dom Θ2)) [=] empty.

Lemma no_flex_dep_cong : forall Δ Δ' Θ,
  Δ [=] Δ' -> no_flex_dep Δ Θ -> no_flex_dep Δ' Θ.
Proof.
  intros Δ Δ' Θ Heq H β τ Hb. pose proof (H β τ Hb) as Hh.
  clear - Heq Hh. fsetdec.
Qed.

Lemma faf_cong : forall Δ Δ' Θ,
  Δ [=] Δ' -> flex_above_free Δ Θ -> flex_above_free Δ' Θ.
Proof.
  intros Δ Δ' Θ Heq H Θ1 β b Θ2 Hsp Hne.
  pose proof (H Θ1 β b Θ2 Hsp Hne) as Hh. clear - Heq Hh. fsetdec.
Qed.

(** The trivial Δ-invariants at Δ = ∅.  ⚙ Moved here 2026-10-10 from
    deco_algo/prop_decorate_sub.v. *)
Lemma rig_empty : forall Θ : aenv,
  forall α, α `in` (empty `union` empty) -> binds α abind_tvar Θ.
Proof. intros Θ α Hα. exfalso. clear - Hα. fsetdec. Qed.

Lemma no_flex_dep_empty : forall Θ, no_flex_dep (empty `union` empty) Θ.
Proof. intros Θ β τ Hb. clear. fsetdec. Qed.

Lemma faf_empty : forall Θ, flex_above_free (empty `union` empty) Θ.
Proof. intros Θ Θ1 β b Θ2 Heq Hne. clear. fsetdec. Qed.


Lemma no_flex_dep_tail : forall Δ (c : atom) (b : abind) Θ,
  no_flex_dep Δ ((c ~ b) ++ Θ) ->
  no_flex_dep Δ Θ.
Proof.
  intros * H β τ Hb. apply (H β τ). unfold binds; right; exact Hb.
Qed.

Lemma faf_tail : forall Δ (c : atom) (b : abind) Θ,
  flex_above_free Δ ((c ~ b) ++ Θ) ->
  flex_above_free Δ Θ.
Proof.
  intros * H Θ1 β b0 Θ2 -> Hne.
  apply (H ((c ~ b) ++ Θ1) β b0 Θ2); auto.
Qed.

Lemma faf_head : forall Δ (c : atom) (b : abind) Θ,
  flex_above_free Δ ((c ~ b) ++ Θ) ->
  b <> abind_tvar ->
  Δ ∩ (add c (dom Θ)) [=] empty.
Proof.
  intros * H Hne. apply (H nil c b Θ); auto.
Qed.

Lemma faf_cons : forall Δ (c : atom) (b : abind) Θ,
  (b <> abind_tvar -> Δ ∩ (add c (dom Θ)) [=] empty) ->
  flex_above_free Δ Θ ->
  flex_above_free Δ ((c ~ b) ++ Θ).
Proof.
  intros * Hhd Hin Θ1 β b0 Θ2 Heq Hne.
  destruct Θ1 as [ | [c1 b1] Θ1' ]; simpl in Heq; inversion Heq; subst.
  - auto.
  - eapply Hin; eauto.
Qed.

(** Prepending a block of Δ-free entries preserves the invariant. *)
Lemma faf_app : forall Δ (E : aenv) Θ,
  Δ ∩ dom E [=] empty ->
  Δ ∩ dom Θ [=] empty ->
  flex_above_free Δ Θ ->
  flex_above_free Δ (E ++ Θ).
Proof.
  intros Δ E; induction E as [ | [c b] E' IH ]; intros Θ HE HΘ Hin;
    simpl in *; auto.
  apply faf_cons.
  - intros _. repeat rewrite dom_app in *. clear - HE HΘ. fsetdec.
  - apply IH; auto. clear - HE. fsetdec.
Qed.

(** Opening a fresh binder at the head extends both invariants. *)
Lemma faf_open_tvar : forall Δ α Θ,
  flex_above_free Δ Θ ->
  α `notin` dom Θ ->
  flex_above_free (add α Δ) ((α ~ abind_tvar) ++ Θ).
Proof.
  intros * Hin Hfr Θ1 β b Θ2 Heq Hne.
  destruct Θ1 as [ | [c1 b1] Θ1' ]; simpl in Heq; inversion Heq; subst.
  - congruence.
  - assert (Hβ : Δ ∩ (add β (dom Θ2)) [=] empty)
      by (eapply Hin; eauto).
    rewrite dom_app in Hfr. simpl in Hfr.
    clear - Hβ Hfr. fsetdec.
Qed.

(** Strip a shared rigid head from an identity information-increase.
    The target's shared [(α, tvar)] head forces the a_inc suffix to be
    empty (its entries are flexible, never rigid), so the increase holds
    at the tails. *)
Lemma a_isub_strip_tvar : forall α Θ0 Θ1,
  ((α ~ abind_tvar) ++ Θ0) ⊴ ((α ~ abind_tvar) ++ Θ1) ->
  Θ0 ⊴ Θ1.
Proof.
  intros α Θ0 Θ1 [[κ [Hid Hinc]] Hdef].
  split.
  - exists κ. split; [exact Hid |].
    eapply a_inc_tvar_head_inv; exact Hinc.
  - intros β τ Hb.
    assert (Hb1 : binds β (abind_flex_mono_def τ) ((α ~ abind_tvar) ++ Θ1))
      by (apply Hdef; unfold binds; right; exact Hb).
    destruct (binds_cons_1 _ _ _ _ _ _ Hb1) as [[? Heq] | Hb'];
      [discriminate | exact Hb'].
Qed.

(** Strip a shared rigid binder from the problem invariants. *)
Lemma no_flex_dep_strip : forall α Δ Θ,
  no_flex_dep (add α Δ) ((α ~ abind_tvar) ++ Θ) ->
  no_flex_dep Δ Θ.
Proof.
  intros α Δ Θ H β τ Hb.
  assert (Hb1 : binds β (abind_flex_mono_def τ) ((α ~ abind_tvar) ++ Θ))
    by (unfold binds; right; exact Hb).
  pose proof (H β τ Hb1) as Hh. clear - Hh. fsetdec.
Qed.

Lemma faf_strip : forall α Δ Θ,
  flex_above_free (add α Δ) ((α ~ abind_tvar) ++ Θ) ->
  flex_above_free Δ Θ.
Proof.
  intros α Δ Θ H Θ1 β b Θ2 Heq Hne.
  assert (Heq' : (α ~ abind_tvar) ++ Θ
               = ((α ~ abind_tvar) ++ Θ1) ++ (β, b) :: Θ2)
    by (subst; simpl; reflexivity).
  pose proof (H ((α ~ abind_tvar) ++ Θ1) β b Θ2 Heq' Hne) as Hh.
  clear - Hh. fsetdec.
Qed.

(** Definitions in a well-formed context are scoped by it. *)
Lemma a_wf_aenv_def_ftv_dom : forall Θ β τ,
  {{ ⊢ Θ }}a ->
  binds β (abind_flex_mono_def τ) Θ ->
  ftvar_in_ptyp τ [<=] dom Θ.
Proof.
  intros * Hwf Hb.
  eapply a_wf_ptyp_ftv_dom; eapply a_wf_aenv_binds_def_wf; eauto.
Qed.

Lemma no_flex_dep_open_tvar : forall Δ α Θ,
  {{ ⊢ Θ }}a ->
  no_flex_dep Δ Θ ->
  α `notin` dom Θ ->
  no_flex_dep (add α Δ) ((α ~ abind_tvar) ++ Θ).
Proof.
  intros * Hwf Hnd Hfr β τ Hb.
  destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
    [ discriminate | ].
  assert (Hd : Δ ∩ ftvar_in_ptyp τ [=] empty)
    by (eapply Hnd; eauto).
  assert (Hsc : ftvar_in_ptyp τ [<=] dom Θ)
    by (eapply a_wf_aenv_def_ftv_dom; eauto).
  clear - Hd Hsc Hfr. fsetdec.
Qed.

(** ⭐ The three Δ-invariants (every Δ-name a rigid of the context,
    [no_flex_dep], [flex_above_free]) EXTEND under a fresh rigid opener:
    what every ∀ row of the consistency / subtyping / splitting walks does
    to them before its IH.  The new Δ' is any subset of [add α Δ] — the
    rows put [α] in one or both halves. *)
Lemma delta_inv_open_tvar : forall Δ Δ' α Θ,
  {{ ⊢ Θ }}a ->
  α `notin` dom Θ ->
  Δ' [<=] add α Δ ->
  (forall β, β `in` Δ -> binds β abind_tvar Θ) ->
  no_flex_dep Δ Θ ->
  flex_above_free Δ Θ ->
  (forall β, β `in` Δ' -> binds β abind_tvar ((α ~ abind_tvar) ++ Θ)) /\
  no_flex_dep Δ' ((α ~ abind_tvar) ++ Θ) /\
  flex_above_free Δ' ((α ~ abind_tvar) ++ Θ).
Proof.
  intros Δ Δ' α Θ Hwf Hfr Hsub Hrig Hnd Hfaf. split; [ | split ].
  - intros β Hβ. destruct (β == α) as [ -> | Hne ];
      [ unfold binds; left; reflexivity
      | unfold binds; right; apply Hrig; clear - Hβ Hne Hsub; fsetdec ].
  - intros β τ Hb.
    assert (Hd : add α Δ ∩ ftvar_in_ptyp τ [=] empty)
      by (eapply (no_flex_dep_open_tvar Hwf Hnd Hfr); exact Hb).
    clear - Hd Hsub. fsetdec.
  - intros Θ1 β b Θ2 Heq Hne.
    assert (Hd : add α Δ ∩ add β (dom Θ2) [=] empty)
      by (eapply (faf_open_tvar Hfaf Hfr); eassumption).
    clear - Hd Hsub. fsetdec.
Qed.


Lemma a_decls_no_def : forall Ξ β τ,
  a_decls Ξ ->
  binds β (abind_flex_mono_def τ) Ξ ->
  False.
Proof.
  intros Ξ β τ H; induction H; intros Hb.
  - inversion Hb.
  - destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
    [ inversion H0; subst; discriminate Heq | auto ].
Qed.

(* ===================================================================== *)
(*  Helpers for the main induction                                        *)
(* ===================================================================== *)

(** Erasure commutes with closing a free variable. *)
Lemma bskl_to_pskl_close_rec : forall Q α k,
  bskl_to_pskl (close_bskl_wrt_bskl_rec k α Q)
  = close_pskl_wrt_pskl_rec k α (bskl_to_pskl Q).
Proof.
  induction Q; intros; simpl; f_equal; auto;
    repeat match goal with
    | |- context [ if ?t then _ else _ ] => destruct t
    | |- context [ lt_ge_dec ?a ?b ] => destruct (lt_ge_dec a b)
    end; reflexivity.
Qed.

Lemma bskl_to_pskl_close : forall Q α,
  bskl_to_pskl (close_bskl_wrt_bskl α Q)
  = close_pskl_wrt_pskl α (bskl_to_pskl Q).
Proof. intros; apply bskl_to_pskl_close_rec. Qed.

(* ===================================================================== *)
(*  ∀-wf at a CHOSEN opener                                               *)
(* ===================================================================== *)

(** [a_consis]'s ∀ rows are exists-fresh now, so they hand their consumers
    ONE opener — an atom the cofinite [a_wf_pskl__all] has no reason to have
    avoided.  [a_wf_pskl_all_inv_at] manufactures the wf instance at that
    opener; it and its two supports moved up from prop_completeness_consis.v (PART B),
    which is downstream and still sees them. *)

(** ⚙ Bounded by the CONTEXT alone — every free variable of a wf skeleton
    is a tvar of [Θ] ([a_wf_pskl_ftv_binds]).  The bound used to read
    [Δ ∪ dom Θ] (strengthened 2026-10-10). *)
Lemma a_wf_pskl_ftv_dom : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  ftvar_in_pskl P [<=] dom Θ.
Proof.
  intros * H γ Hγ. exact (a_binds_tvar_in_dom (a_wf_pskl_ftv_binds H Hγ)).
Qed.

(** Opening a ∀-body at a CHOSEN fresh opener [β]: the ∀ rule records its
    binder in BOTH the context and Δ. *)
Lemma a_wf_pskl_all_inv_at : forall Θ Δ P β,
  {{ Θ ⨟ Δ ⊢ₚₛ (pskl_all_syn P) }}a ->
  β `notin` ftvar_in_pskl P ->
  {{ ((β ~ abind_tvar) ++ Θ) ⨟ (add β Δ) ⊢ₚₛ
     (open_pskl_wrt_pskl P (pskl_var_f β)) }}a.
Proof.
  intros Θ Δ P β H HβP.
  inversion H as [ | | | L1 ? ? ? Hb | | ]; subst.
  pick fresh α for (L1 `union` dom Θ `union` ftvar_in_pskl P `union` Δ
                      `union` singleton β).
  assert (HαL : α `notin` L1) by (clear - Fr; fsetdec).
  pose proof (Hb α HαL) as Hα.
  assert (Hβo : β `notin` ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f α))).
  { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f α))
      as Hup. simpl in Hup. clear - Hup HβP Fr. fsetdec. }
  pose proof (@a_wf_pskl_rename_bound _ _ _ Hα ((β ~ abind_tvar) ++ Θ) α β)
    as Hr.
  rewrite <- (subst_pskl_in_pskl_intro α P (pskl_var_f β)) in Hr;
    [ | clear - Fr; solve_notin_auto ].
  eapply a_wf_pskl_delta_mono; [ apply Hr | ].
  - intros γ Hγ Hne. apply a_binds_tvar_cons_tvar.
    destruct (a_binds_tvar_cons_tvar_inv Hγ) as [-> | Hb']; [ congruence | auto ].
  - apply a_binds_tvar_cons_tvar. auto.
  - clear; fsetdec.
  - exact Hβo.
  - intros γ _ Hγ.
    assert (HαΔ : α `notin` Δ) by (clear - Fr; fsetdec).
    assert (Hαβ : α <> β) by (clear - Fr; fsetdec).
    clear - Hγ HαΔ Hαβ. fsetdec.
Qed.

(** Moving a variable from Δ into the context as a rigid. *)
Lemma a_wf_pskl_reassoc : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  forall α,
  {{ ((α ~ abind_tvar) ++ Θ) ⨟ (remove α Δ) ⊢ₚₛ P }}a.
Proof.
  intros Θ Δ P H α0.
  assert (H' : {{ Θ ⨟ (remove α0 Δ) ⊢ₚₛ P }}a).
  { eapply a_wf_pskl_delta_mono; [ exact H | ].
    intros γ _ Hγ. clear - Hγ. fsetdec. }
  eapply a_wf_pskl_tvar_mono; [ exact H' | ].
  intros γ Hγ. apply a_binds_tvar_cons_tvar. auto.
Qed.

(** Opening a ∀-body at a GIVEN sufficiently fresh rigid α, Δ unchanged
    (the exists-fresh form of the ∀-wf inversion: the cofinite rule
    delivers instances only off its own [L], which an exists-fresh
    consumer does not control).  [a_wf_pskl_all_inv_at], then forget [α]
    from Δ. *)
Lemma a_wf_pskl_all_syn_open_tvar : forall Θ Δ B α,
  {{ Θ ⨟ Δ ⊢ₚₛ (pskl_all_syn B) }}a ->
  α `notin` dom Θ `union` ftvar_in_pskl B `union` Δ ->
  {{ ((α ~ abind_tvar) ++ Θ) ⨟ Δ ⊢ₚₛ (open_pskl_wrt_pskl B (pskl_var_f α)) }}a.
Proof.
  intros Θ Δ B α Hwf Hα.
  eapply a_wf_pskl_delta_mono;
    [ apply a_wf_pskl_all_inv_at; [ exact Hwf | clear - Hα; fsetdec ] | ].
  intros γ _ Hγ. clear - Hγ. fsetdec.
Qed.

(** [a_wf_ptyp] transports along [⊴] (only positive tvar-ish lookups). *)
Lemma a_wf_ptyp_isub : forall Θ A,
  a_wf_ptyp Θ A ->
  forall Θ', Θ ⊴ Θ' ->
  a_wf_ptyp Θ' A.
Proof.
  intros Θ A H; induction H; intros Θ' Hle; eauto using a_wf_ptyp.
  - apply a_wf_ptyp__var. eapply a_isub_binds_tvarish; eauto.
  - apply a_wf_ptyp__all with (L := L `union` dom Θ'). intros α Hα.
    apply H0; auto. apply a_isub_cons_tvar; auto.
Qed.

(** Every binding produced by guess^TY is a plain flexible variable. *)
Lemma a_guess_mono_flex_binds : forall Θ P βs τ,
  a_guess_mono Θ P βs τ ->
  forall α1 b, binds α1 b βs -> b = abind_flex_mono.
Proof.
  intros * H; induction H; intros α1 b Hb; simpl in *;
    try solve [ inversion Hb ].
  - (* ghost *)
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ inversion Heq; auto | inversion Hb' ].
  - (* univ_ghost *)
    eauto.
  - (* arrow *)
    unfold binds in Hb. apply in_app_or in Hb.
    destruct Hb as [Hb | Hb];
      [ eapply IHa_guess_mono1 | eapply IHa_guess_mono2 ];
      unfold binds; eauto.
  - (* forall — exists-fresh: the single premise IS the instance *)
    eauto.
Qed.

(** Prepending a fresh, uniform flexible-variable block preserves
    context well-formedness. *)
Lemma a_wf_aenv_prepend_flex : forall E Θ,
  (forall α1 b, binds α1 b E -> b = abind_flex_mono) ->
  uniq E ->
  (forall α1, α1 `in` dom E -> α1 `notin` dom Θ) ->
  {{ ⊢ Θ }}a ->
  {{ ⊢ (E ++ Θ) }}a.
Proof.
  induction E as [ | [α1 b] E' IH ]; intros Θ Hall Huniq Hfresh Hwf; simpl.
  - exact Hwf.
  - assert (Hb : b = abind_flex_mono)
      by (apply (Hall α1); unfold binds; simpl; left; reflexivity).
    subst.
    assert (HuE : uniq E' /\ α1 `notin` dom E')
      by (inversion Huniq; subst; auto).
    destruct HuE as [HuE Hγ'].
    apply a_wf_aenv__flex.
    + rewrite dom_app.
      assert (Hγd : α1 `notin` dom Θ) by (apply Hfresh; simpl; fsetdec).
      clear - Hγ' Hγd. fsetdec.
    + apply IH; auto.
      * intros α1' b' Hb'. apply (Hall α1'); unfold binds; simpl; right; auto.
      * intros α1' Hγ'2. apply Hfresh. simpl. fsetdec.
Qed.

(** A visible monotype's skeleton is well-formed (no quantifiers, no
    ghosts — only the var leaves need discharging). *)
Lemma mono_ptyp_wf_pskl : forall Θ τ,
  mono_ptyp τ ->
  (forall α, α `in` ftvar_in_ptyp τ -> a_binds_tvar α Θ) ->
  {{ Θ ⨟ empty ⊢ₚₛ (ptyp_to_pskl τ) }}a.
Proof.
  intros Θ τ H; induction H; intros Hvis; simpl in *.
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var. apply Hvis. fsetdec.
  - apply a_wf_pskl__arrow;
      [ apply IHmono_ptyp1 | apply IHmono_ptyp2 ];
      intros α Hα; apply Hvis; fsetdec.
Qed.

(** Clean inversions of context well-formedness. *)
Lemma a_wf_aenv_flex_inv : forall α Θ,
  {{ ⊢ ((α ~ abind_flex_mono) ++ Θ) }}a ->
  α `notin` dom Θ /\ {{ ⊢ Θ }}a.
Proof. intros * H; inversion H; subst; auto. Qed.

Lemma a_wf_aenv_tvar_inv : forall α Θ,
  {{ ⊢ ((α ~ abind_tvar) ++ Θ) }}a ->
  α `notin` dom Θ /\ {{ ⊢ Θ }}a.
Proof. intros * H; inversion H; subst; auto. Qed.

Lemma a_wf_aenv_var_typ_inv : forall x A Θ,
  {{ ⊢ ((x ~ abind_var_typ A) ++ Θ) }}a ->
  x `notin` dom Θ /\ a_wf_ptyp Θ A /\ {{ ⊢ Θ }}a.
Proof. intros * H; inversion H; subst; auto. Qed.

(* ⭐ The middle conjunct is the DISCIPLINED [a_wf_pskl], not [a_scope_pskl]
   — that is what [a_wf_aenv__var] stores.  A caller that only wants scoping
   composes with [a_scope_pskl_of_wf] (or lets [eauto] do it — the conversion
   is an exported hint). *)
Lemma a_wf_aenv_var_skl_inv : forall x P Θ,
  {{ ⊢ ((x ~ abind_var_skl P) ++ Θ) }}a ->
  x `notin` dom Θ /\ {{ Θ ⨟ empty ⊢ₚₛ P }}a /\ {{ ⊢ Θ }}a.
Proof. intros * H; inversion H; subst; auto. Qed.

(** Monotype skeletons are locally closed and guarded. *)
Lemma mono_bskl_lc : forall Q,
  mono_bskl Q -> lc_bskl Q.
Proof. induction 1; auto using lc_bskl. Qed.

Lemma mono_bskl_guarded : forall Q,
  mono_bskl Q -> guarded_bskl Q.
Proof.
  destruct 1 as [ | α | Q1 Q2 ];
    [ apply guarded_bskl__unit | apply guarded_bskl__var
    | apply guarded_bskl__arrow; apply mono_bskl_lc; auto ].
Qed.

(** A non-rigid entry is not among the (rigid) Δ-variables. *)
Lemma faf_flex_notin : forall Δ Θ α b,
  flex_above_free Δ Θ ->
  binds α b Θ ->
  b <> abind_tvar ->
  α `notin` Δ.
Proof.
  intros Δ Θ α b Hfaf Hb Hne.
  apply binds_split in Hb. destruct Hb as [Θ1 [Θ2 Heq]].
  simpl in Heq.
  pose proof (Hfaf _ _ _ _ Heq Hne) as Hh. clear - Hh. fsetdec.
Qed.

(** A flexible variable is not among the (rigid) Δ-variables. *)
Lemma faf_flex_tvar_notin : forall Δ Θ α,
  flex_above_free Δ Θ ->
  a_flex_tvar Θ α ->
  α `notin` Δ.
Proof.
  intros Δ Θ α Hfaf [Hb | [τ Hb]]; eapply faf_flex_notin; eauto; discriminate.
Qed.

(** A flexible variable of the input stays bound in an increased context. *)
Lemma a_isub_flex_binds_tvar : forall Θ Θ' α,
  Θ ⊴ Θ' ->
  a_flex_tvar Θ α ->
  a_binds_tvar α Θ'.
Proof.
  intros Θ Θ' α Hle Hf. eapply a_isub_binds_tvarish; [ exact Hle | ].
  destruct Hf as [Hb | [τ Hb]]; [ right; left | right; right; exists τ ];
    exact Hb.
Qed.

(** The subjects of a variable unification are flexible. *)
Lemma a_unify_subjects_flex : forall Θ0 α β Θ1,
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a ->
  a_flex_tvar Θ0 α /\ a_flex_tvar Θ0 β.
Proof.
  intros * _ Hu; induction Hu;
    intuition eauto using a_flex_tvar_weaken_app;
    left; unfold binds; simpl; auto.
Qed.

(** The subject of an assignment is flexible in the input context.

    Still a STANDALONE induction after the mutual refactor: no case needs an
    [a_consis] IH.  Assign-Assign reads its conclusion straight off the HATTED
    SUBJECT premise (which is exactly why that premise exists — with an opaque
    consistency premise the old "derive it from the [a_assign] IH" argument
    dies, and [a_consis__rigid] would otherwise admit a RIGID subject).  And
    Assign-Depend gets SIMPLER: the suffix now grows at the tail, so the
    context is already associated the right way and [a_flex_tvar_permute_mid]
    is no longer needed — plain [app_assoc] does it. *)
Lemma a_assign_subject_flex : forall Θ0 Ξ α P Θ1,
  {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
  a_flex_tvar (Ξ ++ Θ0) α.
Proof.
  intros * H; induction H; simpl_env in *;
    eauto using a_flex_tvar_weaken_app, a_flex_tvar_weaken_mid.
  - left; unfold binds; simpl; auto.
  - left; unfold binds; apply in_or_app; right; left; reflexivity.
Qed.

(** Rigid bindings are preserved exactly along [⊴]. *)
Lemma a_isub_binds_tvar : forall Θ Θ' α,
  Θ ⊴ Θ' -> binds α abind_tvar Θ -> binds α abind_tvar Θ'.
Proof.
  intros Θ Θ' α [[κ [Hid Hinc]] _] Hb.
  eapply a_inc_binds_tvar; eauto.
Qed.

(** Local closure reflects through the erasure (the converse of
    [lc_bskl_to_pskl]), via degrees. *)
Lemma degree_bskl_of_bskl_to_pskl : forall Q k,
  degree_pskl_wrt_pskl k (bskl_to_pskl Q) -> degree_bskl_wrt_bskl k Q.
Proof.
  induction Q; intros k H; simpl in H; inversion H; subst; constructor; auto.
Qed.

Lemma lc_bskl_of_bskl_to_pskl : forall Q,
  lc_pskl (bskl_to_pskl Q) -> lc_bskl Q.
Proof.
  intros Q H. apply lc_bskl_of_degree, degree_bskl_of_bskl_to_pskl.
  apply degree_pskl_wrt_pskl_of_lc_pskl. exact H.
Qed.

(** Refinement with a guarded left side yields a guarded right side,
    PROVIDED the right side is locally closed (the arrow rule's
    components are otherwise unconstrained: a ghost fill below an arrow
    need not be locally closed any more). *)
Lemma ad_refine_syn_guarded_r : forall Θ Δ Q Q',
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad ->
  guarded_bskl Q ->
  lc_bskl Q' ->
  guarded_bskl Q'.
Proof.
  intros Θ Δ Q Q' Hwf H; induction H; intros Hg Hlc;
    try solve [ inversion Hg ].
  - auto with fresco.
  - auto with fresco.
  - inversion Hlc; subst. apply guarded_bskl__arrow; auto.
  - assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    apply IHad_refine_syn; auto.
    apply mono_bskl_guarded, mono_ptyp_to_bskl_syn; auto.
  - auto with fresco.
Qed.

(** The shape fact the guardedness lemmas are mostly used for, with NO
    side condition: a left side that is neither a ghost nor a ∀◇ never
    refines to a ∀◇. *)
Lemma ad_refine_pskl_not_univ_ghost_r : forall Θ Δ P P',
  {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ P' }}ad ->
  P <> pskl_ghost ->
  (forall P0, P <> pskl_univ_ghost P0) ->
  forall P0', P' <> pskl_univ_ghost P0'.
Proof.
  intros * H; induction H; intros Hnh Hnt P0' Heq; try discriminate;
    try solve [ exact (Hnh eq_refl) | exact (Hnt _ eq_refl) ].
  (* flex_l: a painted type is never a ghost nor a ∀◇ *)
  eapply IHad_refine_pskl; [ | | exact Heq ];
    [ intro Hc | intros P1 Hc ]; destruct τ; simpl in Hc; discriminate.
Qed.

Lemma ad_refine_syn_not_univ_ghost_r : forall Θ Δ Q Q',
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad ->
  Q <> bskl_ghost ->
  (forall Q0, Q <> bskl_univ_ghost Q0) ->
  forall Q0', Q' <> bskl_univ_ghost Q0'.
Proof.
  intros * H; induction H; intros Hnh Hnt Q0' Heq; try discriminate;
    try solve [ exact (Hnh eq_refl) | exact (Hnt _ eq_refl) ].
  (* flex_l: a painted type is never a ghost nor a ∀◇ *)
  eapply IHad_refine_syn; [ | | exact Heq ];
    [ intro Hc | intros P1 Hc ]; unfold ptyp_to_bskl_syn in Hc;
    destruct τ; simpl in Hc; discriminate.
Qed.

(* ===================================================================== *)
(*  The two SUBSIDIARY INDUCTIONS that Assign-Assign's soundness needs     *)
(*  (consistency-proofs.tex:1742-1753).  Assign-Assign's premise is a      *)
(*  CONSISTENCY derivation, so the [a_assign] IH hands back a JOIN [Q]     *)
(*  rather than the variable [α̂] the conclusion asks for.  The paper       *)
(*  eliminates [Q] in two steps:                                           *)
(*                                                                         *)
(*    (h)  from  inh(P[τ/β̂]) ⊳ˢʸⁿ Q  and  α̂[τ/β̂] ∼ Q                       *)
(*         conclude  P[τ/β̂] ∼ α̂[τ/β̂]                                       *)
(*    (i)  fold the definition β̂ ≔ τ back in, on BOTH sides.               *)
(*                                                                         *)
(*  Step (h) splits into [refine_inh_mono_consis] (the refinement side —   *)
(*  the join is a MONOTYPE painting, because the subject [α̂[τ/β̂]] is one,  *)
(*  which kills every quantifier/univ_ghost refinement rule) and the Q-SIDE   *)
(*  transport of consistency along [≡ᵗ] (the mirror of                     *)
(*  [tyequiv_mono_consis_transport], prop_consis_monotype_equiv.v — the subject-side *)
(*  one — which the [Flex-Flex-Assign] case uses).  Step (i) is            *)
(*  [ad_pat_consis_fold_def] (left) + [ad_pat_consis_fold_def_q_mono]      *)
(*  (right); both already exist.                                           *)
(* ===================================================================== *)

(** A monotype PAINTING is colour-blind: syn = inh (colours differ only at
    quantifiers, and a monotype has none).  Companion of [mono_bskl_inh_syn]. *)
Lemma mono_bskl_syn_inh : forall P,
  mono_bskl (pskl_to_bskl_syn P) ->
  pskl_to_bskl_syn P = pskl_to_bskl_inh P.
Proof.
  induction P; intros Hm; simpl in *; try reflexivity;
    inversion Hm; subst; f_equal; auto.
Qed.

(** Substituting a monotype for a variable commutes with the skeleton
    embedding, on a variable.  (The [α̂ = β̂] branch is REACHABLE — there the
    subject of Assign-Assign is the monotype [τ], not a variable.) *)
Lemma subst_pskl_var_ptyp : forall τ β α,
  subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)
  = ptyp_to_pskl (subst_ptyp_in_ptyp τ β (ptyp_var_f α)).
Proof.
  intros. simpl. destruct (eq_var α β); simpl; reflexivity.
Qed.

(* ===================================================================== *)
(*  The TARGET of a consistency derivation is scoped — when the subject    *)
(*  has no plain [◇].                                                      *)
(*                                                                        *)
(*  The paper's [Ghost] rule (and [ad_pat_consis__ghost], since            *)
(*  2026-10-10) fills a plain-ghost subject with an ARBITRARY counterpart:  *)
(*  its well-formedness is the judgement's presupposition (wf of the        *)
(*  counterpart, declarative.tex:2074), not a consequence of the rules.     *)
(*  So the target is scoped by the derivation alone exactly when that rule  *)
(*  cannot fire — [uskl_no_ghost] (def_shapes.v), which holds of every      *)
(*  type painting and of every decorated skeleton.  Everywhere else the     *)
(*  statements CARRY the counterpart's well-formedness                     *)
(*  (docs/WF-SIDE-CONDITIONS.md §2a).                                      *)
(* ===================================================================== *)

Lemma uskl_no_ghost_open_rec : forall R R' k,
  uskl_no_ghost R -> uskl_no_ghost R' ->
  uskl_no_ghost (open_uskl_wrt_uskl_rec k R' R).
Proof.
  induction R; intros R' k HR HR'; simpl in *; auto.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; auto.
  - destruct HR; split; auto.
Qed.

Lemma uskl_no_ghost_open : forall R R',
  uskl_no_ghost R -> uskl_no_ghost R' ->
  uskl_no_ghost (open_uskl_wrt_uskl R R').
Proof. intros; apply uskl_no_ghost_open_rec; assumption. Qed.

Lemma uskl_no_ghost_ptyp : forall A, uskl_no_ghost (ptyp_to_uskl_syn A).
Proof.
  unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn.
  induction A; simpl; auto.
Qed.

Lemma uskl_no_ghost_of_dskl : forall R, is_dskl R -> uskl_no_ghost R.
Proof.
  intros R H; induction H; simpl; auto.
  destruct (atom_fresh L) as [α Hα].
  specialize (H0 α Hα). unfold open_uskl_wrt_uskl in H0.
  revert H0. generalize 0. clear. induction R; intros k Hk; simpl in *; eauto.
  - destruct Hk; split; eauto.
Qed.

Lemma uskl_no_ghost_of_ghost_free : forall R, uskl_ghost_free R -> uskl_no_ghost R.
Proof.
  intros R H; induction H; simpl; auto;
  destruct (atom_fresh L) as [α Hα];
  specialize (H0 α Hα); unfold open_uskl_wrt_uskl in H0;
  revert H0; generalize 0; clear; induction R; intros k Hk; simpl in *; eauto;
  destruct Hk; split; eauto.
Qed.

Lemma ad_pat_consis_target_scope : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  uskl_no_ghost R ->
  a_scope_pskl Θ (bskl_to_pskl Q).
Proof.
  intros Ψ Θ R Q H; induction H; intros Hng; simpl in *.
  (* the four ∀ rows and [univ_ghost_inh]: the target opens at a context
     binder; the subject's no-ghost survives opening with a variable *)
  all: try solve
    [ apply a_scope_pskl_all_of_open with (L := L); intros α Hα;
      rewrite <- bskl_to_pskl_open; apply H0; [ exact Hα | ];
      first [ exact Hng
            | apply uskl_no_ghost_open; [ exact Hng | simpl; exact I ] ] ].
  - split; [ constructor | intros γ Hγ; exfalso; clear - Hγ; fsetdec ].
  - apply a_scope_pskl_var; assumption.
  - destruct Hng as [Hng1 Hng2].
    destruct (IHad_pat_consis1 Hng1) as [Hl1 Hb1].
    destruct (IHad_pat_consis2 Hng2) as [Hl2 Hb2].
    split; [ constructor; assumption | ].
    intros γ Hγ. apply union_1 in Hγ as [Hγ | Hγ]; auto.
  - split; [ constructor | intros γ Hγ; exfalso; clear - Hγ; fsetdec ].
  - destruct (IHad_pat_consis Hng) as [Hl Hb].
    split; [ constructor; assumption | exact Hb ].
  - (* ghost : a plain-ghost subject is excluded *) contradiction.
  - destruct (IHad_pat_consis Hng) as [Hl Hb].
    split; [ constructor; assumption | exact Hb ].
  - (* univ_ghost_drop *) apply IHad_pat_consis; exact Hng.
  - (* flex_l : the subject unfolds to a type painting *)
    apply IHad_pat_consis. apply uskl_no_ghost_ptyp.
  - (* flex_r : the target IS a defined flexible *)
    apply a_scope_pskl_var. right; right; eauto.
Qed.

(** …and when the subject is a TYPE painting outright (no ghost of any
    kind), the target is a well-formed painting of a type — at ANY [Δ],
    since [Δ] is read only under a [∀◇].  This is the disciplined form the
    completeness statements' counterpart-wf premise asks for, at every call
    site whose join starts from an annotation or a variable's type. *)
Lemma msubst_pskl_ghost_free : forall κ P,
  pskl_ghost_free P -> pskl_ghost_free (msubst_pskl κ P).
Proof.
  induction P; cbn; intros Hg; auto.
  - apply ptyp_to_pskl_ghost_free.
  - destruct Hg; split; auto.
Qed.

Lemma ad_pat_consis_target_wf_ghost_free : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  pskl_ghost_free ⌊ R ⌋ˢ ->
  forall Δ, {{ Θ ⨟ Δ ⊢ₚₛ (bskl_to_pskl Q) }}a.
Proof.
  intros Ψ Θ R Q H; induction H; intros Hgf Δ; simpl in *;
    try contradiction.
  (* the four ∀ rows: the body at the opened context, Δ grown *)
  all: try solve
    [ apply a_wf_pskl__all with (L := L); intros α Hα;
      rewrite <- bskl_to_pskl_open; apply H0; [ exact Hα | ];
      rewrite uskl_to_pskl_open; apply pskl_ghost_free_open; exact Hgf ].
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var; assumption.
  - destruct Hgf. apply a_wf_pskl__arrow; auto.
  - (* flex_l : the subject unfolds to a type painting *)
    apply IHad_pat_consis. rewrite uskl_to_pskl_ptyp.
    apply ptyp_to_pskl_ghost_free.
  - (* flex_r *) apply a_wf_pskl__var. right; right; eauto.
Qed.

(** The shape every completeness call site has: the subject is a
    metasubstitution image of a ghost-free (type) skeleton. *)
Corollary ad_pat_consis_msubst_target_wf : forall Ψ Θ κ P Q,
  {{ Ψ ⨟ Θ ⊢ˢ (pskl_to_uskl (msubst_pskl κ P)) ∼ Q }}ad ->
  pskl_ghost_free P ->
  forall Δ, {{ Θ ⨟ Δ ⊢ₚₛ (bskl_to_pskl Q) }}a.
Proof.
  intros Ψ Θ κ P Q H Hgf Δ.
  eapply ad_pat_consis_target_wf_ghost_free; [ exact H | ].
  rewrite uskl_to_pskl_pskl_to_uskl. apply msubst_pskl_ghost_free; exact Hgf.
Qed.

(** The two projections, in the [bskl] form most consumers want. *)
Lemma ad_pat_consis_target_binds : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  uskl_no_ghost R ->
  forall γ, γ `in` ftvar_in_bskl Q -> a_binds_tvar γ Θ.
Proof.
  intros Ψ Θ R Q H Hng γ Hγ.
  apply (a_scope_pskl_ftv_binds (ad_pat_consis_target_scope H Hng)).
  rewrite ftvar_bskl_to_pskl. exact Hγ.
Qed.

Lemma ad_pat_consis_target_lc : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  uskl_no_ghost R ->
  lc_bskl Q.
Proof.
  intros Ψ Θ R Q H Hng.
  apply lc_bskl_of_bskl_to_pskl.
  exact (a_scope_pskl_lc (ad_pat_consis_target_scope H Hng)).
Qed.

(** SUBSIDIARY INDUCTION #1 (the refinement half of the paper's step (h)):
    if the inherited painting of [P0] refines to a join that is a MONOTYPE
    painting, then [⌊P0⌋] is CONSISTENT with that join.  The monotype
    hypothesis is what makes this true: it rules out ForallInh /
    TopholeFill / TopholeKeep (whose outputs are quantifiers or univ_ghosts),
    and it forces the ghost-ghost fill [pskl_to_bskl_syn P] to be
    colour-blind, so consistency's [ghost] rule — which produces the
    INHERITED painting — matches it. *)
Lemma refine_inh_mono_consis : forall Θ Δ Qb Qt,
  {{ Θ ⨟ Δ ⊢ᵣ Qb ⊳ Qt }}ad ->
  {{ ⊢ Θ }}a ->
  mono_bskl Qt ->
  forall P0, Qb = pskl_to_bskl_inh P0 ->
  (forall α, α `in` ftvar_in_bskl Qt -> a_binds_tvar α Θ) ->
  {{ empty ⨟ Θ ⊢ˢ (pskl_to_uskl P0) ∼ Qt }}ad.
Proof.
  intros Θ Δ Qb Qt Hr Hwf; induction Hr; intros Hm P0 Heq Hvis.
  - (* unit *)
    destruct P0; simpl in Heq; try discriminate.
    simpl. apply ad_pat_consis__unit. fsetdec.
  - (* var *)
    destruct P0; simpl in Heq; try discriminate.
    inversion Heq; subst.
    simpl. apply ad_pat_consis__var; [ fsetdec | ].
    apply Hvis. simpl. clear; fsetdec.
  - (* arrow *)
    destruct P0; simpl in Heq; try discriminate.
    inversion Heq; subst. inversion Hm; subst.
    simpl in Hvis.
    simpl. apply ad_pat_consis__arrow with (Ψ1 := empty) (Ψ2 := empty);
      [ apply IHHr1 | apply IHHr2 | fsetdec ]; auto;
      intros α0 Hα0; apply Hvis; clear - Hα0; fsetdec.
  - (* all : the join would be a quantifier, never a monotype *)
    inversion Hm.
  - (* ghost : the ghost fill is colour-blind here *)
    destruct P0; simpl in Heq; try discriminate.
    simpl. rewrite (mono_bskl_syn_inh _ Hm).
    apply ad_pat_consis__ghost; fsetdec.
  - (* univ_ghost_remove *)
    destruct P0; simpl in Heq; try discriminate.
    inversion Heq; subst.
    simpl. apply ad_pat_consis__univ_ghost_drop. apply IHHr; auto.
  - (* univ_ghost_fill : the join would be a quantifier *)
    inversion Hm.
  - (* univ_ghost_keep : the join would be a univ_ghost *)
    inversion Hm.
  - (* flex_l : the input is a DEFINED flexible variable *)
    destruct P0; simpl in Heq; try discriminate.
    inversion Heq; subst.
    assert (Hmt : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    simpl. eapply ad_pat_consis__flex_l; [ exact H | ].
    rewrite <- pskl_to_uskl_ptyp.
    apply IHHr; auto.
    unfold ptyp_to_bskl_syn. rewrite ptyp_to_bskl_inh_syn_eq; auto.
  - (* flex_r : the join is a DEFINED flexible variable *)
    assert (Hmt : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    eapply ad_pat_consis__flex_r; [ exact H | ].
    apply IHHr; auto.
    + apply mono_ptyp_to_bskl_syn; auto.
    + intros α0 Hα0. rewrite ftvar_ptyp_to_bskl_syn in Hα0.
      eapply a_wf_ptyp_ftv_tvarish; [ | exact Hα0 ].
      eapply a_wf_aenv_binds_def_wf; eauto.
Qed.

(** Unfold a DEFINED variable sitting in the JOIN position.  The mirror of
    [consis_unfold_def_subject] (prop_consis_monotype_equiv.v): only [var] / [ghost] /
    [univ_ghost_drop] / [flex_l] / [flex_r] can have join [α1̂]. *)
Lemma consis_unfold_def_join : forall Ψ Θ R Qt,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Qt }}ad ->
  {{ ⊢ Θ }}a ->
  forall α1 τ, Qt = bskl_var_f α1 ->
  binds α1 (abind_flex_mono_def τ) Θ ->
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ (ptyp_to_bskl_syn τ) }}ad.
Proof.
  intros * Hc Hwf; induction Hc; intros α10 τ0 HeqQ Hb;
    try discriminate HeqQ.
  - (* var : the subject is the same variable; unfold it with [flex_l] *)
    inversion HeqQ; subst.
    assert (Hmτ : mono_ptyp τ0) by (eapply a_wf_aenv_binds_def_mono; eauto).
    eapply ad_pat_consis__flex_l; [ exact Hb | ].
    eapply ad_pat_consis_psi_cong;
      [ apply consis_mono_refl | clear - H; fsetdec ]; auto.
    intros α Hα. eapply a_wf_ptyp_ftv_tvarish;
      [ eapply a_wf_aenv_binds_def_wf; eauto | exact Hα ].
  - (* ghost : the ghost fill IS the variable *)
    destruct P; simpl in HeqQ; try discriminate.
    inversion HeqQ; subst.
    assert (Hmτ : mono_ptyp τ0) by (eapply a_wf_aenv_binds_def_mono; eauto).
    rewrite <- (ptyp_to_bskl_inh_syn_eq Hmτ).
    apply ad_pat_consis__ghost; exact H.
  - (* univ_ghost_drop *)
    apply ad_pat_consis__univ_ghost_drop. eapply IHHc; eauto.
  - (* flex_l *)
    eapply ad_pat_consis__flex_l; [ eassumption | ]. eapply IHHc; eauto.
  - (* flex_r : the join's own definition is the one we are unfolding *)
    inversion HeqQ; subst.
    assert (Heqτ : τ = τ0)
      by (assert (Hu : uniq Θ) by (apply a_wf_aenv_uniq; auto);
          pose proof (binds_unique _ _ _ _ _ H Hb Hu) as He;
          inversion He; reflexivity).
    subst. exact Hc.
Qed.

(** Congruence of the JOIN at an arrow.  Mirror of
    [consis_arrow_subject_transport]; the [ghost] case is why the components
    must be given as concrete MONOTYPES rather than opaque transports (the
    rebuilt ghost fill has to be a well-formed skeleton). *)
Lemma consis_arrow_join_transport : forall Ψ Θ R Qt,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Qt }}ad ->
  {{ ⊢ Θ }}a ->
  forall A1' A2' A1 A2,
  Qt = ptyp_to_bskl_syn (ptyp_arrow A1' A2') ->
  mono_ptyp A1 -> mono_ptyp A2 ->
  (forall α, α `in` ftvar_in_ptyp (ptyp_arrow A1 A2) -> a_binds_tvar α Θ) ->
  (forall Ψ' R', {{ Ψ' ⨟ Θ ⊢ˢ R' ∼ (ptyp_to_bskl_syn A1') }}ad ->
                 {{ Ψ' ⨟ Θ ⊢ˢ R' ∼ (ptyp_to_bskl_syn A1) }}ad) ->
  (forall Ψ' R', {{ Ψ' ⨟ Θ ⊢ˢ R' ∼ (ptyp_to_bskl_syn A2') }}ad ->
                 {{ Ψ' ⨟ Θ ⊢ˢ R' ∼ (ptyp_to_bskl_syn A2) }}ad) ->
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ (ptyp_to_bskl_syn (ptyp_arrow A1 A2)) }}ad.
Proof.
  intros Ψ Θ R Qt Hc Hwf; induction Hc;
    intros A1' A2' A1 A2 HeqQ HmA1 HmA2 Hvis Ht1 Ht2;
    unfold ptyp_to_bskl_syn in HeqQ; simpl in HeqQ; try discriminate HeqQ.
  - (* arrow *)
    inversion HeqQ; subst.
    unfold ptyp_to_bskl_syn; simpl.
    apply ad_pat_consis__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2).
    { apply Ht1; unfold ptyp_to_bskl_syn; assumption. }
    { apply Ht2; unfold ptyp_to_bskl_syn; assumption. }
    { assumption. }
  - (* ghost : rebuild the fill at the transported monotype *)
    assert (Hma : mono_ptyp (ptyp_arrow A1 A2))
      by (apply mono_ptyp__arrow; auto).
    rewrite <- (ptyp_to_bskl_inh_syn_eq Hma).
    apply ad_pat_consis__ghost; exact H.
  - (* univ_ghost_drop *)
    apply ad_pat_consis__univ_ghost_drop.
    apply (IHHc Hwf A1' A2' A1 A2 HeqQ HmA1 HmA2 Hvis Ht1 Ht2).
  - (* flex_l *)
    eapply ad_pat_consis__flex_l; [ eassumption | ].
    apply (IHHc Hwf A1' A2' A1 A2 HeqQ HmA1 HmA2 Hvis Ht1 Ht2).
Qed.

(** SUBSIDIARY INDUCTION #2 (the JOIN-side transport): for [A ≡ᵗ B] on
    monotypes, a consistency derivation whose JOIN is [syn{B}] can be
    re-joined at [syn{A}], and vice versa.  Both directions at once, so
    [sym] swaps and [trans] composes.  The exact mirror of
    [tyequiv_mono_consis_transport] (which transports the SUBJECT). *)
Lemma tyequiv_mono_consis_transport_q : forall Θ A A',
  {{ Θ ⊢ A ≡ᵗ A' }}a ->
  {{ ⊢ Θ }}a ->
  mono_ptyp A ->
  (forall α, α `in` ftvar_in_ptyp A -> a_binds_tvar α Θ) ->
  (forall Ψ R, {{ Ψ ⨟ Θ ⊢ˢ R ∼ (ptyp_to_bskl_syn A') }}ad ->
               {{ Ψ ⨟ Θ ⊢ˢ R ∼ (ptyp_to_bskl_syn A) }}ad) /\
  (forall Ψ R, {{ Ψ ⨟ Θ ⊢ˢ R ∼ (ptyp_to_bskl_syn A) }}ad ->
               {{ Ψ ⨟ Θ ⊢ˢ R ∼ (ptyp_to_bskl_syn A') }}ad).
Proof.
  intros Θ A A' Heq Hwf; induction Heq; intros Hm Hv.
  - (* refl *)
    split; intros Ψ R Hc; exact Hc.
  - (* sym : swap the IH's directions *)
    destruct (a_tyequiv_mono_vis Heq Hwf) as [_ Hback].
    destruct (Hback (conj Hm Hv)) as [HmA HvA].
    destruct (IHHeq Hwf HmA HvA) as [Hd1 Hd2].
    split; [ exact Hd2 | exact Hd1 ].
  - (* trans : compose *)
    destruct (a_tyequiv_mono_vis Heq1 Hwf) as [Hfwd _].
    destruct (Hfwd (conj Hm Hv)) as [HmB HvB].
    destruct (IHHeq1 Hwf Hm Hv) as [H1l H1r].
    destruct (IHHeq2 Hwf HmB HvB) as [H2l H2r].
    split; intros Ψ R Hc; [ apply H1l, H2l, Hc | apply H2r, H1r, Hc ].
  - (* flex_def : α̂ ≡ τ with α̂ ≔ τ *)
    split; intros Ψ R Hc.
    + (* fold the join back to the variable : one lookup rule *)
      unfold ptyp_to_bskl_syn; simpl.
      eapply ad_pat_consis__flex_r; [ eassumption | exact Hc ].
    + (* unfold the join's definition *)
      eapply consis_unfold_def_join;
        [ exact Hc | exact Hwf | | eassumption ].
      unfold ptyp_to_bskl_syn; simpl; reflexivity.
  - (* arrow : componentwise *)
    inversion Hm as [ | | ? ? Hm1 Hm2 ]; subst; simpl in Hv.
    assert (Hv1 : forall α, α `in` ftvar_in_ptyp A1 -> a_binds_tvar α Θ)
      by (intros α Hα; apply Hv; fsetdec).
    assert (Hv2 : forall α, α `in` ftvar_in_ptyp A2 -> a_binds_tvar α Θ)
      by (intros α Hα; apply Hv; fsetdec).
    destruct (a_tyequiv_mono_vis Heq1 Hwf) as [Hf1 _].
    destruct (Hf1 (conj Hm1 Hv1)) as [HmB1 HvB1].
    destruct (a_tyequiv_mono_vis Heq2 Hwf) as [Hf2 _].
    destruct (Hf2 (conj Hm2 Hv2)) as [HmB2 HvB2].
    destruct (IHHeq1 Hwf Hm1 Hv1) as [H1l H1r].
    destruct (IHHeq2 Hwf Hm2 Hv2) as [H2l H2r].
    split; intros Ψ R Hc.
    + eapply consis_arrow_join_transport with (A1' := B1) (A2' := B2);
        [ exact Hc | exact Hwf | reflexivity | exact Hm1 | exact Hm2
        | | exact H1l | exact H2l ].
      intros α Hα; simpl in Hα.
      destruct (union_1 Hα); [ apply Hv1 | apply Hv2 ]; auto.
    + eapply consis_arrow_join_transport with (A1' := A1) (A2' := A2);
        [ exact Hc | exact Hwf | reflexivity | exact HmB1 | exact HmB2
        | | exact H1r | exact H2r ].
      intros α Hα; simpl in Hα.
      destruct (union_1 Hα); [ apply HvB1 | apply HvB2 ]; auto.
  - (* all : a monotype is never a ∀ *)
    inversion Hm.
Qed.

(* ===================================================================== *)
(*  THE MUTUAL SOUNDNESS BUNDLE (thm:sound-consistency parts 1+2)          *)
(*                                                                          *)
(*  [a_unify] and [a_consis] are mutually inductive (the corrected          *)
(*  [Flex-Flex-Assign] recurses into consistency), so — exactly as the      *)
(*  paper organises its own proof (consistency-proofs.tex:1562) — their     *)
(*  soundness is ONE mutual induction.  [a_assign] stays BELOW the cycle    *)
(*  (the mech reads Assign-Assign as continuing the assignment, see the     *)
(*  note in algo/def_rules.v), so its lemmas enter as black boxes.          *)
(*                                                                          *)
(*  Conjuncts, per judgment  Θ0 → Θ1:                                       *)
(*   1. Θ0 ⊴ Θ1                    (information increase)                   *)
(*   2. {{ ⊢ Θ1 }}a               (wf preservation)                        *)
(*   3. dom Θ0 ⊆ dom Θ1            (no entry is dropped)                    *)
(*   4. ∀Δ-invariant preservation  (no-flex-dep + flex-above-free +         *)
(*      domain bookkeeping, GENERALIZED over Δ: the consistency premise     *)
(*      of Flex-Flex-Assign runs at Δ1 = Δ2 = ∅, so the fixed-Δ variant     *)
(*      would be useless there.  Its COVERAGE hypothesis is                 *)
(*      OUTPUT-relative, [Δ ∩ dom Θ1 ⊆ dom Θ0], mirroring the walk's own    *)
(*      Barendregt output premises — DESIGN.md §4.3)                        *)
(*   5. the augmented solution     (consistency: join + both refinements;   *)
(*      unification: the type EQUIVALENCE Θ1 ⊢ α ≡ᵗ β)                      *)
(*                                                                          *)
(*  The used-name index [F] and its "new names avoid F" conjunct are GONE   *)
(*  (2026-08-03): the walk's re-attaching rules state the obligation        *)
(*  directly, and completeness carries the matching avoid set on its own    *)
(*  motive (prop_completeness_consis.v (PART B) §2).                                     *)
(* ===================================================================== *)

(** Conclusions of the two motives (hypotheses live in [*_concl] below). *)
(** Each invariant's final domain implication is already supplied by its
    coverage premise. Reuse that premise when rebuilding a context. *)
Definition unify_sound_post (Θ0 : aenv) (α β : atom)
    (Θ1 : aenv) : Prop :=
  Θ0 ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\ dom Θ0 [<=] dom Θ1 /\
  (forall Δ,
     no_flex_dep Δ Θ0 -> flex_above_free Δ Θ0 ->
     Δ ∩ dom Θ1 [<=] dom Θ0 ->
     no_flex_dep Δ Θ1 /\ flex_above_free Δ Θ1 /\
     (forall α, α `in` Δ -> α `in` dom Θ1 -> α `in` dom Θ0)) /\
  ({{ Θ1 ⊢ (ptyp_var_f α) ≡ᵗ (ptyp_var_f β) }}a).

Definition consis_sound_post (Δ1 Δ2 : atoms) (Θ0 : aenv)
    (P0 P Q : pskl) (Θ1 : aenv) : Prop :=
  Θ0 ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\ dom Θ0 [<=] dom Θ1 /\
  (forall Δ,
     no_flex_dep Δ Θ0 -> flex_above_free Δ Θ0 ->
     Δ ∩ dom Θ1 [<=] dom Θ0 ->
     (forall α, α `in` Δ -> α `notin` dom Θ0 ->
        α `notin` (ftvar_in_pskl P0 `union` ftvar_in_pskl P)) ->
     no_flex_dep Δ Θ1 /\ flex_above_free Δ Θ1 /\
     (forall α, α `in` Δ -> α `in` dom Θ1 -> α `in` dom Θ0)) /\
  (exists Qt, bskl_to_pskl Qt = Q /\
     ad_pat_consis empty Θ1 (pskl_to_uskl P) Qt /\
     {{ Θ1 ⨟ Δ1 ⊢ᵣ (pskl_to_bskl_inh P0) ⊳ Qt }}ad) /\
  {{ Θ1 ⨟ Δ2 ⊢ᵣₚ P ⊳ Q }}ad.

Definition unify_sound_concl (Θ0 : aenv) (α β : atom)
    (Θ1 : aenv) : Prop :=
  {{ ⊢ Θ0 }}a -> unify_sound_post Θ0 α β Θ1.

Definition consis_sound_concl (Δ1 Δ2 : atoms) (Θ0 : aenv)
    (P0 P Q : pskl) (Θ1 : aenv) : Prop :=
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
  (forall α, α `in` (Δ1 `union` Δ2) -> binds α abind_tvar Θ0) ->
  no_flex_dep (Δ1 `union` Δ2) Θ0 ->
  flex_above_free (Δ1 `union` Δ2) Θ0 ->
  consis_sound_post Δ1 Δ2 Θ0 P0 P Q Θ1.

(** The ASSIGN motive.  [Ξ] is the pending suffix, so every context slot is
    the MERGED [Ξ ++ Θ0] (which is exactly the context of Assign-Assign's
    consistency premise).  Conjuncts 1-5 mirror the other two motives;
    conjunct 6 is the paper's part-3 solution: the assigned skeleton is
    declaratively consistent with the subject VARIABLE in the output.

    The wf hypothesis is the FULL [{{ _ ⨟ ∅ ⊢ₚₛ P }}a], not the old "every free
    variable is tvar-ish": the consistency IH of Assign-Assign needs
    [{{ _ ⨟ ∅ ⊢ₚₛ _ }}a] on BOTH slots, and [a_wf_pskl__univ_ghost] demands
    [guarded_pskl] — strictly stronger than visibility.  Every [a_assign]
    call site (consistency's FlexL/FlexR and their decorated twins) has it. *)
Definition assign_sound_post (Θ0 Ξ : aenv) (α : atom)
    (P : pskl) (Θ1 : aenv) : Prop :=
  (Ξ ++ Θ0) ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\ dom (Ξ ++ Θ0) [<=] dom Θ1 /\
  (forall Δ,
     no_flex_dep Δ (Ξ ++ Θ0) -> flex_above_free Δ Θ0 ->
     Δ ∩ dom Ξ [=] empty ->
     Δ ∩ dom Θ1 [<=] dom (Ξ ++ Θ0) ->
     (forall α, α `in` Δ -> α `notin` dom Θ0 -> α `notin` ftvar_in_pskl P) ->
     no_flex_dep Δ Θ1 /\ flex_above_free Δ Θ1 /\
     (forall α, α `in` Δ -> α `in` dom Θ1 -> α `in` (dom Ξ `union` dom Θ0))) /\
  ad_pat_consis empty Θ1 (pskl_to_uskl P) (bskl_var_f α).

Definition assign_sound_concl (Θ0 Ξ : aenv) (α : atom)
    (P : pskl) (Θ1 : aenv) : Prop :=
  a_decls Ξ ->
  {{ ⊢ (Ξ ++ Θ0) }}a ->
  {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P }}a ->
  assign_sound_post Θ0 Ξ α P Θ1.

(** Invariant preservation descends through a shared rigid binder when
    opening adds at most that binder to the input free-variable bound. *)
Lemma sound_invariants_strip_tvar : forall α Θ0 Θ1 F Fopen,
  Fopen [<=] add α F ->
  (forall Δ,
    no_flex_dep Δ ((α ~ abind_tvar) ++ Θ0) ->
    flex_above_free Δ ((α ~ abind_tvar) ++ Θ0) ->
    Δ ∩ dom ((α ~ abind_tvar) ++ Θ1) [<=]
      dom ((α ~ abind_tvar) ++ Θ0) ->
    (forall β, β `in` Δ -> β `notin` dom ((α ~ abind_tvar) ++ Θ0) ->
      β `notin` Fopen) ->
    no_flex_dep Δ ((α ~ abind_tvar) ++ Θ1) /\
    flex_above_free Δ ((α ~ abind_tvar) ++ Θ1) /\
    (forall β, β `in` Δ -> β `in` dom ((α ~ abind_tvar) ++ Θ1) ->
      β `in` dom ((α ~ abind_tvar) ++ Θ0))) ->
  forall Δ,
    no_flex_dep Δ Θ0 -> flex_above_free Δ Θ0 ->
    Δ ∩ dom Θ1 [<=] dom Θ0 ->
    (forall β, β `in` Δ -> β `notin` dom Θ0 -> β `notin` F) ->
    no_flex_dep Δ Θ1 /\ flex_above_free Δ Θ1 /\
    (forall β, β `in` Δ -> β `in` dom Θ1 -> β `in` dom Θ0).
Proof.
  intros α Θ0 Θ1 F Fopen Hopen Hinv Δ Hnd Hfa Hcov Hft.
  destruct (Hinv Δ) as [Hnd' [Hfa' _]].
  - intros β τ Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | exact (Hnd β τ Hb') ].
  - apply faf_cons; [ congruence | exact Hfa ].
  - simpl; clear - Hcov; fsetdec.
  - intros β Hβ Hfresh. simpl in Hfresh.
    assert (Hβ0 : β `notin` dom Θ0) by (clear - Hfresh; fsetdec).
    pose proof (Hft β Hβ Hβ0) as Havoid.
    clear - Havoid Hfresh Hopen; fsetdec.
  - split.
    + intros β τ Hb. apply (Hnd' β τ). unfold binds; right; exact Hb.
    + split; [ eapply faf_tail; exact Hfa' | ].
      intros β Hβ Hd; clear - Hcov Hβ Hd; fsetdec.
Qed.

(** The ∀-cases' renaming side conditions (see [*_rename_gen]): the
    opened context's definitions avoid both the old and the new opener. *)
Lemma rename_defs_cons_tvar : forall Θ1 α α0,
  {{ ⊢ Θ1 }}a ->
  α `notin` dom Θ1 ->
  α0 `notin` dom Θ1 ->
  forall β τ, binds β (abind_flex_mono_def τ) ((α ~ abind_tvar) ++ Θ1) ->
    binds β (abind_flex_mono_def τ) ((α0 ~ abind_tvar) ++ Θ1) /\ β <> α /\
    α `notin` ftvar_in_ptyp τ /\ α0 `notin` ftvar_in_ptyp τ.
Proof.
  intros * Hwf Hα Hα0 β τ Hb.
  destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb']; [ discriminate | ].
  pose proof (@a_wf_aenv_def_ftv_dom Θ1 β τ Hwf Hb') as Hsc.
  pose proof (binds_In _ _ _ _ Hb') as Hβ.
  split; [ unfold binds; right; exact Hb' | ].
  split; [ intros ->; contradiction | ].
  split; clear - Hsc Hα Hα0; fsetdec.
Qed.

(** [α0 ∉ ftv (open X α)] from freshness for [X] and [α]. *)
Ltac fresh_open_rhs Hfr :=
  match goal with
  | |- ?a `notin` ftvar_in_pskl (open_pskl_wrt_pskl ?X ?Y) =>
      let Hup := fresh "Hup" in
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper X Y) as Hup;
      simpl in Hup; clear - Hup Hfr; fsetdec
  | |- ?a `notin` ftvar_in_bskl ?X => clear - Hfr; fsetdec
  end.

(** A fresh consistency instance supplies the family needed to close a binder. *)
Lemma ad_pat_consis_close_open : forall Ψ Θ R Q α,
  {{ ⊢ Θ }}a -> α `notin` dom Θ -> α `notin` ftvar_in_uskl R ->
  {{ Ψ ⨟ ((α ~ abind_tvar) ++ Θ) ⊢ˢ
     (open_uskl_wrt_uskl R (uskl_var_f α)) ∼ Q }}ad ->
  forall β,
  {{ Ψ ⨟ ((β ~ abind_tvar) ++ Θ) ⊢ˢ
     (open_uskl_wrt_uskl R (uskl_var_f β))
     ∼ (open_bskl_wrt_bskl (close_bskl_wrt_bskl α Q) (bskl_var_f β)) }}ad.
Proof.
  intros Ψ Θ R Q α Hwf Hα Hfr Hcons β.
  rewrite (subst_uskl_in_uskl_intro α R (uskl_var_f β) Hfr).
  rewrite <- (subst_bskl_in_bskl_spec Q (bskl_var_f β) α).
  change ((β ~ abind_tvar) ++ Θ) with (nil ++ (β ~ abind_tvar) ++ Θ).
  eapply ad_pat_consis_rename_tvar;
    [exact Hcons | exact Hα | eapply a_wf_aenv_def_ftv_notin; eauto].
Qed.

(** Close a refinement proved at one fresh rigid opener. *)
Lemma ad_refine_syn_close_all : forall Θ Δ P Q α,
  {{ ⊢ Θ }}a -> α `notin` dom Θ -> α `notin` ftvar_in_pskl P ->
  {{ ((α ~ abind_tvar) ++ Θ) ⨟ (add α Δ) ⊢ᵣ
     (pskl_to_bskl_inh (open_pskl_wrt_pskl P (pskl_var_f α))) ⊳ Q }}ad ->
  {{ Θ ⨟ Δ ⊢ᵣ (bskl_all_inh (pskl_to_bskl_inh P))
     ⊳ (bskl_all_inh (close_bskl_wrt_bskl α Q)) }}ad.
Proof.
  intros Θ Δ P Q α Hwf Hα Hfr Href.
  apply ad_refine_syn_all_intro
    with (L := dom Θ `union` singleton α `union` ftvar_in_pskl P
               `union` ftvar_in_bskl Q).
  intros β Hβ.
  rewrite <- pskl_to_bskl_inh_open.
  rewrite <- (subst_bskl_in_bskl_spec Q (bskl_var_f β) α).
  rewrite (subst_pskl_in_pskl_intro α P (pskl_var_f β) Hfr).
  rewrite <- subst_var_bskl_inh.
  eapply ad_refine_syn_delta_mono with (Δ0 := add β (add α Δ));
    [ | clear; fsetdec ].
  eapply ad_refine_syn_rename_gen;
    [ exact Href | clear; fsetdec | fresh_open_rhs Hβ
    | eapply rename_defs_cons_tvar; [exact Hwf | exact Hα | clear - Hβ; fsetdec] ].
Qed.

Lemma ad_refine_pskl_close_all : forall Θ Δ P Q α,
  {{ ⊢ Θ }}a -> α `notin` dom Θ ->
  α `notin` ftvar_in_pskl P `union` ftvar_in_pskl Q ->
  {{ ((α ~ abind_tvar) ++ Θ) ⨟ (add α Δ) ⊢ᵣₚ
     (open_pskl_wrt_pskl P (pskl_var_f α))
     ⊳ (open_pskl_wrt_pskl Q (pskl_var_f α)) }}ad ->
  {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_all_syn P) ⊳ (pskl_all_syn Q) }}ad.
Proof.
  intros Θ Δ P Q α Hwf Hα Hfr Href.
  apply ad_refine_pskl__all
    with (L := dom Θ `union` singleton α
               `union` ftvar_in_pskl P `union` ftvar_in_pskl Q).
  intros β Hβ.
  rewrite (subst_pskl_in_pskl_intro α P (pskl_var_f β))
    by (clear - Hfr; fsetdec).
  rewrite (subst_pskl_in_pskl_intro α Q (pskl_var_f β))
    by (clear - Hfr; fsetdec).
  eapply ad_refine_pskl_delta_mono with (Δ0 := add β (add α Δ));
    [ | clear; fsetdec ].
  eapply ad_refine_pskl_rename_gen;
    [ exact Href | clear; fsetdec | fresh_open_rhs Hβ
    | eapply rename_defs_cons_tvar; [exact Hwf | exact Hα | clear - Hβ; fsetdec] ].
Qed.

Lemma ad_refine_syn_close_univ_ghost : forall Θ Δ P Q α,
  {{ ⊢ Θ }}a -> α `notin` dom Θ -> α `notin` ftvar_in_pskl P ->
  {{ ((α ~ abind_tvar) ++ Θ) ⨟ Δ ⊢ᵣ
     (bskl_univ_ghost (pskl_to_bskl_inh P)) ⊳ Q }}ad ->
  {{ Θ ⨟ Δ ⊢ᵣ (bskl_univ_ghost (pskl_to_bskl_inh P))
     ⊳ (bskl_all_syn (close_bskl_wrt_bskl α Q)) }}ad.
Proof.
  intros Θ Δ P Q α Hwf Hα Hfr Href.
  pose proof (a_wf_aenv_def_ftv_notin Hwf Hα) as Hdefs.
  apply ad_refine_syn_univ_ghost_fill_intro
    with (L := dom Θ `union` singleton α `union` Δ).
  intros β Hβ.
  rewrite <- (subst_bskl_in_bskl_spec Q (bskl_var_f β) α).
  replace (bskl_univ_ghost (pskl_to_bskl_inh P))
    with (subst_bskl_in_bskl (bskl_var_f β) α
      (bskl_univ_ghost (pskl_to_bskl_inh P)))
    by (simpl; rewrite subst_var_bskl_inh, subst_pskl_in_pskl_fresh_eq;
        [reflexivity | exact Hfr]).
  eapply ad_refine_syn_rename_ctx_gen with (Θ1 := nil);
    [ exact Href | exact Hα | exact Hdefs | clear - Hβ; fsetdec ].
Qed.

(** The flexible-variable rows of consistency (Flex, FlexL, FlexR), plain
    and decorated, share their bookkeeping: the subject variable is
    flexible, so it avoids the protected Δ and survives into the output, and
    the problem invariants carry over at the protected Δ itself. *)

(** Flex: from the unification post-condition to the row's output. *)
Lemma unify_sound_flex_out : forall Δ1 Δ2 Θ0 Θ1 α β,
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a ->
  unify_sound_post Θ0 α β Θ1 ->
  (forall α0, α0 `in` (Δ1 `union` Δ2) -> binds α0 abind_tvar Θ0) ->
  no_flex_dep (Δ1 `union` Δ2) Θ0 -> flex_above_free (Δ1 `union` Δ2) Θ0 ->
  no_flex_dep (Δ1 `union` Δ2) Θ1 /\ flex_above_free (Δ1 `union` Δ2) Θ1 /\
  (forall Ψ, Ψ [=] empty ->
   (exists Qt, bskl_to_pskl Qt = pskl_var_f α /\
      {{ Ψ ⨟ Θ1 ⊢ˢ (uskl_var_f α) ∼ Qt }}ad /\
      {{ Θ1 ⨟ Δ1 ⊢ᵣ (pskl_to_bskl_inh (pskl_var_f β)) ⊳ Qt }}ad) /\
   {{ Θ1 ⨟ Δ2 ⊢ᵣₚ (pskl_var_f α) ⊳ (pskl_var_f α) }}ad).
Proof.
  intros Δ1 Δ2 Θ0 Θ1 α β Hwf Hu [Hle [Hwf1 [_ [Hinv Heq1]]]] Hrig Hnfd Hfaf.
  destruct (a_unify_subjects_flex Hwf Hu) as [Hfα Hfβ].
  pose proof (faf_flex_tvar_notin Hfaf Hfα) as HαnΔ.
  destruct (Hinv (Δ1 `union` Δ2) Hnfd Hfaf) as [Hnfd1 [Hfaf1 _]].
  { intros α0 Hα0.
    assert (Hα0' : α0 `in` (Δ1 `union` Δ2)) by (clear - Hα0; fsetdec).
    apply Hrig in Hα0'. apply binds_In in Hα0'. exact Hα0'. }
  pose proof (a_isub_flex_binds_tvar Hle Hfα) as Hbα1.
  pose proof (a_isub_flex_binds_tvar Hle Hfβ) as Hbβ1.
  split; [ exact Hnfd1 | ]. split; [ exact Hfaf1 | ].
  intros Ψ HΨ. split.
  - exists (bskl_var_f α). split; [ reflexivity | ].
    split.
    + apply ad_pat_consis__var; [ exact HΨ | exact Hbα1 ].
    + assert (Hcbα : ad_pat_consis empty Θ1
                (ptyp_to_uskl_syn (ptyp_var_f β))
                (ptyp_to_bskl_syn (ptyp_var_f α))).
      { apply tyequiv_mono_consis;
          [ apply a_tyequiv__sym; exact Heq1 | exact Hwf1
          | constructor | ].
        intros α0 Hα0. simpl in Hα0.
        assert (α0 = β) by (clear - Hα0; fsetdec). subst. exact Hbβ1. }
      replace (pskl_to_bskl_inh (pskl_var_f β))
        with (pskl_to_bskl_inh
                (uskl_to_pskl (ptyp_to_uskl_syn (ptyp_var_f β))))
        by (rewrite uskl_to_pskl_ptyp; reflexivity).
      replace (bskl_var_f α) with (ptyp_to_bskl_syn (ptyp_var_f α))
        by reflexivity.
      eapply ad_pat_consis_refine_syn_mono;
        [ exact Hcbα | exact Hwf1
        | apply mono_ptyp_to_bskl_syn; constructor | | ].
      { rewrite ftvar_ptyp_to_bskl_syn. simpl. clear - HαnΔ. fsetdec. }
      { intros α1 τ Hb. eapply (Hnfd1 α1 τ) in Hb. clear - Hb. fsetdec. }
  - apply ad_refine_pskl__var.
Qed.

(** FlexL / FlexR: what the assignment post-condition gives the row. *)
Lemma assign_sound_flex_frame : forall Δ1 Δ2 Θ0 Θ1 α P,
  assign_sound_post Θ0 nil α P Θ1 ->
  a_flex_tvar Θ0 α ->
  (forall α0, α0 `in` (Δ1 `union` Δ2) -> binds α0 abind_tvar Θ0) ->
  no_flex_dep (Δ1 `union` Δ2) Θ0 -> flex_above_free (Δ1 `union` Δ2) Θ0 ->
  α `notin` (Δ1 `union` Δ2) /\ a_binds_tvar α Θ1 /\
  no_flex_dep (Δ1 `union` Δ2) Θ1 /\ flex_above_free (Δ1 `union` Δ2) Θ1.
Proof.
  intros Δ1 Δ2 Θ0 Θ1 α P [Hle [_ [_ [Hinv _]]]] Hfα Hrig Hnfd Hfaf.
  assert (HΔdom : Δ1 `union` Δ2 [<=] dom Θ0).
  { intros α0 Hα0. apply binds_In with (a := abind_tvar). apply Hrig; auto. }
  destruct (Hinv (Δ1 `union` Δ2)) as [Hnd [Hfa _]].
  - exact Hnfd.
  - exact Hfaf.
  - simpl. clear. fsetdec.
  - simpl. clear - HΔdom. fsetdec.
  - intros α0 Hα0 Hnd0. exfalso. apply Hnd0. apply HΔdom. exact Hα0.
  - split; [ exact (faf_flex_tvar_notin Hfaf Hfα) | ].
    split; [ exact (a_isub_flex_binds_tvar Hle Hfα) | ]. split; assumption.
Qed.

(** FlexL / FlexR (plain): the assignment's invariant conjunct, read at the
    row's two input skeletons. *)
Lemma assign_sound_consis_inv : forall Θ0 Θ1 α Pa P0 P,
  assign_sound_post Θ0 nil α Pa Θ1 ->
  ftvar_in_pskl Pa [<=] ftvar_in_pskl P0 `union` ftvar_in_pskl P ->
  forall Δ,
  no_flex_dep Δ Θ0 -> flex_above_free Δ Θ0 ->
  Δ ∩ dom Θ1 [<=] dom Θ0 ->
  (forall α, α `in` Δ -> α `notin` dom Θ0 ->
     α `notin` (ftvar_in_pskl P0 `union` ftvar_in_pskl P)) ->
  no_flex_dep Δ Θ1 /\ flex_above_free Δ Θ1 /\
  (forall α, α `in` Δ -> α `in` dom Θ1 -> α `in` dom Θ0).
Proof.
  intros Θ0 Θ1 α Pa P0 P [_ [_ [_ [Hinv _]]]] Hsub Δ HndΔ HfaΔ HcovΔ Hft.
  destruct (Hinv Δ) as [Hnd' [Hfa' _]].
  - exact HndΔ.
  - exact HfaΔ.
  - simpl. clear. fsetdec.
  - simpl. clear - HcovΔ. fsetdec.
  - intros α0 Hα0 HXd. pose proof (Hft α0 Hα0 HXd) as Hf0.
    clear - Hf0 Hsub. fsetdec.
  - split; [ exact Hnd' | ]. split; [ exact Hfa' | ].
    intros α0 Hα0 HXd. clear - HcovΔ Hα0 HXd; fsetdec.
Qed.

(** FlexL: the output for the assigned input skeleton [P0]. *)
Lemma consis_sound_flex_l_out : forall Ψ Δ1 Δ2 Θ1 α P0,
  ad_pat_consis empty Θ1 (pskl_to_uskl P0) (bskl_var_f α) ->
  {{ ⊢ Θ1 }}a ->
  α `notin` (Δ1 `union` Δ2) -> a_binds_tvar α Θ1 ->
  no_flex_dep (Δ1 `union` Δ2) Θ1 ->
  Ψ [=] empty ->
  (exists Qt, bskl_to_pskl Qt = pskl_var_f α /\
     {{ Ψ ⨟ Θ1 ⊢ˢ (uskl_var_f α) ∼ Qt }}ad /\
     {{ Θ1 ⨟ Δ1 ⊢ᵣ (pskl_to_bskl_inh P0) ⊳ Qt }}ad) /\
  {{ Θ1 ⨟ Δ2 ⊢ᵣₚ (pskl_var_f α) ⊳ (pskl_var_f α) }}ad.
Proof.
  intros Ψ Δ1 Δ2 Θ1 α P0 Hcons Hwf1 HαnΔ Hbα1 Hnfd1 HΨ.
  split.
  - exists (bskl_var_f α). split; [ reflexivity | ].
    split.
    + apply ad_pat_consis__var; [ exact HΨ | exact Hbα1 ].
    + replace (pskl_to_bskl_inh P0)
        with (pskl_to_bskl_inh (uskl_to_pskl (pskl_to_uskl P0)))
        by (rewrite uskl_to_pskl_pskl_to_uskl; reflexivity).
      eapply ad_pat_consis_refine_syn_mono;
        [ exact Hcons | exact Hwf1 | apply mono_bskl__var | | ].
      { simpl. clear - HαnΔ. fsetdec. }
      { intros α1 τ Hb. eapply (Hnfd1 α1 τ) in Hb. clear - Hb. fsetdec. }
  - apply ad_refine_pskl__var.
Qed.

(** FlexR: the output for the assigned subject skeleton [P]. *)
Lemma consis_sound_flex_r_out : forall Ψ Δ1 Δ2 Θ1 α P,
  ad_pat_consis empty Θ1 (pskl_to_uskl P) (bskl_var_f α) ->
  {{ ⊢ Θ1 }}a ->
  α `notin` (Δ1 `union` Δ2) ->
  no_flex_dep (Δ1 `union` Δ2) Θ1 ->
  Ψ [=] empty ->
  (exists Qt, bskl_to_pskl Qt = pskl_var_f α /\
     {{ Ψ ⨟ Θ1 ⊢ˢ (pskl_to_uskl P) ∼ Qt }}ad /\
     {{ Θ1 ⨟ Δ1 ⊢ᵣ (pskl_to_bskl_inh (pskl_var_f α)) ⊳ Qt }}ad) /\
  {{ Θ1 ⨟ Δ2 ⊢ᵣₚ P ⊳ (pskl_var_f α) }}ad.
Proof.
  intros Ψ Δ1 Δ2 Θ1 α P Hcons Hwf1 HαnΔ Hnfd1 HΨ.
  split.
  - exists (bskl_var_f α). split; [ reflexivity | ].
    split.
    + eapply ad_pat_consis_psi_cong; [ exact Hcons | symmetry; exact HΨ ].
    + apply ad_refine_syn__var.
  - replace (pskl_var_f α) with (bskl_to_pskl (bskl_var_f α)) by reflexivity.
    replace P with (uskl_to_pskl (pskl_to_uskl P)) at 1
      by (rewrite uskl_to_pskl_pskl_to_uskl; reflexivity).
    eapply ad_pat_consis_refine_pskl_mono;
      [ exact Hcons | exact Hwf1 | apply mono_bskl__var | | ].
    { simpl. clear - HαnΔ. fsetdec. }
    { intros α1 τ Hb. eapply (Hnfd1 α1 τ) in Hb. clear - Hb. fsetdec. }
Qed.

Theorem a_assign_unify_consis_sound :
  (forall Θ0 Ξ α P Θ1,
     {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a -> assign_sound_concl Θ0 Ξ α P Θ1) /\
  (forall Θ0 α β Θ1,
     {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a -> unify_sound_concl Θ0 α β Θ1) /\
  (forall Δ1 Δ2 Θ0 P0 P P3 Θ1,
     {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ P3 ⊣ Θ1 }}a ->
     consis_sound_concl Δ1 Δ2 Θ0 P0 P P3 Θ1).
Proof.
  apply a_assign_unify_consis_mutind;
    unfold assign_sound_concl, unify_sound_concl, consis_sound_concl,
           assign_sound_post, unify_sound_post, consis_sound_post.
  - (* Assign-UnivGhost-Id *)
    intros Θ0 α Hdecl Hwf HwfP.
    split; [ apply a_isub_refl; try assumption; auto | ].
    split; [ exact Hwf | ].
    split; [ simpl; clear; fsetdec | ].
    split.
    { intros Δ Hnd Hfaf HΔΞ Hcov HP.
      split; [ exact Hnd | ]. split; [ exact Hfaf | ].
      intros α0 _ Hα0. simpl in Hα0. simpl. clear - Hα0. fsetdec. }
    replace (pskl_to_uskl (pskl_univ_ghost (pskl_var_f α)))
      with (uskl_univ_ghost (uskl_var_f α)) by reflexivity.
    apply ad_pat_consis__univ_ghost_drop.
    apply ad_pat_consis__var; [ clear; fsetdec | ].
    right; left. unfold binds; left; reflexivity.

  - (* Assign-SolveM *)
    intros Θ0 Ξ α P βs τ Hαn Hg Hmτ Huβs Hfr Hdecl Hwf HwfP.
    assert (Hvis : forall α0, α0 `in` ftvar_in_pskl P ->
                   a_binds_tvar α0 (Ξ ++ (α ~ abind_flex_mono) ++ Θ0)).
    { intros α0 Hα0. exact (a_wf_pskl_ftv_binds HwfP Hα0). }
    assert (Hβsd : a_decls βs) by (eapply a_guess_mono_decls; eauto).
    assert (Huniq : uniq (Ξ ++ (α ~ abind_flex_mono) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (HwfΞΘ : {{ ⊢ (Ξ ++ Θ0) }}a)
      by (eapply a_wf_aenv_strip_mid; eauto).
    assert (Hαd : α `notin` dom (Ξ ++ Θ0))
      by (repeat rewrite dom_app in *; solve_uniq).
    assert (Hle : (Ξ ++ (α ~ abind_flex_mono) ++ Θ0) ⊴
                  ((α ~ abind_flex_mono_def τ) ++ βs ++ Ξ ++ Θ0)).
    { apply a_isub_prepend_decls_src; auto.
      { intros α1 Hb. right; left.
        unfold binds. apply in_or_app; right.
        apply in_or_app; right. apply in_or_app; left. exact Hb. }
      apply a_isub_prepend_decls_src;
        [ apply (a_decls__cons α); constructor
        | intros α1 Hb;
          destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
          [ subst; right; right; exists τ; unfold binds;
            apply in_or_app; left; left; reflexivity
          | inversion Hb' ]
        | ].
      assert (Hs1 : Θ0 ⊴ ((βs ++ Ξ) ++ Θ0)).
      { pose proof (a_wf_aenv_lc_aenv HwfΞΘ) as Hlca.
        apply lc_aenv_app_inv in Hlca as [_ Hlc0].
        apply a_isub_weaken_suffix; [ exact Hlc0 | ].
        apply a_suffix_app; auto using a_decls_suffix. }
      first [ rewrite <- app_assoc in Hs1 | rewrite app_assoc in Hs1 ].
      apply a_isub_target_weaken with (Ξ := (α ~ abind_flex_mono_def τ))
        in Hs1; auto.
      apply (a_suffix__cons α (b := abind_flex_mono_def τ)); constructor. }
    assert (Hβsfr : forall α1, α1 `in` dom βs -> α1 `notin` dom (Ξ ++ Θ0)).
    { intros α1 Hα1. pose proof (Hfr α1 Hα1) as Hh.
      repeat rewrite dom_app in *. clear - Hh. fsetdec. }
    assert (Hβswf : {{ ⊢ (βs ++ Ξ ++ Θ0) }}a).
    { apply a_wf_aenv_prepend_flex;
        [ intros α1 b Hb; eapply a_guess_mono_flex_binds; eauto
        | exact Huβs
        | intros α1 Hα1;
          (assert (Hf : α1 `notin` dom (Ξ ++ Θ0)) by (apply Hβsfr; auto));
          repeat rewrite dom_app in *; clear - Hf; fsetdec
        | exact HwfΞΘ ]. }
    assert (Hαβs : α `notin` dom βs).
    { intro Hin. pose proof (Hfr α Hin) as Hh. clear - Hh. fsetdec. }
    assert (Hwf1 : {{ ⊢ ((α ~ abind_flex_mono_def τ) ++ βs ++ Ξ ++ Θ0) }}a).
    { apply a_wf_aenv__flex_def; [ | | exact Hmτ | exact Hβswf ].
      { repeat rewrite dom_app in *. clear - Hαd Hαβs. fsetdec. }
      apply mono_ptyp_wf; auto.
      intros α0 Hα0.
      pose proof (a_guess_mono_ftv Hg Hα0) as Hin.
      destruct (union_1 Hin) as [HXP | Hα0βs].
      - assert (Hα0α : α0 <> α) by (intro; subst; auto).
        assert (Htv : a_binds_tvar α0 (Ξ ++ Θ0)).
        { eapply a_binds_tvar_strip_mid with
            (c := α) (b := abind_flex_mono);
            [ apply Hvis; auto
            | intro Hc; inversion Hc; congruence
            | intro Hc; inversion Hc; congruence
            | intros τ0 Hc; inversion Hc; congruence ]. }
        destruct Htv as [Hb | [Hb | [τ0 Hb]]];
          [ left | right; left | right; right; exists τ0 ];
          unfold binds; apply in_or_app; right; exact Hb.
      - right; left. unfold binds; apply in_or_app; left.
        apply binds_In_inv in Hα0βs. destruct Hα0βs as [b Hb].
        assert (Hbf : b = abind_flex_mono)
          by (eapply a_guess_mono_flex_binds; eauto). subst. exact Hb. }
    split; [ exact Hle | ].
    split; [ exact Hwf1 | ].
    split.
    { clear. repeat rewrite dom_app. simpl. fsetdec. }
    split.
    { intros Δ Hnd Hfaf HΔΞ Hcov HP.
      assert (Hhd : Δ ∩ (add α (dom Θ0)) [=] empty)
        by (apply (faf_head Hfaf); discriminate).
      assert (Hft : forall α0, α0 `in` Δ -> α0 `notin` ftvar_in_pskl P).
      { intros α0 Hα0Δ. apply HP; auto. simpl.
        assert (α0 `notin` add α (dom Θ0)) by (clear - Hhd Hα0Δ; fsetdec).
        auto. }
      (* the guessed block is excluded by the OUTPUT-relative coverage: a
         Δ-name among the [β̄] would be in the output's domain, hence — by
         [Hcov] — in the merged input's, which the rule's own side condition
         forbids *)
      assert (HβΔ : forall α0, α0 `in` Δ -> α0 `notin` dom βs).
      { intros α0 Hα0Δ Hα0β.
        assert (HXfr := Hfr α0 Hα0β).
        assert (HXcov : α0 `in` dom (Ξ ++ (α ~ abind_flex_mono) ++ Θ0)).
        { apply Hcov. apply inter_3; [ exact Hα0Δ | ].
          repeat rewrite dom_app. simpl. clear - Hα0β. fsetdec. }
        repeat rewrite dom_app in *. simpl in *.
        clear - HXfr HXcov. fsetdec. }
      assert (Hτ : Δ ∩ ftvar_in_ptyp τ [=] empty).
      { apply inter_empty_pointwise. intros α0 Hα0Δ Hα0τ.
        pose proof (a_guess_mono_ftv Hg Hα0τ) as Hin.
        assert (HnP : α0 `notin` ftvar_in_pskl P) by (apply Hft; auto).
        assert (Hnβ : α0 `notin` dom βs) by (apply HβΔ; auto).
        clear - Hin HnP Hnβ. fsetdec. }
      split; [ | split ].
      + intros β' τ' Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'].
        { inversion Heq; subst; exact Hτ. }
        apply in_app_or in Hb'. destruct Hb' as [Hbβ | HbΞΘ].
        { exfalso. eapply a_decls_no_def; eauto. }
        apply (Hnd β' τ').
        unfold binds. apply in_app_or in HbΞΘ. apply in_or_app.
        destruct HbΞΘ as [HbΞ | HbΘ]; [ auto | ].
        right. right. exact HbΘ.
      + apply faf_cons.
        { intros _. repeat rewrite dom_app.
          apply inter_empty_pointwise. intros α0 Hα0Δ HXin.
          assert (Hn1 : α0 `notin` add α (dom Θ0))
            by (clear - Hhd Hα0Δ; fsetdec).
          assert (Hn2 : α0 `notin` dom βs) by auto.
          assert (Hn3 : α0 `notin` dom Ξ) by (clear - HΔΞ Hα0Δ; fsetdec).
          clear - HXin Hn1 Hn2 Hn3. fsetdec. }
        apply faf_app.
        { apply inter_empty_pointwise. intros α0 Hα0Δ. auto. }
        { rewrite dom_app. apply inter_empty_pointwise.
          intros α0 Hα0Δ HXin.
          assert (Hn3 : α0 `notin` dom Ξ) by (clear - HΔΞ Hα0Δ; fsetdec).
          assert (Hn1 : α0 `notin` add α (dom Θ0))
            by (clear - Hhd Hα0Δ; fsetdec).
          clear - HXin Hn1 Hn3. fsetdec. }
        apply faf_app.
        { exact HΔΞ. }
        { apply inter_empty_pointwise. intros α0 Hα0Δ HXin.
          clear - Hhd Hα0Δ HXin. fsetdec. }
        eapply faf_tail; eauto.
      + intros α0 Hα0Δ HXd.
        repeat rewrite dom_app in *; simpl in *.
        clear - Hcov Hα0Δ HXd; fsetdec. }
    apply ad_pat_consis__flex_r with (τ := τ);
      [ unfold binds; left; reflexivity | ].
    eapply a_guess_mono_consis; eauto.
    { intros α0 Hα0. eapply a_isub_binds_tvarish; eauto. }
    { intros α1 Hb. right; left.
      unfold binds. apply in_or_app; right.
      apply in_or_app; left. exact Hb. }

  - (* Assign-Assign : the premise is a CONSISTENCY derivation, so the join
       [P3] must be eliminated — see the two subsidiary inductions above. *)
    intros Θ0 Θ1 Ξ α β τ P P3 Hfl Hbar Hc IHc Hdecl Hwf HwfP.
    assert (Hτ : a_wf_ptyp Θ0 τ /\ mono_ptyp τ)
      by (eapply a_wf_aenv_mid_def_inv; eauto).
    destruct Hτ as [Hτwf Hτm].
    assert (Hlcτ : lc_ptyp τ) by (eapply a_wf_ptyp_lc; eauto).
    assert (Huniq : uniq (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Hβd : β `notin` dom (Ξ ++ Θ0))
      by (repeat rewrite dom_app in *; solve_uniq).
    assert (Hβd0 : β `notin` dom Θ0)
      by (repeat rewrite dom_app in *; clear - Hβd; fsetdec).
    assert (HwfΞΘ : {{ ⊢ (Ξ ++ Θ0) }}a)
      by (eapply a_wf_aenv_strip_mid; eauto).
    assert (Hbβ : binds β (abind_flex_mono_def τ)
                    (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
      by (unfold binds; apply in_or_app; right; left; reflexivity).
    (* [τ] avoids [β̂] (it is well-formed strictly below it) *)
    assert (Hτfv : forall α0, α0 `in` ftvar_in_ptyp τ -> α0 `in` dom Θ0).
    { intros α0 Hα0.
      assert (Htv : a_binds_tvar α0 Θ0)
        by (eapply a_wf_ptyp_ftv_tvarish; eauto).
      destruct Htv as [Hb | [Hb | [τ0 Hb]]]; eapply binds_In; eauto. }
    assert (Hβτ : β `notin` ftvar_in_ptyp τ)
      by (intro Hin; apply Hβd0; apply Hτfv; exact Hin).
    (* the SUBSTITUTED SUBJECT is a monotype *)
    assert (Hmsub : mono_ptyp (subst_ptyp_in_ptyp τ β (ptyp_var_f α)))
      by (apply mono_ptyp_subst; [ constructor | exact Hτm ]).
    assert (Hsubvis : forall α0,
        α0 `in` ftvar_in_ptyp (subst_ptyp_in_ptyp τ β (ptyp_var_f α)) ->
        a_binds_tvar α0 (Ξ ++ Θ0)).
    { intros α0 Hα0.
      pose proof (ftvar_in_ptyp_subst_ptyp_in_ptyp_upper
                    (ptyp_var_f α) τ β) as Hup.
      assert (HX' : α0 `in` (ftvar_in_ptyp τ `union`
                            remove β (ftvar_in_ptyp (ptyp_var_f α))))
        by (clear - Hα0 Hup; fsetdec).
      destruct (union_1 HX') as [Hτ | Hα].
      - assert (Htv : a_binds_tvar α0 Θ0)
          by (eapply a_wf_ptyp_ftv_tvarish; eauto).
        destruct Htv as [Hb | [Hb | [τ0 Hb]]];
          [ left | right; left | right; right; exists τ0 ];
          unfold binds; apply in_or_app; right; exact Hb.
      - simpl in Hα.
        assert (Hα0α : α0 = α) by (clear - Hα; fsetdec).
        assert (Hα0β : α0 <> β) by (clear - Hα; fsetdec).
        subst α0.
        destruct Hfl as [Hb | [τ' Hb]];
          destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqx ?] | Hb'];
          try solve [ exfalso; apply Hα0β; exact Heqx ];
          [ right; left | right; right; exists τ' ];
          unfold binds; apply in_or_app; right; exact Hb'. }
    (* the two well-formedness obligations of the consistency IH *)
    assert (HwfP0 : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ
                      (subst_pskl_in_pskl (ptyp_to_pskl τ) β P) }}a).
    { eapply a_wf_pskl_strip_mid with (c := β) (b := abind_flex_mono_def τ).
      - apply a_wf_pskl_mono_subst; auto.
      - pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                      P (ptyp_to_pskl τ) β) as Hup.
        rewrite ftvar_ptyp_to_pskl in Hup.
        clear - Hup Hβτ. fsetdec. }
    assert (HwfS : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ
                     (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)) }}a).
    { rewrite subst_pskl_var_ptyp.
      apply mono_ptyp_wf_pskl; [ exact Hmsub | exact Hsubvis ]. }
    destruct (IHc HwfΞΘ HwfP0 HwfS
                ltac:(intros α0 Hα0; exfalso; clear - Hα0; solve_notin_auto)
                ltac:(intros β' τ' _; clear; solve_notin_auto)
                ltac:(intros Θa βa ba Θb Heq Hne; clear; solve_notin_auto))
      as [Hle [Hwf1 [Hdom [Hinv [[Qt [HeQt [HconsQ Hrs]]] Hrp]]]]].
    (* the walked head misses the output: the rule says so *)
    assert (Hβ1 : β `notin` dom Θ1) by exact Hbar.
    assert (Hle0 : Θ0 ⊴ Θ1)
      by (eapply a_isub_strengthen_decls_src; eauto).
    assert (HleF : ((β ~ abind_flex_mono_def τ) ++ Θ0) ⊴
                   ((β ~ abind_flex_mono_def τ) ++ Θ1))
      by (apply a_isub_cons_flex_def; auto).
    assert (Hwf1' : {{ ⊢ ((β ~ abind_flex_mono_def τ) ++ Θ1) }}a).
    { apply a_wf_aenv__flex_def; auto.
      eapply a_wf_ptyp_isub; eauto. }
    assert (Hbβ1 : binds β (abind_flex_mono_def τ)
                     ((β ~ abind_flex_mono_def τ) ++ Θ1))
      by (unfold binds; left; reflexivity).
    (* 1. increase *)
    split.
    { apply a_isub_prepend_decls_src; [ exact Hdecl | | exact HleF ].
      intros α1 Hb.
      apply a_binds_tvar_weaken_cons.
      eapply a_isub_binds_flex; [ exact Hle | ].
      unfold binds; apply in_or_app; left; exact Hb. }
    (* 2. well-formedness *)
    split; [ exact Hwf1' | ].
    (* 3. domain *)
    split.
    { clear - Hdom. repeat rewrite dom_app in *; simpl in *. fsetdec. }
    (* 4. the ∀Δ invariant *)
    split.
    { intros Δ Hnd Hfaf HΔΞ Hcov HP.
      assert (Hhd : Δ ∩ (add β (dom Θ0)) [=] empty)
        by (apply (faf_head Hfaf); discriminate).
      assert (Hτ0 : Δ ∩ ftvar_in_ptyp τ [=] empty)
        by (apply (Hnd β τ); exact Hbβ).
      destruct (Hinv Δ) as [IH1 [IH2 IH3]].
      { intros β' τ' Hb. apply (Hnd β' τ').
        apply (@binds_weaken abind β' (abind_flex_mono_def τ') Ξ
                 (β ~ abind_flex_mono_def τ) Θ0). exact Hb. }
      { apply faf_app.
        - exact HΔΞ.
        - clear - Hhd. fsetdec.
        - eapply faf_tail; eauto. }
      { (* the IH's OUTPUT-relative coverage: a Δ-name in the sub-run's
           output is in the conclusion's too, and it is not the walked head
           (the rule's own premise says the head misses that output) *)
        intros α0 Hα0.
        assert (HXc := Hcov α0 ltac:(clear - Hα0; simpl; solve_notin_auto)).
        clear - HXc Hα0 Hbar.
        repeat rewrite dom_app in *. simpl in *. fsetdec. }
      { intros α0 Hα0Δ HXd.
        repeat rewrite dom_app in HXd.
        assert (Hα0β : α0 <> β) by (intro; subst; clear - Hhd Hα0Δ; fsetdec).
        assert (Hα0Θ0 : α0 `notin` dom Θ0) by (clear - HXd; fsetdec).
        assert (Hα0τ : α0 `notin` ftvar_in_ptyp τ)
          by (clear - Hτ0 Hα0Δ; fsetdec).
        assert (HXP : α0 `notin` ftvar_in_pskl P).
        { apply HP;
            [ exact Hα0Δ | simpl; clear - Hα0β Hα0Θ0; fsetdec ]. }
        assert (HXsub : α0 `notin` ftvar_in_pskl
                          (subst_pskl_in_pskl (ptyp_to_pskl τ) β P)).
        { pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                        P (ptyp_to_pskl τ) β) as Hup.
          rewrite ftvar_ptyp_to_pskl in Hup.
          clear - Hup Hα0τ HXP. fsetdec. }
        assert (Hα0α : α0 <> α).
        { intro; subst α0.
          destruct Hfl as [Hb | [τ' Hb]];
            destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqx ?] | Hb'];
            [ apply Hα0β; exact Heqx | | apply Hα0β; exact Heqx | ];
            apply Hα0Θ0; eapply binds_In; eauto. }
        assert (HXv : α0 `notin` ftvar_in_pskl
                        (subst_pskl_in_pskl (ptyp_to_pskl τ) β
                           (pskl_var_f α))).
        { rewrite subst_pskl_var_ptyp. rewrite ftvar_ptyp_to_pskl.
          pose proof (ftvar_in_ptyp_subst_ptyp_in_ptyp_upper
                        (ptyp_var_f α) τ β) as Hup.
          simpl in Hup. clear - Hup Hα0τ Hα0α. fsetdec. }
        clear - HXsub HXv. fsetdec. }
      split; [ | split ].
      + intros β' τ' Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
          [ inversion Heq; subst; exact Hτ0 | exact (IH1 β' τ' Hb') ].
      + apply faf_cons; [ | exact IH2 ].
        intros _. repeat rewrite dom_app in *; simpl in *.
        clear - Hcov Hhd HΔΞ; fsetdec.
      + intros α0 Hα0Δ HXd.
        repeat rewrite dom_app in *; simpl in *.
        clear - Hcov Hα0Δ HXd; fsetdec. }
    (* 5. the augmented solution: eliminate the join [P3] *)
    (* (a) the join is a monotype painting, ≡ᵗ-equal to the subject *)
    rewrite subst_pskl_var_ptyp in HconsQ.
    rewrite pskl_to_uskl_ptyp in HconsQ.
    destruct (consis_mono_join HconsQ Hwf1
                (A := subst_ptyp_in_ptyp τ β (ptyp_var_f α))
                eq_refl Hmsub)
      as [C [HmC [HeqC HeqmC]]].
    (* (b) the refinement side: ⌊P[τ/β̂]⌋ ∼ P3  (subsidiary induction #1) *)
    assert (Hc0 : {{ empty ⨟ Θ1 ⊢ˢ
                    (pskl_to_uskl (subst_pskl_in_pskl (ptyp_to_pskl τ) β P))
                    ∼ Qt }}ad).
    { eapply refine_inh_mono_consis;
        [ exact Hrs
        | exact Hwf1
        | rewrite HeqC; apply mono_ptyp_to_bskl_syn; exact HmC
        | reflexivity
        | intros α0 Hα0;
          eapply ad_pat_consis_target_binds;
            [ exact HconsQ | apply uskl_no_ghost_ptyp | exact Hα0 ] ]. }
    (* (c) fold the definition on the SUBJECT side *)
    assert (Hc1 : {{ empty ⨟ ((β ~ abind_flex_mono_def τ) ++ Θ1) ⊢ˢ
                    (pskl_to_uskl P) ∼ Qt }}ad).
    { eapply ad_pat_consis_fold_def with
        (β := β) (τ := τ)
        (R' := pskl_to_uskl (subst_pskl_in_pskl (ptyp_to_pskl τ) β P));
        [ apply ad_pat_consis_weaken_cons; exact Hc0
        | exact Hbβ1
        | exact Hτm
        | apply pskl_to_uskl_subst ]. }
    (* (d) fold the definition on the JOIN side (subsidiary induction #2) *)
    assert (Hbα1 : a_binds_tvar α ((β ~ abind_flex_mono_def τ) ++ Θ1)).
    { eapply a_isub_binds_tvarish; [ exact HleF | ].
      destruct Hfl as [Hb | [τ' Hb]];
        [ right; left | right; right; exists τ' ]; exact Hb. }
    assert (Heqα : {{ ((β ~ abind_flex_mono_def τ) ++ Θ1) ⊢
                     (ptyp_var_f α) ≡ᵗ C }}a).
    { eapply a_tyequiv__trans.
      - eapply a_tyequiv_subst_def;
          [ exact Hbβ1 | apply mono_ptyp__var | exact Hlcτ ].
      - apply a_tyequiv_weaken_cons. exact HeqmC. }
    destruct (tyequiv_mono_consis_transport_q Heqα Hwf1'
                (mono_ptyp__var α)
                ltac:(intros α0 Hα0; simpl in Hα0;
                      assert (α0 = α) by (clear - Hα0; solve_notin_auto); subst;
                      exact Hbα1))
      as [Hq _].
    replace (bskl_var_f α) with (ptyp_to_bskl_syn (ptyp_var_f α))
      by reflexivity.
    apply Hq. rewrite <- HeqC. exact Hc1.

  - (* Assign-Depend : the pending suffix grows at the TAIL, so the IH's
       context is LITERALLY the conclusion's, re-associated. *)
    intros Θ0 Θ1 Ξ α β P Hne Hβin Ha IHa Hdecl Hwf HwfP.
    assert (Hdecl' : a_decls (Ξ ++ (β ~ abind_flex_mono)))
      by (apply a_decls_app;
          [ exact Hdecl | apply (a_decls__cons β); apply a_decls__nil ]).
    destruct (IHa Hdecl'
                ltac:(simpl_env; exact Hwf)
                ltac:(simpl_env; exact HwfP))
      as [Hle [Hwf1 [Hdom [Hinv Hcons]]]].
    simpl_env in Hle.
    split; [ exact Hle | ].
    split; [ exact Hwf1 | ].
    split.
    { clear - Hdom. repeat rewrite dom_app in *; simpl in *. fsetdec. }
    split.
    { intros Δ Hnd Hfaf HΔΞ Hcov HP.
      assert (Hhd : Δ ∩ (add β (dom Θ0)) [=] empty)
        by (apply (faf_head Hfaf); discriminate).
      destruct (Hinv Δ) as [IH1 [IH2 IH3]].
      { simpl_env. exact Hnd. }
      { eapply faf_tail; eauto. }
      { repeat rewrite dom_app; simpl.
        apply inter_empty_pointwise. intros α0 Hα0Δ HXin.
        assert (Hα0Ξ : α0 `notin` dom Ξ) by (clear - HΔΞ Hα0Δ; fsetdec).
        assert (Hα0β : α0 `notin` add β (dom Θ0))
          by (clear - Hhd Hα0Δ; fsetdec).
        clear - HXin Hα0Ξ Hα0β. fsetdec. }
      { intros α0 Hα0. assert (HXc := Hcov α0 Hα0).
        repeat rewrite dom_app in *; simpl in *. clear - HXc. fsetdec. }
      { intros α0 Hα0Δ HXd. apply HP;
          [ exact Hα0Δ | simpl; clear - Hhd Hα0Δ HXd; fsetdec ]. }
      split; [ exact IH1 | split; [ exact IH2 | ] ].
      intros α0 Hα0Δ HXd.
      specialize (IH3 α0 Hα0Δ HXd).
      repeat rewrite dom_app in *; simpl in *. clear - IH3. fsetdec. }
    exact Hcons.

  - (* Assign-Skip *)
    intros Θ0 Θ1 Ξ α β P Hne Hβn Hbar Ha IHa Hdecl Hwf HwfP.
    assert (Huniq : uniq (Ξ ++ (β ~ abind_flex_mono) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Hβd : β `notin` dom (Ξ ++ Θ0))
      by (repeat rewrite dom_app in *; solve_uniq).
    assert (HwfΞΘ : {{ ⊢ (Ξ ++ Θ0) }}a)
      by (eapply a_wf_aenv_strip_mid; eauto).
    assert (HwfP' : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P }}a)
      by (eapply a_wf_pskl_strip_mid; eauto).
    destruct (IHa Hdecl HwfΞΘ HwfP')
      as [Hle [Hwf1 [Hdom [Hinv Hcons]]]].
    (* the walked head misses the output: the rule says so *)
    assert (Hβ1 : β `notin` dom Θ1) by exact Hbar.
    split.
    { apply a_isub_prepend_decls_src; auto.
      { intros α1 Hb.
        apply a_binds_tvar_weaken_cons.
        eapply a_isub_binds_flex; [ exact Hle | ].
        unfold binds; apply in_or_app; left; exact Hb. }
      apply a_isub_cons_flex.
      eapply a_isub_strengthen_decls_src; eauto. }
    split; [ apply a_wf_aenv__flex; auto | ].
    split.
    { clear - Hdom. repeat rewrite dom_app in *; simpl in *. fsetdec. }
    split.
    { intros Δ Hnd Hfaf HΔΞ Hcov HP.
      assert (Hhd : Δ ∩ (add β (dom Θ0)) [=] empty)
        by (apply (faf_head Hfaf); discriminate).
      destruct (Hinv Δ) as [IH1 [IH2 IH3]].
      { intros β' τ' Hb. apply (Hnd β' τ').
        apply (@binds_weaken abind β' (abind_flex_mono_def τ') Ξ
                 (β ~ abind_flex_mono) Θ0). exact Hb. }
      { eapply faf_tail; eauto. }
      { exact HΔΞ. }
      { (* the IH's OUTPUT-relative coverage: a Δ-name in the sub-run's
           output is in the conclusion's too, and it is not the walked head
           (the rule's own premise says the head misses that output) *)
        intros α0 Hα0.
        assert (HXc := Hcov α0 ltac:(clear - Hα0; simpl; solve_notin_auto)).
        clear - HXc Hα0 Hbar.
        repeat rewrite dom_app in *. simpl in *. fsetdec. }
      { intros α0 Hα0Δ HXd. apply HP; auto. simpl.
        assert (α0 `notin` add β (dom Θ0)) by (clear - Hhd Hα0Δ; fsetdec).
        auto. }
      split; [ | split ].
      + intros β' τ' Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
          [ discriminate | exact (IH1 β' τ' Hb') ].
      + apply faf_cons; [ | exact IH2 ].
        intros _. repeat rewrite dom_app in *; simpl in *.
        clear - Hcov Hhd HΔΞ; fsetdec.
      + intros α0 Hα0Δ HXd.
        repeat rewrite dom_app in *; simpl in *.
        clear - Hcov Hα0Δ HXd; fsetdec. }
    apply ad_pat_consis_weaken_cons. exact Hcons.

  - (* Assign-SkipRigid *)
    intros Θ0 Θ1 Ξ α β P Hβn Hbar Ha IHa Hdecl Hwf HwfP.
    assert (Huniq : uniq (Ξ ++ (β ~ abind_tvar) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Hβd : β `notin` dom (Ξ ++ Θ0))
      by (repeat rewrite dom_app in *; solve_uniq).
    assert (HwfΞΘ : {{ ⊢ (Ξ ++ Θ0) }}a)
      by (eapply a_wf_aenv_strip_mid; eauto).
    assert (HwfP' : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P }}a)
      by (eapply a_wf_pskl_strip_mid; eauto).
    destruct (IHa Hdecl HwfΞΘ HwfP')
      as [Hle [Hwf1 [Hdom [Hinv Hcons]]]].
    (* the walked head misses the output: the rule says so *)
    assert (Hβ1 : β `notin` dom Θ1) by exact Hbar.
    split.
    { apply a_isub_prepend_decls_src; auto.
      { intros α1 Hb.
        apply a_binds_tvar_weaken_cons.
        eapply a_isub_binds_flex; [ exact Hle | ].
        unfold binds; apply in_or_app; left; exact Hb. }
      apply a_isub_cons_tvar.
      eapply a_isub_strengthen_decls_src; eauto. }
    split; [ apply a_wf_aenv__tvar; auto | ].
    split.
    { clear - Hdom. repeat rewrite dom_app in *; simpl in *. fsetdec. }
    split.
    { intros Δ Hnd Hfaf HΔΞ Hcov HP.
      destruct (Hinv Δ) as [IH1 [IH2 IH3]].
      { intros β' τ' Hb. apply (Hnd β' τ').
        apply (@binds_weaken abind β' (abind_flex_mono_def τ') Ξ
                 (β ~ abind_tvar) Θ0). exact Hb. }
      { eapply faf_tail; eauto. }
      { exact HΔΞ. }
      { (* the IH's OUTPUT-relative coverage: a Δ-name in the sub-run's
           output is in the conclusion's too, and it is not the walked head
           (the rule's own premise says the head misses that output) *)
        intros α0 Hα0.
        assert (HXc := Hcov α0 ltac:(clear - Hα0; simpl; solve_notin_auto)).
        clear - HXc Hα0 Hbar.
        repeat rewrite dom_app in *. simpl in *. fsetdec. }
      { intros α0 Hα0Δ HXd.
        destruct (eq_var α0 β) as [->|Hnex]; [ exact Hβn | ].
        apply HP; auto; simpl; auto. }
      split; [ | split ].
      + intros β' τ' Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
          [ discriminate | exact (IH1 β' τ' Hb') ].
      + apply faf_cons; [ intros Hne; congruence | exact IH2 ].
      + intros α0 Hα0Δ HXd.
        repeat rewrite dom_app in *; simpl in *.
        clear - Hcov Hα0Δ HXd; fsetdec. }
    apply ad_pat_consis_weaken_cons. exact Hcons.

  - (* Assign-SkipTmVar (typ) *)
    intros Θ0 Θ1 Ξ α x P3 P Hbar Ha IHa Hdecl Hwf HwfP.
    assert (Huniq : uniq (Ξ ++ (x ~ abind_var_typ P3) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Hxd : x `notin` dom (Ξ ++ Θ0))
      by (repeat rewrite dom_app in *; solve_uniq).
    assert (HwfΞΘ : {{ ⊢ (Ξ ++ Θ0) }}a)
      by (eapply a_wf_aenv_strip_mid; eauto).
    assert (Hxwf : {{ ⊢ ((x ~ abind_var_typ P3) ++ Θ0) }}a)
      by (eapply a_wf_aenv_strip_prefix; eauto).
    apply a_wf_aenv_var_typ_inv in Hxwf.
    destruct Hxwf as [_ [HQwf _]].
    (* a TERM variable cannot occur in a well-formed SKELETON *)
    assert (Hxn : x `notin` ftvar_in_pskl P).
    { intro Hin.
      pose proof (a_wf_pskl_ftv_binds HwfP Hin) as Ht.
      assert (Hbx : binds x (abind_var_typ P3)
                      (Ξ ++ (x ~ abind_var_typ P3) ++ Θ0))
        by (unfold binds; apply in_or_app; right; left; reflexivity).
      destruct Ht as [Hb | [Hb | [τ0 Hb]]];
        pose proof (binds_unique _ _ _ _ _ Hb Hbx Huniq) as He;
        discriminate He. }
    assert (HwfP' : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P }}a)
      by (eapply a_wf_pskl_strip_mid; eauto).
    destruct (IHa Hdecl HwfΞΘ HwfP')
      as [Hle [Hwf1 [Hdom [Hinv Hcons]]]].
    assert (Hx1 : x `notin` dom Θ1).
    exact Hbar.
    assert (Hle0 : Θ0 ⊴ Θ1)
      by (eapply a_isub_strengthen_decls_src; eauto).
    split.
    { apply a_isub_prepend_decls_src; auto.
      { intros α1 Hb.
        apply a_binds_tvar_weaken_cons.
        eapply a_isub_binds_flex; [ exact Hle | ].
        unfold binds; apply in_or_app; left; exact Hb. }
      apply a_isub_cons_var_typ; [ exact Hle0 | eapply a_wf_ptyp_lc; exact HQwf ]. }
    split.
    { apply a_wf_aenv__var_typ; auto.
      eapply a_wf_ptyp_isub; eauto. }
    split.
    { clear - Hdom. repeat rewrite dom_app in *; simpl in *. fsetdec. }
    split.
    { intros Δ Hnd Hfaf HΔΞ Hcov HP.
      assert (Hhd : Δ ∩ (add x (dom Θ0)) [=] empty)
        by (apply (faf_head Hfaf); discriminate).
      destruct (Hinv Δ) as [IH1 [IH2 IH3]].
      { intros β' τ' Hb. apply (Hnd β' τ').
        apply (@binds_weaken abind β' (abind_flex_mono_def τ') Ξ
                 (x ~ abind_var_typ P3) Θ0). exact Hb. }
      { eapply faf_tail; eauto. }
      { exact HΔΞ. }
      { (* the IH's OUTPUT-relative coverage: a Δ-name in the sub-run's
           output is in the conclusion's too, and it is not the walked head
           (the rule's own premise says the head misses that output) *)
        intros α0 Hα0.
        assert (HXc := Hcov α0 ltac:(clear - Hα0; simpl; solve_notin_auto)).
        clear - HXc Hα0 Hbar.
        repeat rewrite dom_app in *. simpl in *. fsetdec. }
      { intros α0 Hα0Δ HXd. apply HP; auto. simpl.
        assert (α0 `notin` add x (dom Θ0)) by (clear - Hhd Hα0Δ; fsetdec).
        auto. }
      split; [ | split ].
      + intros β' τ' Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
          [ discriminate | exact (IH1 β' τ' Hb') ].
      + apply faf_cons; [ | exact IH2 ].
        intros _. repeat rewrite dom_app in *; simpl in *.
        clear - Hcov Hhd HΔΞ; fsetdec.
      + intros α0 Hα0Δ HXd.
        repeat rewrite dom_app in *; simpl in *.
        clear - Hcov Hα0Δ HXd; fsetdec. }
    apply ad_pat_consis_weaken_cons. exact Hcons.

  - (* Assign-SkipTmVar (skl) *)
    intros Θ0 Θ1 Ξ α x P3 P Hbar Ha IHa Hdecl Hwf HwfP.
    assert (Huniq : uniq (Ξ ++ (x ~ abind_var_skl P3) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Hxd : x `notin` dom (Ξ ++ Θ0))
      by (repeat rewrite dom_app in *; solve_uniq).
    assert (HwfΞΘ : {{ ⊢ (Ξ ++ Θ0) }}a)
      by (eapply a_wf_aenv_strip_mid; eauto).
    assert (Hxwf : {{ ⊢ ((x ~ abind_var_skl P3) ++ Θ0) }}a)
      by (eapply a_wf_aenv_strip_prefix; eauto).
    apply a_wf_aenv_var_skl_inv in Hxwf.
    destruct Hxwf as [_ [HQwf _]].
    assert (Hxn : x `notin` ftvar_in_pskl P).
    { intro Hin.
      pose proof (a_wf_pskl_ftv_binds HwfP Hin) as Ht.
      assert (Hbx : binds x (abind_var_skl P3)
                      (Ξ ++ (x ~ abind_var_skl P3) ++ Θ0))
        by (unfold binds; apply in_or_app; right; left; reflexivity).
      destruct Ht as [Hb | [Hb | [τ0 Hb]]];
        pose proof (binds_unique _ _ _ _ _ Hb Hbx Huniq) as He;
        discriminate He. }
    assert (HwfP' : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P }}a)
      by (eapply a_wf_pskl_strip_mid; eauto).
    destruct (IHa Hdecl HwfΞΘ HwfP')
      as [Hle [Hwf1 [Hdom [Hinv Hcons]]]].
    assert (Hx1 : x `notin` dom Θ1).
    exact Hbar.
    assert (Hle0 : Θ0 ⊴ Θ1)
      by (eapply a_isub_strengthen_decls_src; eauto).
    split.
    { apply a_isub_prepend_decls_src; auto.
      { intros α1 Hb.
        apply a_binds_tvar_weaken_cons.
        eapply a_isub_binds_flex; [ exact Hle | ].
        unfold binds; apply in_or_app; left; exact Hb. }
      apply a_isub_cons_var_skl; [ exact Hle0 | eapply a_scope_pskl_lc; exact (a_scope_pskl_of_wf HQwf) ]. }
    split.
    { apply a_wf_aenv__var; auto.
      eapply a_wf_pskl_isub; eauto. }
    split.
    { clear - Hdom. repeat rewrite dom_app in *; simpl in *. fsetdec. }
    split.
    { intros Δ Hnd Hfaf HΔΞ Hcov HP.
      assert (Hhd : Δ ∩ (add x (dom Θ0)) [=] empty)
        by (apply (faf_head Hfaf); discriminate).
      destruct (Hinv Δ) as [IH1 [IH2 IH3]].
      { intros β' τ' Hb. apply (Hnd β' τ').
        apply (@binds_weaken abind β' (abind_flex_mono_def τ') Ξ
                 (x ~ abind_var_skl P3) Θ0). exact Hb. }
      { eapply faf_tail; eauto. }
      { exact HΔΞ. }
      { (* the IH's OUTPUT-relative coverage: a Δ-name in the sub-run's
           output is in the conclusion's too, and it is not the walked head
           (the rule's own premise says the head misses that output) *)
        intros α0 Hα0.
        assert (HXc := Hcov α0 ltac:(clear - Hα0; simpl; solve_notin_auto)).
        clear - HXc Hα0 Hbar.
        repeat rewrite dom_app in *. simpl in *. fsetdec. }
      { intros α0 Hα0Δ HXd. apply HP; auto. simpl.
        assert (α0 `notin` add x (dom Θ0)) by (clear - Hhd Hα0Δ; fsetdec).
        auto. }
      split; [ | split ].
      + intros β' τ' Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
          [ discriminate | exact (IH1 β' τ' Hb') ].
      + apply faf_cons; [ | exact IH2 ].
        intros _. repeat rewrite dom_app in *; simpl in *.
        clear - Hcov Hhd HΔΞ; fsetdec.
      + intros α0 Hα0Δ HXd.
        repeat rewrite dom_app in *; simpl in *.
        clear - Hcov Hα0Δ HXd; fsetdec. }
    apply ad_pat_consis_weaken_cons. exact Hcons.
  - (* U-Flex-Flex-Id *)
    intros Θ0 α Hb Hwf.
    split; [ apply a_isub_refl; try assumption; auto | ].
    split; [ exact Hwf | ].
    split; [ clear; fsetdec | ].
    split.
    { intros Δ Hnd Hfa _.
      split; [ exact Hnd | ]. split; [ exact Hfa | ].
      intros α0 _ Hα0; exact Hα0. }
    apply a_tyequiv__refl. constructor.
  - (* U-Flex-Flex-L : α̂ := β̂ *)
    intros Θ0 α β Hne Hfβ Hwf.
    assert (Hαd : α `notin` dom Θ0) by (inversion Hwf; auto).
    assert (Hwf0 : {{ ⊢ Θ0 }}a) by (inversion Hwf; auto).
    assert (Hbβ : a_binds_tvar β Θ0)
      by (destruct Hfβ as [Hb | [τ Hb]];
          [ right; left | right; right; exists τ ]; exact Hb).
    assert (Hβd : β `in` dom Θ0)
      by (destruct Hfβ as [Hb | [τ Hb]]; apply binds_In in Hb; auto).
    split.
    { split.
      - destruct (a_inc_refl_gen
          (Ξ0 := (α ~ abind_flex_mono_def (ptyp_var_f β)))
          (a_wf_aenv_lc_aenv Hwf0))
          as [κ0 [Hid0 Hinc0]].
        { apply (a_suffix__cons α (b := abind_flex_mono_def (ptyp_var_f β)));
            constructor. }
        exists ((α, ptyp_var_f α) :: κ0). split.
        { constructor; auto. unfold is_id_entry; reflexivity. }
        apply a_inc__flex; auto;
          try (apply a_wf_ptyp__var; right; right;
               exists (ptyp_var_f β); unfold binds; left; reflexivity);
          try constructor.
      - intros α1 τ0 Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
          [ discriminate | ].
        simpl. unfold binds. right. auto. }
    split.
    { apply a_wf_aenv__flex_def; auto.
      - apply a_wf_ptyp__var; exact Hbβ.
      - constructor. }
    split; [ simpl; clear; fsetdec | ].
    split.
    { intros Δ Hnd Hfa Hcov.
      assert (Hhd : Δ ∩ (add α (dom Θ0)) [=] empty)
        by (apply (faf_head Hfa); discriminate).
      split; [ | split ].
      - intros β' τ' Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'].
        + inversion Heq; subst. simpl.
          apply inter_empty_pointwise. intros α0 Hα0Δ Hα0β.
          assert (α0 = β) by (clear - Hα0β; fsetdec). subst.
          clear - Hhd Hα0Δ Hβd. fsetdec.
        + apply (Hnd β' τ'). unfold binds; right; exact Hb'.
      - apply faf_cons; [ | eapply faf_tail; eauto ].
        intros _. simpl. exact Hhd.
      - intros α0 Hα0Δ HXd. simpl in *. exact HXd. }
    apply a_tyequiv__flex_def. unfold binds; left; reflexivity.
  - (* U-Flex-Flex-R : β̂ := α̂ *)
    intros Θ0 α β Hne Hfα Hwf.
    assert (Hβd : β `notin` dom Θ0) by (inversion Hwf; auto).
    assert (Hwf0 : {{ ⊢ Θ0 }}a) by (inversion Hwf; auto).
    assert (Hbα : a_binds_tvar α Θ0)
      by (destruct Hfα as [Hb | [τ Hb]];
          [ right; left | right; right; exists τ ]; exact Hb).
    assert (Hαd : α `in` dom Θ0)
      by (destruct Hfα as [Hb | [τ Hb]]; apply binds_In in Hb; auto).
    split.
    { split.
      - destruct (a_inc_refl_gen
          (Ξ0 := (β ~ abind_flex_mono_def (ptyp_var_f α)))
          (a_wf_aenv_lc_aenv Hwf0))
          as [κ0 [Hid0 Hinc0]].
        { apply (a_suffix__cons β (b := abind_flex_mono_def (ptyp_var_f α)));
            constructor. }
        exists ((β, ptyp_var_f β) :: κ0). split.
        { constructor; auto. unfold is_id_entry; reflexivity. }
        apply a_inc__flex; auto;
          try (apply a_wf_ptyp__var; right; right;
               exists (ptyp_var_f α); unfold binds; left; reflexivity);
          try constructor.
      - intros α1 τ0 Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
          [ discriminate | ].
        simpl. unfold binds. right. auto. }
    split.
    { apply a_wf_aenv__flex_def; auto.
      - apply a_wf_ptyp__var; exact Hbα.
      - constructor. }
    split; [ simpl; clear; fsetdec | ].
    split.
    { intros Δ Hnd Hfa Hcov.
      assert (Hhd : Δ ∩ (add β (dom Θ0)) [=] empty)
        by (apply (faf_head Hfa); discriminate).
      split; [ | split ].
      - intros β' τ' Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'].
        + inversion Heq; subst. simpl.
          apply inter_empty_pointwise. intros α0 Hα0Δ Hα0α.
          assert (α0 = α) by (clear - Hα0α; fsetdec). subst.
          clear - Hhd Hα0Δ Hαd. fsetdec.
        + apply (Hnd β' τ'). unfold binds; right; exact Hb'.
      - apply faf_cons; [ | eapply faf_tail; eauto ].
        intros _. simpl. exact Hhd.
      - intros α0 Hα0Δ HXd. simpl in *. exact HXd. }
    apply a_tyequiv__sym.
    apply a_tyequiv__flex_def. unfold binds; left; reflexivity.
  - (* U-Flex-Flex-Assign : the consistency premise, through the BRIDGE *)
    intros Θ0 Θ1 α1 τ α β P3 Hfα Hfβ Hbar Hcons IHcons Hwf.
    inversion Hwf as [ | | γx τx Θx Hγd Hwτ Hmτ Hwf0 | | | ]; subst.
    (* the substituted subjects are visible monotypes over Θ0 *)
    assert (Hτvis : forall α0, α0 `in` ftvar_in_ptyp τ -> a_binds_tvar α0 Θ0)
      by (intros α0 Hα0; eapply a_wf_ptyp_ftv_tvarish; eauto).
    assert (Hsubvis : forall β1,
        a_flex_tvar ((α1 ~ abind_flex_mono_def τ) ++ Θ0) β1 ->
        forall α0, α0 `in` ftvar_in_ptyp (subst_ptyp_in_ptyp τ α1 (ptyp_var_f β1)) ->
        a_binds_tvar α0 Θ0).
    { intros β1 Hfδ α0 Hα0.
      pose proof (ftvar_in_ptyp_subst_ptyp_in_ptyp_upper
                    (ptyp_var_f β1) τ α1) as Hup.
      assert (HX' : α0 `in` (ftvar_in_ptyp τ `union`
                            remove α1 (ftvar_in_ptyp (ptyp_var_f β1))))
        by (clear - Hα0 Hup; fsetdec).
      destruct (union_1 HX') as [Hτ | Hβ1]; [ auto | ].
      simpl in Hβ1.
      assert (Hα0δ : α0 = β1) by (clear - Hβ1; fsetdec).
      assert (Hα0γ : α0 <> α1) by (clear - Hβ1; fsetdec).
      subst α0.
      destruct Hfδ as [Hb | [τ' Hb]];
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqx ?] | Hb'];
        try solve [ exfalso; apply Hα0γ; exact Heqx ];
        [ right; left | right; right; exists τ' ]; exact Hb'. }
    assert (HmA' : mono_ptyp (subst_ptyp_in_ptyp τ α1 (ptyp_var_f α)))
      by (apply mono_ptyp_subst; [ constructor | exact Hmτ ]).
    assert (HmB' : mono_ptyp (subst_ptyp_in_ptyp τ α1 (ptyp_var_f β)))
      by (apply mono_ptyp_subst; [ constructor | exact Hmτ ]).
    destruct (IHcons Hwf0) as
        [Hle [Hwf1 [Hdom [Hinv [[Qt [HeQt [HconsQ Hrs]]] _]]]]].
    { apply mono_ptyp_wf_pskl; [ exact HmB' | apply (Hsubvis β Hfβ) ]. }
    { apply mono_ptyp_wf_pskl; [ exact HmA' | apply (Hsubvis α Hfα) ]. }
    { intros α0 Hα0. exfalso. clear - Hα0. fsetdec. }
    { intros β' τ' _. clear. fsetdec. }
    { intros Θa βa ba Θb Heq Hne. clear. fsetdec. }
    assert (Hγd1 : α1 `notin` dom Θ1) by exact Hbar.
    split.
    { apply a_isub_cons_flex_def; auto. apply mono_ptyp_lc; auto. }
    split.
    { apply a_wf_aenv__flex_def; auto.
      apply mono_ptyp_wf; [ exact Hmτ | ].
      intros α0 Hα0. eapply a_isub_binds_tvarish; eauto. }
    split; [ simpl; clear - Hdom; fsetdec | ].
    split.
    { intros Δ Hnd Hfa Hcov.
      assert (Hhd : Δ ∩ (add α1 (dom Θ0)) [=] empty)
        by (apply (faf_head Hfa); discriminate).
      assert (Hτfree : Δ ∩ ftvar_in_ptyp τ [=] empty)
        by (apply (Hnd α1 τ); unfold binds; left; reflexivity).
      assert (Hsubfree : forall β1,
          a_flex_tvar ((α1 ~ abind_flex_mono_def τ) ++ Θ0) β1 ->
          forall α0, α0 `in` Δ ->
          α0 `notin` ftvar_in_pskl
              (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f β1)))).
      { intros β1 Hfδ α0 Hα0Δ.
        rewrite ftvar_ptyp_to_pskl.
        pose proof (ftvar_in_ptyp_subst_ptyp_in_ptyp_upper
                      (ptyp_var_f β1) τ α1) as Hup.
        intros HXin.
        assert (HX' : α0 `in` (ftvar_in_ptyp τ `union`
                              remove α1 (ftvar_in_ptyp (ptyp_var_f β1))))
          by (clear - HXin Hup; fsetdec).
        simpl in HX'.
        assert (Hδd : β1 `in` add α1 (dom Θ0)).
        { destruct Hfδ as [Hb | [τ' Hb]]; apply binds_In in Hb;
            simpl in Hb; clear - Hb; fsetdec. }
        clear - Hτfree Hα0Δ HX' Hhd Hδd. fsetdec. }
      destruct (Hinv Δ) as [Hnd1 [Hfa1 _]].
      { eapply no_flex_dep_tail; eauto. }
      { eapply faf_tail; eauto. }
      { intros α0 Hα0.
        assert (HXc := Hcov α0 ltac:(clear - Hα0; simpl; solve_notin_auto)).
        clear - HXc Hα0 Hbar. simpl in *. fsetdec. }
      { intros α0 Hα0 _.
        pose proof (Hsubfree β Hfβ α0 Hα0).
        pose proof (Hsubfree α Hfα α0 Hα0).
        clear - H H0. fsetdec. }
      split; [ | split ].
      - intros β' τ' Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
          [ inversion Heq; subst; exact Hτfree
          | exact (Hnd1 β' τ' Hb') ].
      - apply faf_cons; [ | exact Hfa1 ].
        intros _. simpl in *; clear - Hcov Hhd; fsetdec.
      - intros α0 Hα0Δ HXd.
        repeat rewrite dom_app in *; simpl in *.
        clear - Hcov Hα0Δ HXd; fsetdec. }
    (* the type equivalence, via the BRIDGE *)
    assert (HeqAB : {{ Θ1 ⊢ (subst_ptyp_in_ptyp τ α1 (ptyp_var_f α))
                       ≡ᵗ (subst_ptyp_in_ptyp τ α1 (ptyp_var_f β)) }}a).
    { eapply consis_refine_mono_tyequiv with (Qt := Qt); eauto.
      rewrite <- pskl_to_uskl_ptyp. exact HconsQ. }
    assert (Hlcτ : lc_ptyp τ) by (apply mono_ptyp_lc; assumption).
    assert (Hbγ : binds α1 (abind_flex_mono_def τ)
                    ((α1 ~ abind_flex_mono_def τ) ++ Θ1))
      by (unfold binds; left; reflexivity).
    eapply a_tyequiv__trans.
    { eapply a_tyequiv_subst_def; eauto. constructor. }
    eapply a_tyequiv__trans.
    { apply a_tyequiv_weaken_cons. exact HeqAB. }
    apply a_tyequiv__sym.
    eapply a_tyequiv_subst_def; eauto. constructor.
  - (* U-Flex-Flex-Skip *)
    intros Θ0 Θ1 α1 α β Hnα Hnβ Hbar Hu IHu Hwf.
    inversion Hwf as [ | γx Θx Hγd Hwf0 | | | | ]; subst.
    destruct (IHu Hwf0) as [Hle [Hwf1 [Hdom [Hinv Heq1]]]].
    assert (Hγd1 : α1 `notin` dom Θ1) by exact Hbar.
    split; [ apply a_isub_cons_flex; auto | ].
    split; [ apply a_wf_aenv__flex; auto | ].
    split; [ simpl; clear - Hdom; fsetdec | ].
    split.
    { intros Δ Hnd Hfa Hcov.
      assert (Hhd : Δ ∩ (add α1 (dom Θ0)) [=] empty)
        by (apply (faf_head Hfa); discriminate).
      destruct (Hinv Δ) as [Hnd1 [Hfa1 _]].
      { eapply no_flex_dep_tail; eauto. }
      { eapply faf_tail; eauto. }
      { intros α0 Hα0.
        assert (HXc := Hcov α0 ltac:(clear - Hα0; simpl; solve_notin_auto)).
        clear - HXc Hα0 Hbar. simpl in *. fsetdec. }
      split; [ | split ].
      - intros β' τ' Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
          [ discriminate | exact (Hnd1 β' τ' Hb') ].
      - apply faf_cons; [ | exact Hfa1 ].
        intros _. simpl in *; clear - Hcov Hhd; fsetdec.
      - intros α0 Hα0Δ HXd.
        repeat rewrite dom_app in *; simpl in *.
        clear - Hcov Hα0Δ HXd; fsetdec. }
    apply a_tyequiv_weaken_cons. exact Heq1.
  - (* U-Flex-Flex-Skip' *)
    intros Θ0 Θ1 c b α β Hb Hbar Hu IHu Hwf.
    assert (Hwf0c : {{ ⊢ Θ0 }}a /\ c `notin` dom Θ0).
    { destruct Hb as [-> | [[Qb ->] | [Qb ->]]].
      - apply a_wf_aenv_tvar_inv in Hwf; tauto.
      - apply a_wf_aenv_var_typ_inv in Hwf; destruct Hwf as [? [? ?]]; auto.
      - apply a_wf_aenv_var_skl_inv in Hwf; destruct Hwf as [? [? ?]]; auto. }
    destruct Hwf0c as [Hwf0 Hcd].
    destruct (IHu Hwf0) as [Hle [Hwf1 [Hdom [Hinv Heq1]]]].
    assert (Hcd1 : c `notin` dom Θ1) by exact Hbar.
    split.
    { destruct Hb as [-> | [[Qb ->] | [Qb ->]]];
        [ apply a_isub_cons_tvar; auto
        | apply a_isub_cons_var_typ; auto;
          apply a_wf_aenv_var_typ_inv in Hwf; destruct Hwf as [_ [HQwf _]];
          eapply a_wf_ptyp_lc; exact HQwf
        | apply a_isub_cons_var_skl; auto;
          apply a_wf_aenv_var_skl_inv in Hwf; destruct Hwf as [_ [HQwf _]];
          eapply a_scope_pskl_lc; exact (a_scope_pskl_of_wf HQwf) ]. }
    split.
    { destruct Hb as [-> | [[Qb ->] | [Qb ->]]].
      - apply a_wf_aenv__tvar; auto.
      - apply a_wf_aenv__var_typ; auto.
        apply a_wf_ptyp_isub with (Θ := Θ0); auto.
        apply a_wf_aenv_var_typ_inv in Hwf; tauto.
      - apply a_wf_aenv__var; auto.
        apply a_wf_pskl_isub with (Θ := Θ0); auto.
        apply a_wf_aenv_var_skl_inv in Hwf; tauto. }
    split; [ simpl; clear - Hdom; fsetdec | ].
    split.
    { intros Δ Hnd Hfa Hcov.
      destruct (Hinv Δ) as [Hnd1 [Hfa1 _]].
      { eapply no_flex_dep_tail; eauto. }
      { eapply faf_tail; eauto. }
      { intros α0 Hα0.
        assert (HXc := Hcov α0 ltac:(clear - Hα0; simpl; solve_notin_auto)).
        clear - HXc Hα0 Hbar. simpl in *. fsetdec. }
      split; [ | split ].
      - intros β' τ' Hb'.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb') as [[? Heq] | Hb''];
          [ | exact (Hnd1 β' τ' Hb'') ].
        exfalso.
        destruct Hb as [Hb2 | [[Qb Hb2] | [Qb Hb2]]]; subst; congruence.
      - apply faf_cons; [ | exact Hfa1 ].
        intros Hnonrig. pose proof (faf_head Hfa Hnonrig) as Hhd.
        simpl in *; clear - Hcov Hhd; fsetdec.
      - intros α0 Hα0Δ HXd.
        repeat rewrite dom_app in *; simpl in *.
        clear - Hcov Hα0Δ HXd; fsetdec. }
    apply a_tyequiv_weaken_cons. exact Heq1.
  - (* C-Ghost *)
    intros Δ1 Δ2 Θ0 P0 Hint Hwf HwfP0 HwfP Hrig Hnfd Hfaf.
    split; [ apply a_isub_refl; try assumption; auto | ].
    split; [ exact Hwf | ].
    split; [ clear; fsetdec | ].
    split.
    { intros Δ Hnd Hfa _ _.
      split; [ exact Hnd | ]. split; [ exact Hfa | ].
      intros α0 _ Hα0; exact Hα0. }
    split.
    + exists (pskl_to_bskl_inh P0).
      split; [ apply bskl_to_pskl_pskl_to_bskl_inh | ].
      split.
      * apply ad_pat_consis__ghost; [ fsetdec ].
      * eapply ad_refine_syn_refl_inh_gen; exact HwfP0.
    + apply ad_refine_pskl__ghost; exact Hint.
  - (* C-Unit *)
    intros Δ1 Δ2 Θ0 Hwf HwfP0 HwfP Hrig Hnfd Hfaf.
    split; [ apply a_isub_refl; try assumption; auto | ].
    split; [ exact Hwf | ].
    split; [ clear; fsetdec | ].
    split.
    { intros Δ Hnd Hfa _ _.
      split; [ exact Hnd | ]. split; [ exact Hfa | ].
      intros α0 _ Hα0; exact Hα0. }
    split.
    + exists bskl_unit. split; [ reflexivity | ].
      split; [ apply ad_pat_consis__unit; fsetdec
             | apply ad_refine_syn__unit ].
    + apply ad_refine_pskl__unit.
  - (* C-Rigid *)
    intros Δ1 Δ2 Θ0 α Hbind Hwf HwfP0 HwfP Hrig Hnfd Hfaf.
    split; [ apply a_isub_refl; try assumption; auto | ].
    split; [ exact Hwf | ].
    split; [ clear; fsetdec | ].
    split.
    { intros Δ Hnd Hfa _ _.
      split; [ exact Hnd | ]. split; [ exact Hfa | ].
      intros α0 _ Hα0; exact Hα0. }
    split.
    + exists (bskl_var_f α). split; [ reflexivity | ].
      split.
      * apply ad_pat_consis__var; [ fsetdec | left; exact Hbind ].
      * apply ad_refine_syn__var.
    + apply ad_refine_pskl__var.
  - (* C-Arrow *)
    intros Δ1 Δ2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc1 IH1 Hc2 IH2
           Hwf HwfP0 HwfP Hrig Hnfd Hfaf.
    simpl in HwfP0, HwfP.
    inversion HwfP0 as [ | | Θa Δa P0a' P0b' HwfP0a HwfP0b | | | ]; subst.
    inversion HwfP as [ | | Θb Δb P1' P2' HwfP1 HwfP2 | | | ]; subst.
    assert (Hft12 : forall (R : atoms) α0, α0 `in` (Δ1 `union` Δ2) ->
              α0 `notin` dom Θ0 -> α0 `notin` R).
    { intros R α0 Hα0 HXd. exfalso. apply HXd.
      eapply binds_In. apply Hrig. exact Hα0. }
    assert (Hcov12 : forall (Θx : aenv), ((Δ1 `union` Δ2) ∩ dom Θx) [<=] dom Θ0).
    { intros Θx α0 Hα0.
      assert (Hα0' : α0 `in` (Δ1 `union` Δ2)) by (clear - Hα0; fsetdec).
      apply Hrig in Hα0'. apply binds_In in Hα0'. exact Hα0'. }
    destruct (IH1 Hwf HwfP0a HwfP1 Hrig Hnfd Hfaf)
      as [Hle1 [Hwf1 [Hdom1 [Hinv1 [[Qt1 [HeQt1 [Hcons1 Hrs1]]] Hrp1]]]]].
    destruct (Hinv1 (Δ1 `union` Δ2) Hnfd Hfaf (Hcov12 _) (Hft12 _))
      as [Hnfd1 [Hfaf1 _]].
    assert (Hrig1 : forall α0, α0 `in` (Δ1 `union` Δ2) ->
              binds α0 abind_tvar Θ1)
      by (intros α0 Hα0; eapply a_isub_binds_tvar; eauto).
    destruct (IH2 Hwf1) as
        [Hle2 [Hwf2 [Hdom2 [Hinv2 [[Qt2 [HeQt2 [Hcons2 Hrs2]]] Hrp2]]]]];
      auto.
    { eapply a_wf_pskl_isub; eauto. }
    { eapply a_wf_pskl_isub; eauto. }
    split; [ eapply a_isub_trans; eauto | ].
    split; [ exact Hwf2 | ].
    split; [ clear - Hdom1 Hdom2; fsetdec | ].
    split.
    { intros Δ Hnd Hfa Hcov Hft.
      destruct (Hinv1 Δ Hnd Hfa ltac:(clear - Hcov Hdom2; solve_notin_auto))
        as [Hnd1' [Hfa1' _]].
      { intros α0 Hα0 HXd HXin. apply (Hft α0 Hα0 HXd).
        simpl. clear - HXin. fsetdec. }
      destruct (Hinv2 Δ Hnd1' Hfa1') as [Hnd2' [Hfa2' _]].
      { clear - Hcov Hdom1. fsetdec. }
      { intros α0 Hα0 HXd HXin.
        apply (Hft α0 Hα0).
        - intros HXin0. apply HXd. apply Hdom1. exact HXin0.
        - simpl. clear - HXin. fsetdec. }
      split; [ exact Hnd2' | ]. split; [ exact Hfa2' | ].
      intros α0 Hα0 HXd. clear - Hcov Hα0 HXd; fsetdec. }
    split.
    + exists (bskl_arrow Qt1 Qt2). split.
      { simpl. rewrite HeQt1, HeQt2. reflexivity. }
      split.
      * simpl. apply ad_pat_consis__arrow with (Ψ1 := empty) (Ψ2 := empty);
          [ eapply ad_pat_consis_isub; eauto | exact Hcons2 | fsetdec ].
      * simpl. apply ad_refine_syn_arrow_intro;
          [ eapply ad_refine_syn_isub; eauto | exact Hrs2 ].
    + simpl. apply ad_refine_pskl__arrow;
        [ eapply ad_refine_pskl_isub; eauto | exact Hrp2 ].
  - (* C-ForallInh : ∀α.P ∼ ∀α.P3 against input ∀α.P0 *)
    (* cluster 4: the opener is the RULE's now.  Two consequences — the wf
       judgments' cofinite bounds have no reason to avoid it (so instantiate
       them AT α with [a_wf_pskl_all_inv_at]), and the freshness facts the
       old [pick fresh] supplied must be REBUILT: the input-side ones from
       the rule's own side condition, [α ∉ dom Θ1] from the premise's output
       well-formedness, and [α ∉ ftv P3] for free, since the conclusion's
       output is [close α Q]. *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfrα Hprem0 IH Hwf HwfP0 HwfP Hrig Hnfd Hfaf.
    simpl in HwfP0, HwfP.
    assert (HαP0 : α `notin` ftvar_in_pskl P0) by (clear - Hfrα; fsetdec).
    assert (HαP : α `notin` ftvar_in_pskl P) by (clear - Hfrα; fsetdec).
    assert (HαΔ1 : α `notin` Δ1) by (clear - Hfrα; fsetdec).
    assert (HαΔ2 : α `notin` Δ2) by (clear - Hfrα; fsetdec).
    assert (HαΘ0 : α `notin` dom Θ0)
      by (pose proof (dom_subset_ftvar_in_aenv Θ0); clear - Hfrα H; fsetdec).
    remember (close_pskl_wrt_pskl α Q) as P3 eqn:HeqP3.
    assert (HαP3 : α `notin` ftvar_in_pskl P3)
      by (subst P3; rewrite ftvar_in_pskl_close_pskl_wrt_pskl;
          clear; fsetdec).
    assert (HQP3 : Q = open_pskl_wrt_pskl P3 (pskl_var_f α))
      by (subst P3; symmetry;
          apply open_pskl_wrt_pskl_close_pskl_wrt_pskl).
    rewrite HQP3 in Hprem0, IH.
    assert (Hpostα : consis_sound_post (add α Δ1) (add α Δ2)
                       ((α ~ abind_tvar) ++ Θ0)
                       (open_pskl_wrt_pskl P0 (pskl_var_f α))
                       (open_pskl_wrt_pskl P (pskl_var_f α))
                       (open_pskl_wrt_pskl P3 (pskl_var_f α))
                       ((α ~ abind_tvar) ++ Θ1)).
    { destruct (@delta_inv_open_tvar (Δ1 `union` Δ2) (add α Δ1 `union` add α Δ2) α Θ0) as (HΔr & HΔn & HΔf);
        [ auto | auto | clear; fsetdec | exact Hrig | auto | auto | ].
      apply IH.
      - apply a_wf_aenv__tvar; [ exact HαΘ0 | exact Hwf ].
      - eapply a_wf_pskl_delta_mono;
          [ apply (a_wf_pskl_all_inv_at HwfP0 HαP0)
          | intros γ _ Hγ; clear - Hγ; fsetdec ].
      - eapply a_wf_pskl_delta_mono;
          [ apply (a_wf_pskl_all_inv_at HwfP HαP)
          | intros γ _ Hγ; clear - Hγ; fsetdec ].
      - exact HΔr.
      - exact HΔn.
      - exact HΔf. }
    destruct Hpostα
      as [Hleα [Hwfα [Hdomα [Hinvα [[Qtα [HeQtα [Hconsα Hrsα]]] Hrpα]]]]].
    assert (Hwf1 : {{ ⊢ Θ1 }}a)
      by (apply a_wf_aenv_tvar_inv in Hwfα; tauto).
    assert (Hα1 : α `notin` dom Θ1)
      by (apply a_wf_aenv_tvar_inv in Hwfα; tauto).
    assert (Fr : α `notin` (dom Θ0 `union` dom Θ1 `union` ftvar_in_pskl P0
                  `union` ftvar_in_pskl P `union` ftvar_in_pskl P3
                  `union` Δ1 `union` Δ2))
      by (clear - HαΘ0 Hα1 HαP0 HαP HαP3 HαΔ1 HαΔ2; fsetdec).
    split; [ eapply a_isub_strip_tvar; eauto | ].
    split; [ exact Hwf1 | ].
    split.
    { eapply dom_sub_strip_tvar;
        [ clear - Fr; solve_notin_auto | exact Hdomα ]. }
    split.
    { eapply sound_invariants_strip_tvar; [ | exact Hinvα ].
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                    P0 (pskl_var_f α)) as Hopen0.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                    P (pskl_var_f α)) as Hopen1.
      simpl in *; clear - Hopen0 Hopen1; fsetdec. }
    split.
    + exists (bskl_all_inh (close_bskl_wrt_bskl α Qtα)). split.
      { simpl. rewrite bskl_to_pskl_close. rewrite HeQtα.
        rewrite close_pskl_wrt_pskl_open_pskl_wrt_pskl;
          [ reflexivity | clear - Fr; solve_notin_auto ]. }
      split.
      * simpl. apply ad_pat_consis__forall_inh_untagged
          with (L := dom Θ1 `union` singleton α `union` ftvar_in_pskl P).
        intros α0 Hα0. eapply ad_pat_consis_close_open;
          [exact Hwf1 | exact Hα1 | | ].
        -- rewrite ftvar_in_uskl_pskl. clear - Fr; solve_notin_auto.
        -- rewrite <- pskl_to_uskl_open_var. exact Hconsα.
      * change (pskl_to_bskl_inh (pskl_all_syn P0))
          with (bskl_all_inh (pskl_to_bskl_inh P0)).
        eapply ad_refine_syn_close_all with (α := α);
          [exact Hwf1 | exact Hα1 | clear - Fr; solve_notin_auto | exact Hrsα].
    + simpl. eapply ad_refine_pskl_close_all with (α := α);
        [exact Hwf1 | exact Hα1 | | ].
      * clear - Fr; solve_notin_auto.
      * exact Hrpα.
  - (* C-ForallSyn : ∀α.P ∼ ∀α.P3 against input ∀◇P0 *)
    (* cluster 4: exists-fresh opener — see C-ForallInh for the pattern *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfrα Hprem0 IH Hwf HwfP0 HwfP Hrig Hnfd Hfaf.
    simpl in HwfP0, HwfP.
    inversion HwfP0 as [ | | | | | Θc Δc P0c Hg0 Hwf0c Heqc ]; subst.
    try rewrite aenv_minus_empty in *.
    assert (HαP0 : α `notin` ftvar_in_pskl P0) by (clear - Hfrα; fsetdec).
    assert (HαP : α `notin` ftvar_in_pskl P) by (clear - Hfrα; fsetdec).
    assert (HαΔ1 : α `notin` Δ1) by (clear - Hfrα; fsetdec).
    assert (HαΔ2 : α `notin` Δ2) by (clear - Hfrα; fsetdec).
    assert (HαΘ0 : α `notin` dom Θ0)
      by (pose proof (dom_subset_ftvar_in_aenv Θ0); clear - Hfrα H; fsetdec).
    remember (close_pskl_wrt_pskl α Q) as P3 eqn:HeqP3.
    assert (HαP3 : α `notin` ftvar_in_pskl P3)
      by (subst P3; rewrite ftvar_in_pskl_close_pskl_wrt_pskl;
          clear; fsetdec).
    assert (HQP3 : Q = open_pskl_wrt_pskl P3 (pskl_var_f α))
      by (subst P3; symmetry;
          apply open_pskl_wrt_pskl_close_pskl_wrt_pskl).
    rewrite HQP3 in Hprem0, IH.
    assert (Hpostα : consis_sound_post Δ1 (add α Δ2)
                       ((α ~ abind_tvar) ++ Θ0)
                       (pskl_univ_ghost P0)
                       (open_pskl_wrt_pskl P (pskl_var_f α))
                       (open_pskl_wrt_pskl P3 (pskl_var_f α))
                       ((α ~ abind_tvar) ++ Θ1)).
    { destruct (@delta_inv_open_tvar (Δ1 `union` Δ2) (Δ1 `union` add α Δ2) α Θ0) as (HΔr & HΔn & HΔf);
        [ auto | auto | clear; fsetdec | exact Hrig | auto | auto | ].
      apply IH.
      - apply a_wf_aenv__tvar; [ exact HαΘ0 | exact Hwf ].
      - apply a_wf_pskl__univ_ghost; auto; rewrite aenv_minus_empty.
        eapply a_wf_pskl_weaken; [ | exact Hwf0c ].
        intros y b Hb. unfold binds; right; exact Hb.
      - eapply a_wf_pskl_delta_mono;
          [ apply (a_wf_pskl_all_inv_at HwfP HαP)
          | intros γ _ Hγ; clear - Hγ; fsetdec ].
      - exact HΔr.
      - exact HΔn.
      - exact HΔf. }
    destruct Hpostα
      as [Hleα [Hwfα [Hdomα [Hinvα [[Qtα [HeQtα [Hconsα Hrsα]]] Hrpα]]]]].
    assert (Hwf1 : {{ ⊢ Θ1 }}a)
      by (apply a_wf_aenv_tvar_inv in Hwfα; tauto).
    assert (Hα1 : α `notin` dom Θ1)
      by (apply a_wf_aenv_tvar_inv in Hwfα; tauto).
    assert (Fr : α `notin` (dom Θ0 `union` dom Θ1 `union` ftvar_in_pskl P0
                  `union` ftvar_in_pskl P `union` ftvar_in_pskl P3
                  `union` Δ1 `union` Δ2))
      by (clear - HαΘ0 Hα1 HαP0 HαP HαP3 HαΔ1 HαΔ2; fsetdec).
    split; [ eapply a_isub_strip_tvar; eauto | ].
    split; [ exact Hwf1 | ].
    split.
    { eapply dom_sub_strip_tvar;
        [ clear - Fr; solve_notin_auto | exact Hdomα ]. }
    split.
    { eapply sound_invariants_strip_tvar; [ | exact Hinvα ].
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                    P (pskl_var_f α)) as Hopen0.
      simpl in *; clear - Hopen0; fsetdec. }
    split.
    + exists (bskl_all_syn (close_bskl_wrt_bskl α Qtα)). split.
      { simpl. rewrite bskl_to_pskl_close. rewrite HeQtα.
        rewrite close_pskl_wrt_pskl_open_pskl_wrt_pskl;
          [ reflexivity | clear - Fr; solve_notin_auto ]. }
      split.
      * simpl. apply ad_pat_consis__forall_syn
          with (L := dom Θ1 `union` singleton α `union` ftvar_in_pskl P).
        intros α0 Hα0. eapply ad_pat_consis_close_open;
          [exact Hwf1 | exact Hα1 | | ].
        -- rewrite ftvar_in_uskl_pskl. clear - Fr; solve_notin_auto.
        -- rewrite <- pskl_to_uskl_open_var. exact Hconsα.
      * change (pskl_to_bskl_inh (pskl_univ_ghost P0))
          with (bskl_univ_ghost (pskl_to_bskl_inh P0)).
        eapply ad_refine_syn_close_univ_ghost with (α := α);
          [exact Hwf1 | exact Hα1 | clear - Fr; solve_notin_auto | exact Hrsα].
    + simpl. eapply ad_refine_pskl_close_all with (α := α);
        [exact Hwf1 | exact Hα1 | | ].
      * clear - Fr; solve_notin_auto.
      * exact Hrpα.
  - (* C-UnivGhost : ∀◇P ∼ ∀◇P3 against input ∀◇P0 *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P P3 Hc IHc Hwf HwfP0 HwfP Hrig Hnfd Hfaf.
    simpl in HwfP0, HwfP.
    inversion HwfP0 as [ | | | | | Θa Δa P0' Hg0 Hwf0' ]; subst.
    try rewrite aenv_minus_empty in *.
    inversion HwfP as [ | | | | | Θb Δb P' Hg' Hwf' ]; subst.
    try rewrite aenv_minus_empty in *.
    destruct (IHc Hwf) as
        [Hle [Hwf1 [Hdom [Hinv [[Qt [HeQt [Hcons Hrs]]] Hrp]]]]]; auto.
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    split; [ exact Hdom | ].
    split.
    { intros Δ Hnd Hfa Hcov Hft.
      apply (Hinv Δ Hnd Hfa Hcov).
      intros α0 Hα0 HXd. specialize (Hft α0 Hα0 HXd).
      simpl in Hft. exact Hft. }
    split.
    + exists (bskl_univ_ghost Qt). split.
      { simpl. rewrite HeQt. reflexivity. }
      split.
      * simpl. apply ad_pat_consis__univ_ghost. exact Hcons.
      * simpl. apply ad_refine_syn_univ_ghost_keep_intro; exact Hrs.
    + simpl. apply ad_refine_pskl__univ_ghost_keep; exact Hrp.
  - (* C-UnivGhost1 : ∀◇P ∼ ∀α.P3 against input ∀α.P0 *)
    (* cluster 4: exists-fresh opener — see C-ForallInh for the pattern *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfrα Hprem0 IH Hwf HwfP0 HwfP Hrig Hnfd Hfaf.
    simpl in HwfP0, HwfP.
    inversion HwfP as [ | | | | | Θc Δc Pc Hg' Hwf' Heqc ]; subst.
    try rewrite aenv_minus_empty in *.
    assert (HαP0 : α `notin` ftvar_in_pskl P0) by (clear - Hfrα; fsetdec).
    assert (HαP : α `notin` ftvar_in_pskl P) by (clear - Hfrα; fsetdec).
    assert (HαΔ1 : α `notin` Δ1) by (clear - Hfrα; fsetdec).
    assert (HαΔ2 : α `notin` Δ2) by (clear - Hfrα; fsetdec).
    assert (HαΘ0 : α `notin` dom Θ0)
      by (pose proof (dom_subset_ftvar_in_aenv Θ0); clear - Hfrα H; fsetdec).
    remember (close_pskl_wrt_pskl α Q) as P3 eqn:HeqP3.
    assert (HαP3 : α `notin` ftvar_in_pskl P3)
      by (subst P3; rewrite ftvar_in_pskl_close_pskl_wrt_pskl;
          clear; fsetdec).
    assert (HQP3 : Q = open_pskl_wrt_pskl P3 (pskl_var_f α))
      by (subst P3; symmetry;
          apply open_pskl_wrt_pskl_close_pskl_wrt_pskl).
    rewrite HQP3 in Hprem0, IH.
    assert (Hpostα : consis_sound_post (add α Δ1) Δ2
                       ((α ~ abind_tvar) ++ Θ0)
                       (open_pskl_wrt_pskl P0 (pskl_var_f α))
                       (pskl_univ_ghost P)
                       (open_pskl_wrt_pskl P3 (pskl_var_f α))
                       ((α ~ abind_tvar) ++ Θ1)).
    { destruct (@delta_inv_open_tvar (Δ1 `union` Δ2) (add α Δ1 `union` Δ2) α Θ0) as (HΔr & HΔn & HΔf);
        [ auto | auto | clear; fsetdec | exact Hrig | auto | auto | ].
      apply IH.
      - apply a_wf_aenv__tvar; [ exact HαΘ0 | exact Hwf ].
      - eapply a_wf_pskl_delta_mono;
          [ apply (a_wf_pskl_all_inv_at HwfP0 HαP0)
          | intros γ _ Hγ; clear - Hγ; fsetdec ].
      - apply a_wf_pskl__univ_ghost; auto; rewrite aenv_minus_empty.
        eapply a_wf_pskl_weaken; [ | exact Hwf' ].
        intros y b Hb. unfold binds; right; exact Hb.
      - exact HΔr.
      - exact HΔn.
      - exact HΔf. }
    destruct Hpostα
      as [Hleα [Hwfα [Hdomα [Hinvα [[Qtα [HeQtα [Hconsα Hrsα]]] Hrpα]]]]].
    assert (Hwf1 : {{ ⊢ Θ1 }}a)
      by (apply a_wf_aenv_tvar_inv in Hwfα; tauto).
    assert (Hα1 : α `notin` dom Θ1)
      by (apply a_wf_aenv_tvar_inv in Hwfα; tauto).
    assert (Fr : α `notin` (dom Θ0 `union` dom Θ1 `union` ftvar_in_pskl P0
                  `union` ftvar_in_pskl P `union` ftvar_in_pskl P3
                  `union` Δ1 `union` Δ2))
      by (clear - HαΘ0 Hα1 HαP0 HαP HαP3 HαΔ1 HαΔ2; fsetdec).
    pose proof (a_wf_aenv_def_ftv_notin Hwf1 Hα1) as Hdefsα.
    split; [ eapply a_isub_strip_tvar; eauto | ].
    split; [ exact Hwf1 | ].
    split.
    { eapply dom_sub_strip_tvar;
        [ clear - Fr; solve_notin_auto | exact Hdomα ]. }
    split.
    { eapply sound_invariants_strip_tvar; [ | exact Hinvα ].
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                    P0 (pskl_var_f α)) as Hopen0.
      simpl in *; clear - Hopen0; fsetdec. }
    split.
    + exists (bskl_all_inh (close_bskl_wrt_bskl α Qtα)). split.
      { simpl. rewrite bskl_to_pskl_close. rewrite HeQtα.
        rewrite close_pskl_wrt_pskl_open_pskl_wrt_pskl;
          [ reflexivity | clear - Fr; solve_notin_auto ]. }
      split.
      * simpl. apply ad_pat_consis__univ_ghost_inh
          with (L := dom Θ1 `union` singleton α `union` ftvar_in_pskl P).
        intros α0 Hα0.
        rewrite <- (subst_bskl_in_bskl_spec Qtα (bskl_var_f α0) α).
        replace (uskl_univ_ghost (pskl_to_uskl P))
          with (subst_uskl_in_uskl (uskl_var_f α0) α
                  (uskl_univ_ghost (pskl_to_uskl P)))
          by (simpl; rewrite subst_uskl_in_uskl_fresh_eq;
              [ reflexivity
              | rewrite ftvar_in_uskl_pskl; clear - Fr; solve_notin_auto ]).
        change ((α0 ~ abind_tvar) ++ Θ1)
          with (nil ++ (α0 ~ abind_tvar) ++ Θ1).
        eapply ad_pat_consis_rename_tvar;
          [ | exact Hα1 | exact Hdefsα ].
        exact Hconsα.
      * change (pskl_to_bskl_inh (pskl_all_syn P0))
          with (bskl_all_inh (pskl_to_bskl_inh P0)).
        eapply ad_refine_syn_close_all with (α := α);
          [exact Hwf1 | exact Hα1 | clear - Fr; solve_notin_auto | exact Hrsα].
    + apply ad_refine_pskl__univ_ghost_fill
        with (L := dom Θ1 `union` singleton α
                   `union` ftvar_in_pskl P `union` ftvar_in_pskl P3
                   `union` Δ1 `union` Δ2).
      intros α0 Hα0.
      rewrite (subst_pskl_in_pskl_intro α P3 (pskl_var_f α0));
        [ | clear - Fr; solve_notin_auto ].
      replace (pskl_univ_ghost P)
        with (subst_pskl_in_pskl (pskl_var_f α0) α (pskl_univ_ghost P))
        by (simpl; rewrite subst_pskl_in_pskl_fresh_eq;
            [ reflexivity | clear - Fr; solve_notin_auto ]).
      eapply ad_refine_pskl_rename_ctx_gen with (Θ1 := nil);
        [ change (nil ++ (α ~ abind_tvar) ++ Θ1)
            with ((α ~ abind_tvar) ++ Θ1); exact Hrpα
        | simpl; exact Hα1 | exact Hdefsα | clear - Hα0; fsetdec ].
  - (* C-UnivGhost2 *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P P3 Hg Hnf Hc IHc Hwf HwfP0 HwfP Hrig Hnfd Hfaf.
    simpl in HwfP.
    inversion HwfP as [ | | | | | Θb Δb P' Hg' Hwf' ]; subst.
    try rewrite aenv_minus_empty in *.
    destruct (IHc Hwf) as
        [Hle [Hwf1 [Hdom [Hinv [[Qt [HeQt [Hcons Hrs]]] Hrp]]]]]; auto.
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    split; [ exact Hdom | ].
    split.
    { intros Δ Hnd Hfa Hcov Hft.
      apply (Hinv Δ Hnd Hfa Hcov).
      intros α0 Hα0 HXd. specialize (Hft α0 Hα0 HXd).
      simpl in Hft. exact Hft. }
    split.
    + exists Qt. split; [ exact HeQt | ].
      split;
        [ simpl; apply ad_pat_consis__univ_ghost_drop; exact Hcons | exact Hrs ].
    + simpl. apply ad_refine_pskl__univ_ghost_remove. exact Hrp.
  - (* C-Flex : the mutual case — subjects equated by unification *)
    intros Δ1 Δ2 Θ0 Θ1 α β Hu IHu Hwf HwfP0 HwfP Hrig Hnfd Hfaf.
    pose proof (IHu Hwf) as Hpost.
    destruct (unify_sound_flex_out Hwf Hu Hpost Hrig Hnfd Hfaf)
      as [_ [_ Hout]].
    destruct Hpost as [Hle [Hwf1 [Hdom [Hinv _]]]].
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    split; [ exact Hdom | ].
    split.
    { intros Δ Hnd Hfa Hcov _. apply Hinv; auto. }
    apply Hout. reflexivity.
  - (* C-FlexL : assign α̂ := P0 (the input skeleton).  MUTUAL case: the
       [a_assign] premise is handled by the bundle's ASSIGN motive. *)
    intros Δ1 Δ2 Θ0 Θ1 α P0 Hnf Hnhole Hassign IHassign Hwf HwfP0 HwfP Hrig Hnfd Hfaf.
    pose proof (IHassign a_decls__nil Hwf HwfP0) as Hpost.
    destruct (assign_sound_flex_frame Hpost (a_assign_subject_flex Hassign)
                Hrig Hnfd Hfaf) as [HαnΔ [Hbα1 [Hnfd1 _]]].
    pose proof Hpost as [Hle [Hwf1 [Hdom [_ Hcons]]]].
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    split; [ exact Hdom | ].
    split.
    { apply (@assign_sound_consis_inv _ _ _ _ _ _ Hpost). clear. fsetdec. }
    apply (@consis_sound_flex_l_out _ _ _ _ _ _ Hcons Hwf1 HαnΔ Hbα1 Hnfd1).
    reflexivity.
  - (* C-FlexR : assign α̂ := P (the subject skeleton), output var α̂.
       MUTUAL case: the [a_assign] premise is the bundle's ASSIGN motive. *)
    intros Δ1 Δ2 Θ0 Θ1 α P Hnf Hnhole Hassign IHassign Hwf HwfP0 HwfP Hrig Hnfd Hfaf.
    pose proof (IHassign a_decls__nil Hwf HwfP) as Hpost.
    destruct (assign_sound_flex_frame Hpost (a_assign_subject_flex Hassign)
                Hrig Hnfd Hfaf) as [HαnΔ [_ [Hnfd1 _]]].
    pose proof Hpost as [Hle [Hwf1 [Hdom [_ Hcons]]]].
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    split; [ exact Hdom | ].
    split.
    { apply (@assign_sound_consis_inv _ _ _ _ _ _ Hpost). clear. fsetdec. }
    apply (@consis_sound_flex_r_out _ _ _ _ _ _ Hcons Hwf1 HαnΔ Hnfd1).
    reflexivity.
  - (* C-GhostR *)
    intros Δ1 Δ2 Θ0 P Hint Hwf HwfP0 HwfP Hrig Hnfd Hfaf.
    split; [ apply a_isub_refl; try assumption; auto | ].
    split; [ exact Hwf | ].
    split; [ clear; fsetdec | ].
    split.
    { intros Δ Hnd Hfa _ _.
      split; [ exact Hnd | ]. split; [ exact Hfa | ].
      intros α0 _ Hα0; exact Hα0. }
    split.
    + exists (pskl_to_bskl_syn P).
      split; [ apply bskl_to_pskl_pskl_to_bskl_syn | ].
      split.
      * replace (pskl_to_bskl_syn P)
          with (pskl_to_bskl_syn (uskl_to_pskl (pskl_to_uskl P)))
          by (rewrite uskl_to_pskl_pskl_to_uskl; reflexivity).
        apply ad_pat_consis_refl_erase.
        { apply pskl_to_uskl_lc. eapply a_wf_pskl_lc; eauto. }
        { intros α0 Hα0. rewrite ftvar_in_uskl_pskl in Hα0.
          exact (a_wf_pskl_ftv_binds HwfP Hα0). }
      * replace (pskl_to_bskl_inh pskl_ghost) with bskl_ghost by reflexivity.
        apply ad_refine_syn__ghost; exact Hint.
    + eapply ad_refine_pskl_refl_gen; exact HwfP.
  - (* C-UnivGhostR *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P P3 Hg Hnf Hc IHc Hwf HwfP0 HwfP Hrig Hnfd Hfaf.
    simpl in HwfP0.
    inversion HwfP0 as [ | | | | | Θa Δa P0' Hg0 Hwf0' ]; subst.
    try rewrite aenv_minus_empty in *.
    destruct (IHc Hwf) as
        [Hle [Hwf1 [Hdom [Hinv [[Qt [HeQt [Hcons Hrs]]] Hrp]]]]]; auto.
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    split; [ exact Hdom | ].
    split.
    { intros Δ Hnd Hfa Hcov Hft.
      apply (Hinv Δ Hnd Hfa Hcov).
      intros α0 Hα0 HXd. specialize (Hft α0 Hα0 HXd).
      simpl in Hft. exact Hft. }
    split.
    + exists Qt. split; [ exact HeQt | ]. split; [ exact Hcons | ].
      apply ad_refine_syn_univ_ghost_remove_intro. exact Hrs.
    + exact Hrp.
Qed.

(* ===================================================================== *)
(*  The [a_assign] lemmas, RE-EXPORTED from the bundle under their         *)
(*  original names.  Each used to be a standalone induction; now that      *)
(*  Assign-Assign's premise is a CONSISTENCY derivation they are conjuncts *)
(*  of the bundle's ASSIGN motive.  The only change to their statements is *)
(*  the wf hypothesis (full [{{ _ ⨟ ∅ ⊢ₚₛ P }}a] instead of the old visibility     *)
(*  side condition) — every call site has it.                             *)
(* ===================================================================== *)

(** Soundness of assignment (thm:sound-consistency part 3):
    [Θ₀ | Ξ ⊲ α̂ ≔ P ⊣ Θ₁] gives [(Ξ ++ Θ₀) ⊴ Θ₁] and, declaratively, the
    assigned skeleton is consistent with the variable in [Θ₁]. *)
Lemma a_assign_sound : forall Θ0 Ξ α P Θ1,
  {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
  a_decls Ξ ->
  {{ ⊢ (Ξ ++ Θ0) }}a ->
  {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P }}a ->
  (Ξ ++ Θ0) ⊴ Θ1 /\
  ad_pat_consis empty Θ1 (pskl_to_uskl P) (bskl_var_f α).
Proof.
  intros * Ha Hdecl Hwf HwfP.
  destruct (proj1 a_assign_unify_consis_sound _ _ _ _ _ Ha Hdecl Hwf HwfP)
    as [Hle [_ [_ [_ Hcons]]]].
  split; assumption.
Qed.

(** [a_assign] preserves context well-formedness. *)
Lemma a_assign_preserves_wf : forall Θ0 Ξ α P Θ1,
  {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
  a_decls Ξ ->
  {{ ⊢ (Ξ ++ Θ0) }}a ->
  {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P }}a ->
  {{ ⊢ Θ1 }}a.
Proof.
  intros * Ha Hdecl Hwf HwfP.
  destruct (proj1 a_assign_unify_consis_sound _ _ _ _ _ Ha Hdecl Hwf HwfP)
    as [_ [Hwf1 _]]. exact Hwf1.
Qed.

(** Preservation of the problem invariants by assignment, at any protected Δ. *)
Lemma a_assign_preserves_inv : forall Θ0 Ξ α P Θ1 Δ,
  {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
  a_decls Ξ ->
  {{ ⊢ (Ξ ++ Θ0) }}a ->
  {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P }}a ->
  no_flex_dep Δ (Ξ ++ Θ0) ->
  flex_above_free Δ Θ0 ->
  Δ ∩ dom Ξ [=] empty ->
  Δ ∩ dom Θ1 [<=] dom (Ξ ++ Θ0) ->
  (forall α0, α0 `in` Δ -> α0 `notin` dom Θ0 -> α0 `notin` ftvar_in_pskl P) ->
  no_flex_dep Δ Θ1 /\
  flex_above_free Δ Θ1 /\
  (forall α0, α0 `in` Δ -> α0 `in` dom Θ1 -> α0 `in` (dom Ξ `union` dom Θ0)).
Proof.
  intros * Ha Hdecl Hwf HwfP.
  destruct (proj1 a_assign_unify_consis_sound _ _ _ _ _ Ha Hdecl Hwf HwfP)
    as [_ [_ [_ [Hinv _]]]]. apply (Hinv Δ).
Qed.

(** The subject of an assignment is bound (as a flexible or defined variable)
    in the output context.  NO induction: the increase conjunct transports the
    input flexibility of the subject ([a_assign_subject_flex]) forward. *)
Lemma a_assign_subject_binds : forall Θ0 Ξ α P Θ1,
  {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
  a_decls Ξ ->
  {{ ⊢ (Ξ ++ Θ0) }}a ->
  {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P }}a ->
  a_binds_tvar α Θ1.
Proof.
  intros * Ha Hdecl Hwf HwfP.
  destruct (a_assign_sound Ha Hdecl Hwf HwfP) as [Hle _].
  eapply a_isub_binds_tvarish; [ exact Hle | ].
  destruct (a_assign_subject_flex Ha) as [Hb | [τ Hb]];
    [ right; left | right; right; exists τ ]; exact Hb.
Qed.

(** Part 2, packaged (thm:sound-consistency part 2, paper reading). *)
Corollary a_unify_sound : forall Θ0 α β Θ1,
  {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a ->
  {{ ⊢ Θ0 }}a ->
  Θ0 ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\ ({{ Θ1 ⊢ (ptyp_var_f α) ≡ᵗ (ptyp_var_f β) }}a).
Proof.
  intros * Hu Hwf.
  destruct (proj1 (proj2 a_assign_unify_consis_sound) _ _ _ _ Hu Hwf)
    as [Hle [Hwf1 [_ [_ Heq]]]]; auto.
Qed.

(** Preservation of the part-1 problem invariants by unification, at any
    protected Δ (the shape [a_consistag_sound_aux]'s Flex case needs). *)
Corollary a_unify_preserves_inv : forall Θ0 α β Θ1 Δ,
  {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a ->
  {{ ⊢ Θ0 }}a ->
  no_flex_dep Δ Θ0 ->
  flex_above_free Δ Θ0 ->
  Δ ∩ dom Θ1 [<=] dom Θ0 ->
  no_flex_dep Δ Θ1 /\ flex_above_free Δ Θ1.
Proof.
  intros * Hu Hwf Hnd Hfa Hcov.
  destruct (proj1 (proj2 a_assign_unify_consis_sound) _ _ _ _ Hu Hwf)
    as [_ [_ [_ [Hinv _]]]].
  destruct (Hinv Δ Hnd Hfa Hcov) as [Hnd1 [Hfa1 _]]; auto.
Qed.

(* ===================================================================== *)
(*  Soundness of DECORATED consistency (lemma:sound-decorated-consistency) *)
(*  The parallel of [a_consis_sound_aux] over the tagged/decorated        *)
(*  algorithmic consistency judgment [a_consistag], threading the tag     *)
(*  context Ψ into the declarative consistency component.                 *)
(* ===================================================================== *)

(** Erasure preserves free variables. *)
Lemma ftvar_in_pskl_uskl_to_pskl : forall R,
  ftvar_in_pskl (uskl_to_pskl R) [=] ftvar_in_uskl R.
Proof. induction R; simpl; fsetdec. Qed.

(** The conclusion of [a_consistag_sound_aux], named so that its four
    binder rows (ForallInh / ForallSyn, each tagged and untagged) can share
    one argument per input shape: the tagged and untagged rows differ only
    in the declarative rule that re-binds the opened consistency. *)
Definition consistag_sound_post (Δ1 Δ2 : atoms) (P0 : pskl) (Ψ : atoms)
    (Θ0 : aenv) (R : uskl) (P' : pskl) (Θ1 : aenv) : Prop :=
  Θ0 ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\
  no_flex_dep (Δ1 `union` Δ2) Θ1 /\ flex_above_free (Δ1 `union` Δ2) Θ1 /\
  (exists Qt, bskl_to_pskl Qt = P' /\
     {{ Ψ ⨟ Θ1 ⊢ˢ R ∼ Qt }}ad /\
     {{ Θ1 ⨟ Δ1 ⊢ᵣ (pskl_to_bskl_inh P0) ⊳ Qt }}ad) /\
  {{ Θ1 ⨟ Δ2 ⊢ᵣₚ (uskl_to_pskl R) ⊳ P' }}ad.

(** Decorated ForallInh (either tag): input [∀α.P0], subject [Rall]
    erasing to [∀α.R]. *)
Lemma consistag_sound_forall_inh : forall L Δ1 Δ2 Ψ Ψ' Θ0 Θ1 P0 R Rall Q,
  (forall α, α `notin` L ->
     {{ ⊢ ((α ~ abind_tvar) ++ Θ0) }}a ->
     lc_uskl (open_uskl_wrt_uskl R (uskl_var_f α)) ->
     {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty
        ⊢ₚₛ (open_pskl_wrt_pskl P0 (pskl_var_f α)) }}a ->
     {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty
        ⊢ₚₛ (uskl_to_pskl (open_uskl_wrt_uskl R (uskl_var_f α))) }}a ->
     (forall α0, α0 `in` (add α Δ1 `union` add α Δ2) ->
        binds α0 abind_tvar ((α ~ abind_tvar) ++ Θ0)) ->
     no_flex_dep (add α Δ1 `union` add α Δ2) ((α ~ abind_tvar) ++ Θ0) ->
     flex_above_free (add α Δ1 `union` add α Δ2) ((α ~ abind_tvar) ++ Θ0) ->
     consistag_sound_post (add α Δ1) (add α Δ2)
       (open_pskl_wrt_pskl P0 (pskl_var_f α)) Ψ' ((α ~ abind_tvar) ++ Θ0)
       (open_uskl_wrt_uskl R (uskl_var_f α))
       (open_pskl_wrt_pskl Q (pskl_var_f α)) ((α ~ abind_tvar) ++ Θ1)) ->
  (forall Qb L',
     (forall α, α `notin` L' ->
        {{ Ψ' ⨟ ((α ~ abind_tvar) ++ Θ1) ⊢ˢ
          (open_uskl_wrt_uskl R (uskl_var_f α)) ∼
          (open_bskl_wrt_bskl Qb (bskl_var_f α)) }}ad) ->
     {{ Ψ ⨟ Θ1 ⊢ˢ Rall ∼ (bskl_all_inh Qb) }}ad) ->
  uskl_to_pskl Rall = pskl_all_syn (uskl_to_pskl R) ->
  {{ ⊢ Θ0 }}a ->
  (forall α, lc_uskl (open_uskl_wrt_uskl R (uskl_var_f α))) ->
  {{ Θ0 ⨟ empty ⊢ₚₛ (pskl_all_syn P0) }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ (pskl_all_syn (uskl_to_pskl R)) }}a ->
  (forall α0, α0 `in` (Δ1 `union` Δ2) -> binds α0 abind_tvar Θ0) ->
  no_flex_dep (Δ1 `union` Δ2) Θ0 -> flex_above_free (Δ1 `union` Δ2) Θ0 ->
  consistag_sound_post Δ1 Δ2 (pskl_all_syn P0) Ψ Θ0 Rall (pskl_all_syn Q) Θ1.
Proof.
  intros L Δ1 Δ2 Ψ Ψ' Θ0 Θ1 P0 R Rall Q IH Hbuild HRall Hwf HlcSbody
    HwfP0 HwfS Hrig Hnfd Hfaf.
  inversion HwfP0 as [ | | | L0 Θa Δa P0a Hbody0 Heqa | | ]; subst.
  inversion HwfS as [ | | | LS ΘbS ΔbS SbS HbodyS HeqS | | ]; subst.
  pick fresh α for
    (L `union` L0 `union` LS `union` dom Θ0 `union` dom Θ1
     `union` ftvar_in_pskl P0 `union` ftvar_in_uskl R `union` ftvar_in_pskl Q
     `union` Δ1 `union` Δ2).
  assert (HαL : α `notin` L) by auto.
  assert (HwfΘα : {{ ⊢ ((α ~ abind_tvar) ++ Θ0) }}a)
    by (apply a_wf_aenv__tvar; auto).
  assert (HwfP0α : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty
                     ⊢ₚₛ (open_pskl_wrt_pskl P0 (pskl_var_f α)) }}a).
  { eapply a_wf_pskl_delta_mono;
      [ apply Hbody0; auto
      | intros γ _ Hγ; clear - Hγ; fsetdec ]. }
  assert (HwfSα : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty
                 ⊢ₚₛ (uskl_to_pskl (open_uskl_wrt_uskl R (uskl_var_f α))) }}a).
  { rewrite uskl_to_pskl_open.
    eapply a_wf_pskl_delta_mono;
      [ apply HbodyS; auto
      | intros γ _ Hγ; clear - Hγ; fsetdec ]. }
  destruct (@delta_inv_open_tvar (Δ1 `union` Δ2) (add α Δ1 `union` add α Δ2) α Θ0) as (Hrigα & Hnfdα & Hfafα);
      [ auto | auto | clear; fsetdec | exact Hrig | auto | auto | ].
  destruct (IH α HαL HwfΘα (HlcSbody α) HwfP0α HwfSα Hrigα Hnfdα Hfafα)
    as [Hleα [Hwfα [Hnfdα1 [Hfafα1 [[Qtα [HeQtα [Hconsα Hrsα]]] Hrpα]]]]].
  assert (Hwf1 : {{ ⊢ Θ1 }}a)
    by (apply a_wf_aenv_tvar_inv in Hwfα; tauto).
  assert (Hα1 : α `notin` dom Θ1) by auto.
  split; [ eapply a_isub_strip_tvar; eauto | ].
  split; [ exact Hwf1 | ].
  split.
  { apply no_flex_dep_strip with (α := α).
    apply no_flex_dep_cong with (Δ := add α Δ1 `union` add α Δ2);
      [ clear; fsetdec | exact Hnfdα1 ]. }
  split.
  { apply faf_strip with (α := α).
    apply faf_cong with (Δ := add α Δ1 `union` add α Δ2);
      [ clear; fsetdec | exact Hfafα1 ]. }
  split.
  - exists (bskl_all_inh (close_bskl_wrt_bskl α Qtα)). split.
    { simpl. rewrite bskl_to_pskl_close. rewrite HeQtα.
      rewrite close_pskl_wrt_pskl_open_pskl_wrt_pskl;
        [ reflexivity | clear - Fr; solve_notin_auto ]. }
    split.
    + apply (Hbuild _ (dom Θ1 `union` singleton α `union` ftvar_in_uskl R)).
      intros α0 Hα0. eapply ad_pat_consis_close_open;
        [exact Hwf1 | exact Hα1 | | ].
      * clear - Fr; solve_notin_auto.
      * exact Hconsα.
    + change (pskl_to_bskl_inh (pskl_all_syn P0))
        with (bskl_all_inh (pskl_to_bskl_inh P0)).
      eapply ad_refine_syn_close_all with (α := α);
        [exact Hwf1 | exact Hα1 | clear - Fr; solve_notin_auto | exact Hrsα].
  - rewrite HRall. eapply ad_refine_pskl_close_all with (α := α);
      [exact Hwf1 | exact Hα1 | | ].
    + rewrite ftvar_in_pskl_uskl_to_pskl. clear - Fr; solve_notin_auto.
    + rewrite <- uskl_to_pskl_open. exact Hrpα.
Qed.

(** Decorated ForallSyn (either tag): input [∀◇P0], subject [Rall]
    erasing to [∀α.R]. *)
Lemma consistag_sound_forall_syn : forall L Δ1 Δ2 Ψ Ψ' Θ0 Θ1 P0 R Rall Q,
  (forall α, α `notin` L ->
     {{ ⊢ ((α ~ abind_tvar) ++ Θ0) }}a ->
     lc_uskl (open_uskl_wrt_uskl R (uskl_var_f α)) ->
     {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ (pskl_univ_ghost P0) }}a ->
     {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty
        ⊢ₚₛ (uskl_to_pskl (open_uskl_wrt_uskl R (uskl_var_f α))) }}a ->
     (forall α0, α0 `in` (Δ1 `union` add α Δ2) ->
        binds α0 abind_tvar ((α ~ abind_tvar) ++ Θ0)) ->
     no_flex_dep (Δ1 `union` add α Δ2) ((α ~ abind_tvar) ++ Θ0) ->
     flex_above_free (Δ1 `union` add α Δ2) ((α ~ abind_tvar) ++ Θ0) ->
     consistag_sound_post Δ1 (add α Δ2)
       (pskl_univ_ghost P0) Ψ' ((α ~ abind_tvar) ++ Θ0)
       (open_uskl_wrt_uskl R (uskl_var_f α))
       (open_pskl_wrt_pskl Q (pskl_var_f α)) ((α ~ abind_tvar) ++ Θ1)) ->
  (forall Qb L',
     (forall α, α `notin` L' ->
        {{ Ψ' ⨟ ((α ~ abind_tvar) ++ Θ1) ⊢ˢ
          (open_uskl_wrt_uskl R (uskl_var_f α)) ∼
          (open_bskl_wrt_bskl Qb (bskl_var_f α)) }}ad) ->
     {{ Ψ ⨟ Θ1 ⊢ˢ Rall ∼ (bskl_all_syn Qb) }}ad) ->
  uskl_to_pskl Rall = pskl_all_syn (uskl_to_pskl R) ->
  {{ ⊢ Θ0 }}a ->
  (forall α, lc_uskl (open_uskl_wrt_uskl R (uskl_var_f α))) ->
  {{ Θ0 ⨟ empty ⊢ₚₛ (pskl_univ_ghost P0) }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ (pskl_all_syn (uskl_to_pskl R)) }}a ->
  (forall α0, α0 `in` (Δ1 `union` Δ2) -> binds α0 abind_tvar Θ0) ->
  no_flex_dep (Δ1 `union` Δ2) Θ0 -> flex_above_free (Δ1 `union` Δ2) Θ0 ->
  consistag_sound_post Δ1 Δ2 (pskl_univ_ghost P0) Ψ Θ0 Rall
    (pskl_all_syn Q) Θ1.
Proof.
  intros L Δ1 Δ2 Ψ Ψ' Θ0 Θ1 P0 R Rall Q IH Hbuild HRall Hwf HlcSbody
    HwfP0 HwfS Hrig Hnfd Hfaf.
  inversion HwfP0 as [ | | | | | Θc Δc P0c Hg0 Hwf0c Heqc ]; subst.
  try rewrite aenv_minus_empty in *.
  inversion HwfS as [ | | | LS ΘbS ΔbS SbS HbodyS HeqS | | ]; subst.
  pick fresh α for
    (L `union` LS `union` dom Θ0 `union` dom Θ1
     `union` ftvar_in_pskl P0 `union` ftvar_in_uskl R `union` ftvar_in_pskl Q
     `union` Δ1 `union` Δ2).
  assert (HαL : α `notin` L) by auto.
  assert (HwfΘα : {{ ⊢ ((α ~ abind_tvar) ++ Θ0) }}a)
    by (apply a_wf_aenv__tvar; auto).
  assert (HwfP0α : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty
                     ⊢ₚₛ (pskl_univ_ghost P0) }}a).
  { apply a_wf_pskl__univ_ghost; auto; rewrite aenv_minus_empty.
    eapply a_wf_pskl_weaken; [ | exact Hwf0c ].
    intros y b Hb. unfold binds; right; exact Hb. }
  assert (HwfSα : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty
                 ⊢ₚₛ (uskl_to_pskl (open_uskl_wrt_uskl R (uskl_var_f α))) }}a).
  { rewrite uskl_to_pskl_open.
    eapply a_wf_pskl_delta_mono;
      [ apply HbodyS; auto
      | intros γ _ Hγ; clear - Hγ; fsetdec ]. }
  destruct (@delta_inv_open_tvar (Δ1 `union` Δ2) (Δ1 `union` add α Δ2) α Θ0) as (Hrigα & Hnfdα & Hfafα);
      [ auto | auto | clear; fsetdec | exact Hrig | auto | auto | ].
  destruct (IH α HαL HwfΘα (HlcSbody α) HwfP0α HwfSα Hrigα Hnfdα Hfafα)
    as [Hleα [Hwfα [Hnfdα1 [Hfafα1 [[Qtα [HeQtα [Hconsα Hrsα]]] Hrpα]]]]].
  assert (Hwf1 : {{ ⊢ Θ1 }}a)
    by (apply a_wf_aenv_tvar_inv in Hwfα; tauto).
  assert (Hα1 : α `notin` dom Θ1) by auto.
  split; [ eapply a_isub_strip_tvar; eauto | ].
  split; [ exact Hwf1 | ].
  split.
  { apply no_flex_dep_strip with (α := α).
    apply no_flex_dep_cong with (Δ := Δ1 `union` add α Δ2);
      [ clear; fsetdec | exact Hnfdα1 ]. }
  split.
  { apply faf_strip with (α := α).
    apply faf_cong with (Δ := Δ1 `union` add α Δ2);
      [ clear; fsetdec | exact Hfafα1 ]. }
  split.
  - exists (bskl_all_syn (close_bskl_wrt_bskl α Qtα)). split.
    { simpl. rewrite bskl_to_pskl_close. rewrite HeQtα.
      rewrite close_pskl_wrt_pskl_open_pskl_wrt_pskl;
        [ reflexivity | clear - Fr; solve_notin_auto ]. }
    split.
    + apply (Hbuild _ (dom Θ1 `union` singleton α `union` ftvar_in_uskl R)).
      intros α0 Hα0. eapply ad_pat_consis_close_open;
        [exact Hwf1 | exact Hα1 | | ].
      * clear - Fr; solve_notin_auto.
      * exact Hconsα.
    + change (pskl_to_bskl_inh (pskl_univ_ghost P0))
        with (bskl_univ_ghost (pskl_to_bskl_inh P0)).
      eapply ad_refine_syn_close_univ_ghost with (α := α);
        [exact Hwf1 | exact Hα1 | clear - Fr; solve_notin_auto | exact Hrsα].
  - rewrite HRall. eapply ad_refine_pskl_close_all with (α := α);
      [exact Hwf1 | exact Hα1 | | ].
    + rewrite ftvar_in_pskl_uskl_to_pskl. clear - Fr; solve_notin_auto.
    + rewrite <- uskl_to_pskl_open. exact Hrpα.
Qed.

Lemma a_consistag_sound_aux : forall Δ1 Δ2 P0 Ψ Θ0 R P' Θ1,
  {{ Θ0 ⊢[ Δ1 | Δ2 | P0 | Ψ ] R ∼ P' ⊣ Θ1 }}da ->
  {{ ⊢ Θ0 }}a ->
  lc_uskl R ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ (uskl_to_pskl R) }}a ->
  (forall α0, α0 `in` (Δ1 `union` Δ2) -> binds α0 abind_tvar Θ0) ->
  no_flex_dep (Δ1 `union` Δ2) Θ0 -> flex_above_free (Δ1 `union` Δ2) Θ0 ->
  Θ0 ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\
  no_flex_dep (Δ1 `union` Δ2) Θ1 /\ flex_above_free (Δ1 `union` Δ2) Θ1 /\
  (exists Qt, bskl_to_pskl Qt = P' /\
     {{ Ψ ⨟ Θ1 ⊢ˢ R ∼ Qt }}ad /\
     {{ Θ1 ⨟ Δ1 ⊢ᵣ (pskl_to_bskl_inh P0) ⊳ Qt }}ad) /\
  {{ Θ1 ⨟ Δ2 ⊢ᵣₚ (uskl_to_pskl R) ⊳ P' }}ad.
Proof.
  intros * Hc Hwf HlcS HwfP0 HwfS Hrig Hnfd Hfaf.
  revert Hwf HlcS HwfP0 HwfS Hrig Hnfd Hfaf.
  induction Hc; intros Hwf HlcS HwfP0 HwfS Hrig Hnfd Hfaf.
  - (* Ghost *)
    split; [ apply a_isub_refl; try assumption; auto | ].
    split; [ exact Hwf | ]. split; [ exact Hnfd | ]. split; [ exact Hfaf | ].
    split.
    + exists (pskl_to_bskl_inh P0).
      split; [ apply bskl_to_pskl_pskl_to_bskl_inh | ].
      split.
      * apply ad_pat_consis__ghost; [ fsetdec ].
      * eapply ad_refine_syn_refl_inh_gen; exact HwfP0.
    + apply ad_refine_pskl__ghost; exact H.
  - (* Unit *)
    split; [ apply a_isub_refl; try assumption; auto | ].
    split; [ exact Hwf | ]. split; [ exact Hnfd | ]. split; [ exact Hfaf | ].
    split.
    + exists bskl_unit. split; [ reflexivity | ].
      split; [ apply ad_pat_consis__unit; fsetdec | apply ad_refine_syn__unit ].
    + apply ad_refine_pskl__unit.
  - (* Rigid *)
    split; [ apply a_isub_refl; try assumption; auto | ].
    split; [ exact Hwf | ]. split; [ exact Hnfd | ]. split; [ exact Hfaf | ].
    split.
    + exists (bskl_var_f α). split; [ reflexivity | ].
      split.
      * apply ad_pat_consis__var; [ fsetdec | left; exact H ].
      * apply ad_refine_syn__var.
    + apply ad_refine_pskl__var.
  - (* Flex : decorated — through the mutual soundness bundle *)
    pose proof (proj1 (proj2 a_assign_unify_consis_sound) _ _ _ _ H Hwf)
      as Hpost.
    destruct (unify_sound_flex_out Hwf H Hpost Hrig Hnfd Hfaf)
      as [Hnfd1 [Hfaf1 Hout]].
    destruct Hpost as [Hle [Hwf1 _]].
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    split; [ exact Hnfd1 | ]. split; [ exact Hfaf1 | ].
    exact (Hout Ψ H0).
  - (* FlexL : decorated *)
    pose proof (proj1 a_assign_unify_consis_sound _ _ _ _ _ H1
                  a_decls__nil Hwf HwfP0) as Hpost.
    destruct (assign_sound_flex_frame Hpost (a_assign_subject_flex H1)
                Hrig Hnfd Hfaf) as [HαnΔ [Hbα1 [Hnfd1 Hfaf1]]].
    destruct Hpost as [Hle [Hwf1 [_ [_ Hcons]]]].
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    split; [ exact Hnfd1 | ]. split; [ exact Hfaf1 | ].
    exact (@consis_sound_flex_l_out _ _ _ _ _ _
             Hcons Hwf1 HαnΔ Hbα1 Hnfd1 H2).
  - (* FlexR : decorated (subject [pskl_to_uskl P], mirrors ordinary FlexR) *)
    rewrite uskl_to_pskl_pskl_to_uskl in HwfS |- *.
    pose proof (proj1 a_assign_unify_consis_sound _ _ _ _ _ H1
                  a_decls__nil Hwf HwfS) as Hpost.
    destruct (assign_sound_flex_frame Hpost (a_assign_subject_flex H1)
                Hrig Hnfd Hfaf) as [HαnΔ [_ [Hnfd1 Hfaf1]]].
    destruct Hpost as [Hle [Hwf1 [_ [_ Hcons]]]].
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    split; [ exact Hnfd1 | ]. split; [ exact Hfaf1 | ].
    exact (@consis_sound_flex_r_out _ _ _ _ _ _ Hcons Hwf1 HαnΔ Hnfd1 H2).
  - (* GhostG *)
    split; [ apply a_isub_refl; try assumption; auto | ].
    split; [ exact Hwf | ]. split; [ exact Hnfd | ]. split; [ exact Hfaf | ].
    split.
    + exists bskl_ghost. split; [ reflexivity | ].
      split.
      * apply ad_pat_consis__ghostg. fsetdec.
      * replace (@bskl_ghost) with (pskl_to_bskl_syn pskl_ghost) by reflexivity.
        apply ad_refine_syn__ghost; simpl; fsetdec.
    + apply ad_refine_pskl__ghost; simpl; fsetdec.
  - (* Arrow *)
    simpl in HwfP0, HwfS. inversion HlcS; subst.
    inversion HwfP0 as [ | | Θa Δa P0a' P0b' HwfP0a HwfP0b | | | ]; subst.
    inversion HwfS as [ | | Θb Δb S1p S2p HwfS1 HwfS2 | | | ]; subst.
    destruct IHHc1
      as [Hle1 [Hwf1 [Hnfd1 [Hfaf1 [[Qt1 [HeQt1 [Hcons1 Hrs1]]] Hrp1]]]]]; auto.
    destruct IHHc2
      as [Hle2 [Hwf2 [Hnfd2 [Hfaf2 [[Qt2 [HeQt2 [Hcons2 Hrs2]]] Hrp2]]]]]; auto.
    { eapply a_wf_pskl_isub; eauto. }
    { eapply a_wf_pskl_isub; eauto. }
    { intros α0 Hα0. eapply a_isub_binds_tvar; eauto. }
    split; [ eapply a_isub_trans; eauto | ].
    split; [ exact Hwf2 | ]. split; [ exact Hnfd2 | ]. split; [ exact Hfaf2 | ].
    split.
    + exists (bskl_arrow Qt1 Qt2). split.
      { simpl. rewrite HeQt1, HeQt2. reflexivity. }
      split.
      * simpl. apply ad_pat_consis__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
          [ eapply ad_pat_consis_isub; eauto | exact Hcons2 | exact H ].
      * simpl. apply ad_refine_syn_arrow_intro;
          [ eapply ad_refine_syn_isub; eauto | exact Hrs2 ].
    + simpl. apply ad_refine_pskl__arrow;
        [ eapply ad_refine_pskl_isub; eauto | exact Hrp2 ].
  - (* ForallInh tagged : decorated *)
    inversion HlcS; subst.
    eapply consistag_sound_forall_inh with (R := R); eauto.
    intros Qb L' Hb. eapply ad_pat_consis__forall_inh_tagged; eauto.
  - (* ForallInh untagged : decorated *)
    inversion HlcS; subst.
    eapply consistag_sound_forall_inh with (R := R); eauto.
    intros Qb L' Hb. eapply ad_pat_consis__forall_inh_untagged; eauto.
  - (* ForallSyn tagged : decorated *)
    inversion HlcS; subst.
    eapply consistag_sound_forall_syn with (R := R); eauto.
    intros Qb L' Hb. eapply ad_pat_consis__forall_syn_tagged; eauto.
  - (* ForallSyn untagged : decorated *)
    inversion HlcS; subst.
    eapply consistag_sound_forall_syn with (R := R); eauto.
    intros Qb L' Hb. eapply ad_pat_consis__forall_syn; eauto.
  - (* UnivGhost *)
    simpl in HwfP0, HwfS.
    inversion HlcS; subst.
    inversion HwfP0 as [ | | | | | Θa Δa P0' Hg0 Hwf0' Heqa ]; subst.
    try rewrite aenv_minus_empty in *.
    inversion HwfS as [ | | | | | Θb Δb Rp Hgs Hwfs Heqb ]; subst.
    try rewrite aenv_minus_empty in *.
    destruct IHHc
      as [Hle [Hwf1 [Hnfd1 [Hfaf1 [[Qt [HeQt [Hcons Hrs]]] Hrp]]]]]; auto.
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    split; [ exact Hnfd1 | ]. split; [ exact Hfaf1 | ].
    split.
    + exists (bskl_univ_ghost Qt). split.
      { simpl. rewrite HeQt. reflexivity. }
      split.
      * simpl. apply ad_pat_consis__univ_ghost. exact Hcons.
      * simpl. apply ad_refine_syn_univ_ghost_keep_intro; exact Hrs.
    + simpl. apply ad_refine_pskl__univ_ghost_keep; exact Hrp.
  - (* UnivGhostG *)
    simpl in HwfP0, HwfS.
    inversion HlcS; subst.
    inversion HwfP0 as [ | | | | | Θa Δa P0' Hg0 Hwf0' Heqa ]; subst.
    try rewrite aenv_minus_empty in *.
    inversion HwfS as [ | | | | | Θb Δb Rp Hgs Hwfs Heqb ]; subst.
    try rewrite aenv_minus_empty in *.
    destruct IHHc
      as [Hle [Hwf1 [Hnfd1 [Hfaf1 [[Qt [HeQt [Hcons Hrs]]] Hrp]]]]]; auto.
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    split; [ exact Hnfd1 | ]. split; [ exact Hfaf1 | ].
    split.
    + exists (bskl_univ_ghost Qt). split.
      { simpl. rewrite HeQt. reflexivity. }
      split.
      * simpl. apply ad_pat_consis__dot_univ_ghost. exact Hcons.
      * simpl. apply ad_refine_syn_univ_ghost_keep_intro; exact Hrs.
    + simpl. apply ad_refine_pskl__univ_ghost_keep; exact Hrp.
  - (* UnivGhost1 : decorated *)
    simpl in HwfP0, HwfS.
    inversion HwfP0 as [ | | | L0 Θa Δa P0a Hbody0 Heqa | | ]; subst.
    inversion HwfS as [ | | | | | ΘbS ΔbS SbS HgS HwfSbody HeqS ]; subst.
    try rewrite aenv_minus_empty in *.
    pick fresh α for
      (L `union` L0 `union` dom Θ0 `union` dom Θ1
       `union` ftvar_in_pskl P0 `union` ftvar_in_uskl R `union` ftvar_in_pskl Q
       `union` Δ1 `union` Δ2).
    assert (HαL : α `notin` L) by auto.
    assert (HwfΘα : {{ ⊢ ((α ~ abind_tvar) ++ Θ0) }}a)
      by (apply a_wf_aenv__tvar; auto).
    assert (HwfP0α : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty
                       ⊢ₚₛ (open_pskl_wrt_pskl P0 (pskl_var_f α)) }}a).
    { eapply a_wf_pskl_delta_mono;
        [ apply Hbody0; auto
        | intros γ _ Hγ; clear - Hγ; fsetdec ]. }
    assert (HwfSα : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty
                   ⊢ₚₛ (uskl_to_pskl (uskl_univ_ghost R)) }}a).
    { simpl. apply a_wf_pskl__univ_ghost; [ exact HgS | ]. rewrite aenv_minus_empty.
      eapply a_wf_pskl_weaken; [ | exact HwfSbody ].
      intros y b Hb. unfold binds; right; exact Hb. }
    destruct (@delta_inv_open_tvar (Δ1 `union` Δ2) (add α Δ1 `union` Δ2) α Θ0) as (Hrigα & Hnfdα & Hfafα);
        [ auto | auto | clear; fsetdec | exact Hrig | auto | auto | ].
    destruct (H0 α HαL HwfΘα HlcS HwfP0α HwfSα Hrigα Hnfdα Hfafα)
      as [Hleα [Hwfα [Hnfdα1 [Hfafα1 [[Qtα [HeQtα [Hconsα Hrsα]]] Hrpα]]]]].
    assert (Hwf1 : {{ ⊢ Θ1 }}a)
      by (apply a_wf_aenv_tvar_inv in Hwfα; tauto).
    assert (Hα1 : α `notin` dom Θ1) by auto.
    pose proof (a_wf_aenv_def_ftv_notin Hwf1 Hα1) as Hdefsα.
    split; [ eapply a_isub_strip_tvar; eauto | ].
    split; [ exact Hwf1 | ].
    split.
    { apply no_flex_dep_strip with (α := α).
      apply no_flex_dep_cong with (Δ := add α Δ1 `union` Δ2);
        [ clear; fsetdec | exact Hnfdα1 ]. }
    split.
    { apply faf_strip with (α := α).
      apply faf_cong with (Δ := add α Δ1 `union` Δ2);
        [ clear; fsetdec | exact Hfafα1 ]. }
    split.
    + exists (bskl_all_inh (close_bskl_wrt_bskl α Qtα)). split.
      { simpl. rewrite bskl_to_pskl_close. rewrite HeQtα.
        rewrite close_pskl_wrt_pskl_open_pskl_wrt_pskl;
          [ reflexivity | clear - Fr; solve_notin_auto ]. }
      split.
      * simpl. apply ad_pat_consis__univ_ghost_inh
          with (L := dom Θ1 `union` singleton α `union` ftvar_in_uskl R).
        intros α0 Hα0.
        rewrite <- (subst_bskl_in_bskl_spec Qtα (bskl_var_f α0) α).
        replace (uskl_univ_ghost R)
          with (subst_uskl_in_uskl (uskl_var_f α0) α (uskl_univ_ghost R))
          by (simpl; rewrite subst_uskl_in_uskl_fresh_eq;
              [ reflexivity | clear - Fr; solve_notin_auto ]).
        change ((α0 ~ abind_tvar) ++ Θ1)
          with (nil ++ (α0 ~ abind_tvar) ++ Θ1).
        eapply ad_pat_consis_rename_tvar;
          [ exact Hconsα | exact Hα1 | exact Hdefsα ].
      * change (pskl_to_bskl_inh (pskl_all_syn P0))
          with (bskl_all_inh (pskl_to_bskl_inh P0)).
        eapply ad_refine_syn_close_all with (α := α);
          [exact Hwf1 | exact Hα1 | clear - Fr; solve_notin_auto | exact Hrsα].
    + simpl.
      assert (Hrpα' : {{ ((α ~ abind_tvar) ++ Θ1) ⨟ Δ2 ⊢ᵣₚ
                        (pskl_univ_ghost (uskl_to_pskl R))
                        ⊳ (open_pskl_wrt_pskl Q (pskl_var_f α)) }}ad)
        by exact Hrpα.
      apply ad_refine_pskl__univ_ghost_fill
        with (L := dom Θ1 `union` singleton α
                   `union` ftvar_in_uskl R `union` ftvar_in_pskl Q
                   `union` Δ1 `union` Δ2).
      intros α0 Hα0.
      rewrite (subst_pskl_in_pskl_intro α Q (pskl_var_f α0));
        [ | clear - Fr; solve_notin_auto ].
      replace (pskl_univ_ghost (uskl_to_pskl R))
        with (subst_pskl_in_pskl (pskl_var_f α0) α
                (pskl_univ_ghost (uskl_to_pskl R)))
        by (simpl; rewrite subst_pskl_in_pskl_fresh_eq;
            [ reflexivity
            | rewrite ftvar_in_pskl_uskl_to_pskl; clear - Fr; solve_notin_auto ]).
      eapply ad_refine_pskl_rename_ctx_gen with (Θ1 := nil);
        [ change (nil ++ (α ~ abind_tvar) ++ Θ1)
            with ((α ~ abind_tvar) ++ Θ1); exact Hrpα'
        | simpl; exact Hα1 | exact Hdefsα | clear - Hα0; fsetdec ].
  - (* UnivGhost2 *)
    simpl in HwfS. inversion HlcS; subst.
    inversion HwfS as [ | | | | | Θb Δb Rp Hgs Hwfs Heqb ]; subst.
    try rewrite aenv_minus_empty in *.
    destruct IHHc
      as [Hle [Hwf1 [Hnfd1 [Hfaf1 [[Qt [HeQt [Hcons Hrs]]] Hrp]]]]]; auto.
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    split; [ exact Hnfd1 | ]. split; [ exact Hfaf1 | ].
    split.
    + exists Qt. split; [ exact HeQt | ].
      split; [ simpl; apply ad_pat_consis__univ_ghost_drop; exact Hcons | exact Hrs ].
    + simpl. apply ad_refine_pskl__univ_ghost_remove. exact Hrp.
  - (* GhostR *)
    split; [ apply a_isub_refl; try assumption; auto | ].
    split; [ exact Hwf | ]. split; [ exact Hnfd | ]. split; [ exact Hfaf | ].
    split.
    + exists (pskl_to_bskl_syn (uskl_to_pskl R)).
      split; [ apply bskl_to_pskl_pskl_to_bskl_syn | ].
      split.
      * apply ad_pat_consis_psi_cong with (Ψ := empty); [ | symmetry; exact H0 ].
        apply ad_pat_consis_refl_erase; [ exact HlcS | ].
        intros α0 Hα0.
        assert (HX' : α0 `in` ftvar_in_pskl (uskl_to_pskl R))
          by (rewrite ftvar_in_pskl_uskl_to_pskl; exact Hα0).
        exact (a_wf_pskl_ftv_binds HwfS HX').
      * replace (pskl_to_bskl_inh pskl_ghost) with (@bskl_ghost) by reflexivity.
        apply ad_refine_syn__ghost; exact H.
    + eapply ad_refine_pskl_refl_gen; exact HwfS.
  - (* UnivGhostR *)
    simpl in HwfP0.
    inversion HwfP0 as [ | | | | | Θa Δa P0' Hg0 Hwf0' Heqa ]; subst.
    try rewrite aenv_minus_empty in *.
    destruct IHHc
      as [Hle [Hwf1 [Hnfd1 [Hfaf1 [[Qt [HeQt [Hcons Hrs]]] Hrp]]]]]; auto.
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    split; [ exact Hnfd1 | ]. split; [ exact Hfaf1 | ].
    split.
    + exists Qt. split; [ exact HeQt | ].
      split; [ exact Hcons | ].
      apply ad_refine_syn_univ_ghost_remove_intro. exact Hrs.
    + exact Hrp.
Qed.

(* ===================================================================== *)
(*  Soundness of consistency, part 1 (thm:sound-consistency)              *)
(*                                                                        *)
(*  Now a COROLLARY of the decorated soundness above.  An ordinary        *)
(*  consistency run decorates to a run with the EMPTY tag context         *)
(*  (lemma:decorating-algorithmic-consistency, [a_consis_decorate]),      *)
(*  whose subject is the plain skeleton read as an untagged unresolved    *)
(*  skeleton.  The decorated conclusion then reads back verbatim, because *)
(*  erasure is a retraction on plain skeletons                            *)
(*  ([uskl_to_pskl_pskl_to_uskl] : ⌊pskl_to_uskl P⌋ˢ = P).                *)
(* ===================================================================== *)

Corollary a_consis_sound_aux : forall Δ1 Δ2 Θ0 P0 P P' Θ1,
  {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ P' ⊣ Θ1 }}a ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
  (forall α, α `in` (Δ1 `union` Δ2) -> binds α abind_tvar Θ0) ->
  no_flex_dep (Δ1 `union` Δ2) Θ0 ->
  flex_above_free (Δ1 `union` Δ2) Θ0 ->
  Θ0 ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\
  no_flex_dep (Δ1 `union` Δ2) Θ1 /\ flex_above_free (Δ1 `union` Δ2) Θ1 /\
  (exists Qt, bskl_to_pskl Qt = P' /\
     {{ empty ⨟ Θ1 ⊢ˢ (pskl_to_uskl P) ∼ Qt }}ad /\
     {{ Θ1 ⨟ Δ1 ⊢ᵣ (pskl_to_bskl_inh P0) ⊳ Qt }}ad) /\
  {{ Θ1 ⨟ Δ2 ⊢ᵣₚ P ⊳ P' }}ad.
Proof.
  intros * Hc Hwf HwfP0 HwfP Hrig Hnfd Hfaf.
  assert (HlcS : lc_uskl (pskl_to_uskl P))
    by (apply pskl_to_uskl_lc; eapply a_wf_pskl_lc; eauto).
  assert (HwfS : {{ Θ0 ⨟ empty ⊢ₚₛ (uskl_to_pskl (pskl_to_uskl P)) }}a)
    by (rewrite uskl_to_pskl_pskl_to_uskl; exact HwfP).
  destruct (a_consistag_sound_aux
              (a_consis_decorate Hc (a_wf_aenv_uniq Hwf)) Hwf HlcS
              HwfP0 HwfS Hrig Hnfd Hfaf)
    as [Hle [Hwf1 [Hnfd1 [Hfaf1 [Hex Hrp]]]]].
  rewrite uskl_to_pskl_pskl_to_uskl in Hrp.
  split; [ exact Hle | ]. split; [ exact Hwf1 | ].
  split; [ exact Hnfd1 | ]. split; [ exact Hfaf1 | ].
  split; [ exact Hex | exact Hrp ].
Qed.

(** Paper-shaped statement (thm:sound-consistency, part 1): with the
    auxiliary Δ-contexts empty, a consistency run is an identity
    increase whose output is a coloured skeleton consistent with the
    synthesised painting of the input and a valid refinement of both
    inputs. *)
Corollary a_consis_sound : forall Θ0 P0 P P' Θ1,
  {{ Θ0 ⊢[ P0 ] P ∼ P' ⊣ Θ1 }}a ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
  Θ0 ⊴ Θ1 /\
  (exists Qt, bskl_to_pskl Qt = P' /\
     {{ empty ⨟ Θ1 ⊢ˢ (pskl_to_uskl P) ∼ Qt }}ad /\
     {{ Θ1 ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P0) ⊳ Qt }}ad) /\
  {{ Θ1 ⨟ empty ⊢ᵣₚ P ⊳ P' }}ad.
Proof.
  intros * Hc Hwf HwfP0 HwfP.
  destruct (a_consis_sound_aux Hc Hwf HwfP0 HwfP
              (@rig_empty _) (@no_flex_dep_empty _) (@faf_empty _))
    as [Hle [Hwf1 [Hnfd [Hfaf [[Qt [HeQt [Hcons Hrs]]] Hrp]]]]].
  split; [ exact Hle | ].
  split.
  - exists Qt. split; [ exact HeQt | ]. split; [ exact Hcons | ].
    exact Hrs.
  - exact Hrp.
Qed.

(* ===================================================================== *)
(*  A consistency run's OUTPUT is SCOPED in the output context             *)
(*                                                                        *)
(*  The scoping half of [a_consis_output_wf] (prop_wf_preservation.v),    *)
(*  at ANY Δ1/Δ2 and without that lemma's shielded-variable hypotheses.   *)
(*  ⚙ Why a second statement: consistency completeness's C-Arrow row      *)
(*  needs the first component's output scoped at the run's output         *)
(*  context, and [a_consis_output_wf]'s file IMPORTS consistency          *)
(*  completeness.  Until 2026-10-10 the scope was read off the soundness  *)
(*  join's TARGET instead ([ad_pat_consis_target_wf]); that reading died  *)
(*  with the Ghost rows' fill premise.                                     *)
(* ===================================================================== *)
Lemma a_consis_output_scope : forall Δ1 Δ2 Θ0 P0 P Q Θ1,
  {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}a ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
  (forall α, α `in` (Δ1 `union` Δ2) -> binds α abind_tvar Θ0) ->
  no_flex_dep (Δ1 `union` Δ2) Θ0 ->
  flex_above_free (Δ1 `union` Δ2) Θ0 ->
  a_scope_pskl Θ1 Q.
Proof.
  intros Δ1 Δ2 Θ0 P0 P Q Θ1 Hc.
  induction Hc; intros Hwf HwfP0 HwfP Hcov Hnfd Hfaf.
  - (* C-Ghost : output P0 *) exact (a_scope_pskl_of_wf HwfP0).
  - (* C-Unit *)
    split; [ constructor | intros γ Hγ; exfalso; simpl in Hγ; clear - Hγ; fsetdec ].
  - (* C-Rigid *) apply a_scope_pskl_var. left; exact H.
  - (* C-Arrow *)
    inversion HwfP0 as [ | | Θz Δz P0az P0bz HwfP0a HwfP0b | | | ]; subst.
    inversion HwfP as [ | | Θz Δz P1z P2z HwfP1 HwfP2 | | | ]; subst.
    destruct (a_consis_sound_aux Hc1 Hwf HwfP0a HwfP1 Hcov Hnfd Hfaf)
      as [Hle1 [Hwf1 [Hnfd1 [Hfaf1 _]]]].
    assert (Hcov1 : forall α, α `in` (Δ1 `union` Δ2) -> binds α abind_tvar Θ1)
      by (intros α Hα; eapply a_isub_binds_tvar; [ exact Hle1 | apply Hcov; exact Hα ]).
    assert (HwfP0b1 : {{ Θ1 ⨟ empty ⊢ₚₛ P0b }}a)
      by (eapply a_wf_pskl_isub; [ exact HwfP0b | exact Hle1 ]).
    assert (HwfP21 : {{ Θ1 ⨟ empty ⊢ₚₛ P2 }}a)
      by (eapply a_wf_pskl_isub; [ exact HwfP2 | exact Hle1 ]).
    destruct (IHHc1 Hwf HwfP0a HwfP1 Hcov Hnfd Hfaf) as [Hl1 Hb1].
    destruct (IHHc2 Hwf1 HwfP0b1 HwfP21 Hcov1 Hnfd1 Hfaf1) as [Hl2 Hb2].
    destruct (a_consis_sound_aux Hc2 Hwf1 HwfP0b1 HwfP21 Hcov1 Hnfd1 Hfaf1)
      as [Hle2 _].
    split; [ constructor; assumption | ].
    intros γ Hγ; simpl in Hγ. apply union_1 in Hγ as [Hγ | Hγ];
      [ eapply a_isub_binds_tvarish; [ exact Hle2 | exact (Hb1 γ Hγ) ]
      | exact (Hb2 γ Hγ) ].
  - (* C-ForallInh : the opened run, re-bound *)
    assert (HαP0 : α `notin` ftvar_in_pskl P0) by (clear - H; fsetdec).
    assert (HαP : α `notin` ftvar_in_pskl P) by (clear - H; fsetdec).
    assert (HαΔ : α `notin` (Δ1 `union` Δ2)) by (clear - H; fsetdec).
    assert (HαΘ0 : α `notin` dom Θ0)
      by (pose proof (dom_subset_ftvar_in_aenv Θ0); clear - H H0; fsetdec).
    apply a_scope_pskl_all_close.
    destruct (@delta_inv_open_tvar (Δ1 `union` Δ2) (add α Δ1 `union` add α Δ2) α Θ0
                ltac:(auto) ltac:(auto) ltac:(clear; fsetdec) Hcov
                ltac:(auto) ltac:(auto)) as (HΔr & HΔn & HΔf).
    apply IHHc.
    + apply a_wf_aenv__tvar; [ exact HαΘ0 | exact Hwf ].
    + apply a_wf_pskl_all_syn_open_tvar;
        [ exact HwfP0 | clear - HαΘ0 HαP0; fsetdec ].
    + apply a_wf_pskl_all_syn_open_tvar;
        [ exact HwfP | clear - HαΘ0 HαP; fsetdec ].
    + exact HΔr.
    + exact HΔn.
    + exact HΔf.
  - (* C-ForallSyn : the subject's opening, re-bound *)
    assert (HαP : α `notin` ftvar_in_pskl P) by (clear - H; fsetdec).
    assert (HαΔ : α `notin` (Δ1 `union` Δ2)) by (clear - H; fsetdec).
    assert (HαΘ0 : α `notin` dom Θ0)
      by (pose proof (dom_subset_ftvar_in_aenv Θ0); clear - H H0; fsetdec).
    apply a_scope_pskl_all_close.
    destruct (@delta_inv_open_tvar (Δ1 `union` Δ2) (Δ1 `union` add α Δ2) α Θ0
                ltac:(auto) ltac:(auto) ltac:(clear; fsetdec) Hcov
                ltac:(auto) ltac:(auto)) as (HΔr & HΔn & HΔf).
    apply IHHc.
    + apply a_wf_aenv__tvar; [ exact HαΘ0 | exact Hwf ].
    + eapply a_wf_pskl_delta_mono;
        [ apply (a_wf_pskl_reassoc HwfP0 α) | clear; fsetdec ].
    + apply a_wf_pskl_all_syn_open_tvar;
        [ exact HwfP | clear - HαΘ0 HαP; fsetdec ].
    + exact HΔr.
    + exact HΔn.
    + exact HΔf.
  - (* C-UnivGhost *)
    inversion HwfP0 as [ | | | | | Θz Δz P0z Hg0 Hwb0 ]; subst.
    inversion HwfP as [ | | | | | Θz Δz Pz Hgs Hwbs ]; subst.
    rewrite aenv_minus_empty in Hwb0, Hwbs.
    destruct (IHHc Hwf Hwb0 Hwbs Hcov Hnfd Hfaf) as [Hl Hb].
    split; [ constructor; exact Hl | exact Hb ].
  - (* C-UnivGhost1 : the input's opening, re-bound *)
    assert (HαP0 : α `notin` ftvar_in_pskl P0) by (clear - H; fsetdec).
    assert (HαΔ : α `notin` (Δ1 `union` Δ2)) by (clear - H; fsetdec).
    assert (HαΘ0 : α `notin` dom Θ0)
      by (pose proof (dom_subset_ftvar_in_aenv Θ0); clear - H H0; fsetdec).
    apply a_scope_pskl_all_close.
    destruct (@delta_inv_open_tvar (Δ1 `union` Δ2) (add α Δ1 `union` Δ2) α Θ0
                ltac:(auto) ltac:(auto) ltac:(clear; fsetdec) Hcov
                ltac:(auto) ltac:(auto)) as (HΔr & HΔn & HΔf).
    apply IHHc.
    + apply a_wf_aenv__tvar; [ exact HαΘ0 | exact Hwf ].
    + apply a_wf_pskl_all_syn_open_tvar;
        [ exact HwfP0 | clear - HαΘ0 HαP0; fsetdec ].
    + eapply a_wf_pskl_delta_mono;
        [ apply (a_wf_pskl_reassoc HwfP α) | clear; fsetdec ].
    + exact HΔr.
    + exact HΔn.
    + exact HΔf.
  - (* C-UnivGhost2 *)
    inversion HwfP as [ | | | | | Θz Δz Pz Hgs Hwbs ]; subst.
    rewrite aenv_minus_empty in Hwbs.
    exact (IHHc Hwf HwfP0 Hwbs Hcov Hnfd Hfaf).
  - (* C-Flex : the subject variable survives the unification *)
    assert (Hbα : a_binds_tvar α Θ0).
    { inversion HwfP as [ | Θz Δz αz Hd | | | | ]; subst; exact Hd. }
    pose proof a_assign_unify_consis_sound as [_ [Hus _]].
    destruct (Hus _ _ _ _ H Hwf) as [Hle _].
    apply a_scope_pskl_var. eapply a_isub_binds_tvarish; [ exact Hle | exact Hbα ].
  - (* C-FlexL *)
    assert (Hbα : a_binds_tvar α Θ0).
    { inversion HwfP as [ | Θz Δz αz Hd | | | | ]; subst; exact Hd. }
    pose proof a_assign_unify_consis_sound as [Has _].
    match goal with
    | Ha : {{ _ ⊲[ _ ] _ ≔ _ ⊣ _ }}a |- _ =>
        destruct (Has _ _ _ _ _ Ha (a_decls__nil) Hwf HwfP0) as [Hle _]
    end.
    apply a_scope_pskl_var. eapply a_isub_binds_tvarish; [ exact Hle | exact Hbα ].
  - (* C-FlexR *)
    assert (Hbα : a_binds_tvar α Θ0).
    { inversion HwfP0 as [ | Θz Δz αz Hd | | | | ]; subst; exact Hd. }
    pose proof a_assign_unify_consis_sound as [Has _].
    match goal with
    | Ha : {{ _ ⊲[ _ ] _ ≔ _ ⊣ _ }}a |- _ =>
        destruct (Has _ _ _ _ _ Ha (a_decls__nil) Hwf HwfP) as [Hle _]
    end.
    apply a_scope_pskl_var. eapply a_isub_binds_tvarish; [ exact Hle | exact Hbα ].
  - (* C-GhostR : output the subject *) exact (a_scope_pskl_of_wf HwfP).
  - (* C-UnivGhostR *)
    inversion HwfP0 as [ | | | | | Θz Δz P0z Hg0 Hwb0 ]; subst.
    rewrite aenv_minus_empty in Hwb0.
    exact (IHHc Hwf Hwb0 HwfP Hcov Hnfd Hfaf).
Qed.
