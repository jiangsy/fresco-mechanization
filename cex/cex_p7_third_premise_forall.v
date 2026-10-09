(** ⚠️ HISTORICAL WITNESS — the ROOT-level third solution premise excluded
    every solution whose subject and counterpart disagree at the head.
    RESOLVED 2026-07-30 (same day): the motive was repaired — the premise was
    removed from the root and moved to the join's CONSISTENCY LEAVES
    ([ad_pat_sub_fuel], def_subtyping.v), under which both
    configurations below are covered (their leaves are [unit ⊳ unit]).  This
    file keeps the machine-checked record of why the root-level formulation
    was wrong; the text below describes the PRE-repair state.

    THE ORIGINAL FINDING.  The root premise did not only lose Sub-UnivGhostR:
    it excluded every solution whose subject and counterpart disagree at the
    head — in particular the ForallL instantiations and the ForallR
    generalisations that are the POINT of the subtyping relation.

    Companion to [cex_p7_univ_ghost_r_vacuous.v] (which see for where the
    premise came from).  That file shows the ROW Sub-UnivGhostR closes by
    contradiction.  This file shows the damage is not confined to a ghost
    corner: the third premise [{{ … ⊢ᵣₚ κ⌊R⌋ˢ ⊳ ⌊Q⌋ }}ad] is a LOCKSTEP condition —
    [ad_refine_pskl] descends both sides together, so it can only hold when
    subject and counterpart agree in shape (modulo ghosts on the LEFT and
    flexibles) — while declarative subtyping exists precisely to relate
    shape-DISAGREEING sides:

      - [Sub-ForallL] strips a ∀ from the SUBJECT   (∀a.a ⩽ unit), and
      - [Sub-ForallR] adds  a ∀ to the COUNTERPART  (unit ⩽ ∀a.unit).

    Both configurations below satisfy the paper's two solution conditions
    (join + P0-fill), are well formed and mode-compatible, and FAIL the
    mech-added third premise — so the mechanized completeness theorem says
    NOTHING about either, although the algorithm handles both (its output
    tracks P0, not the subject, so the optimality conclusion is fine there).

    WHY CONSISTENCY'S THIRD PREMISE DOES NOT HAVE THIS PROBLEM.  The paper's
    own augmented thm:complete-consistency (consistency-proofs.tex:2230-2242)
    carries the same subject-refinement condition, and there it is harmless:
    [ad_pat_consis] is itself a LOCKSTEP relation — every ∀-inh counterpart
    row ([__forall_inh_tagged] / [__forall_inh_untagged] / [__univ_ghost_inh])
    requires the subject to be a ∀ or a ghost, so consistency never pairs a
    guarded subject with a ∀-headed counterpart, and the third condition only
    adds what it was designed to add: the no-capture discipline on ghost fills
    (the [(P0=∀X.X, P=∀X.◇, Q=∀X.X)] cex of DESIGN-subtyping.md §3.1).
    Subtyping's ForallL / ForallR / UnivGhostR BREAK lockstep — that is their
    job — so importing consistency's condition verbatim cuts exactly the
    solutions those rules create.  Registered in docs/PAPER-GAPS.md. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.def_shapes.
Require Import src.fresco.coercions.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.def_meta.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo_decl.def_subtyping.
Require Import src.fresco.algo.prop_refine.
Require Import src.fresco.algo.consis.prop_soundness_consis.

Set Implicit Arguments.

(* ===================================================================== *)
(*  §1  Sub-ForallL — the instantiation  ∀a.a ⩽ unit  is excluded          *)
(*                                                                        *)
(*  (TY, TC), Θ0 = Θ = ·, κ = ι, subject ∀a.a, counterpart unit,           *)
(*  P0 = unit.  The same shape scales to the flagship ∀a.a→a ⩽ unit→unit. *)
(* ===================================================================== *)

Definition cexL_R : uskl := uskl_all_syn (uskl_var_b 0).
Definition cexL_P0 : pskl := pskl_unit.
Definition cexL_Q : bskl := bskl_unit.

(** The subtyping problem is well posed: subject wf, P0 wf and TC-compatible. *)
Lemma cexL_subject_wf : {{ nil ⨟ empty ⊢ₚₛ ⌊ cexL_R ⌋ˢ }}a.
Proof.
  cbn. apply a_wf_pskl__all with (L := empty).
  intros α Hα. cbn. apply a_wf_pskl__var. left. clear; fsetdec.
Qed.

Lemma cexL_p0_mode : a_ty_mode_compat mode_tc cexL_P0.
Proof. exact (a_ty_mode_compat__tc ptyp_unit). Qed.

(** (b) the P0-FILL condition. *)
Lemma cexL_p0_fill :
  {{ nil ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl nil cexL_P0)) ⊳ cexL_Q }}ad.
Proof. cbn. apply ad_refine_syn__unit. Qed.

(** (c) the increase is the identity on the empty context. *)
Lemma cexL_inc : nil ∷ nil ⊑ nil.
Proof. apply a_inc__empty. apply a_suffix__nil. Qed.

(** (d) …and the THIRD condition fails: [∀a.a ⊳ unit] has no rule — the only
    rows with a [∀] on the left are [__all] (wants a [∀] on the right) and
    [__flex_l] (wants a flexible variable on the left). *)
Lemma cexL_third_fails :
  {{ nil ⨟ empty ⊢ᵣₚ (msubst_pskl nil ⌊ cexL_R ⌋ˢ) ⊳ (bskl_to_pskl cexL_Q) }}ad ->
  False.
Proof. cbn. intros H. inversion H. Qed.

(* ===================================================================== *)
(*  §2  Sub-ForallR — checking against a ∀:  unit ⩽ ∀a.unit  is excluded   *)
(*                                                                        *)
(*  (TY, TC), Θ0 = Θ = ·, κ = ι, subject unit, counterpart ∀a.unit,        *)
(*  P0 = ∀a.unit.                                                         *)
(* ===================================================================== *)

Definition cexR_R : uskl := uskl_unit.
Definition cexR_P0 : pskl := pskl_all_syn pskl_unit.
Definition cexR_Q : bskl := bskl_all_inh bskl_unit.

Lemma cexR_subject_wf : {{ nil ⨟ empty ⊢ₚₛ ⌊ cexR_R ⌋ˢ }}a.
Proof. cbn. apply a_wf_pskl__unit. Qed.

Lemma cexR_p0_mode : a_ty_mode_compat mode_tc cexR_P0.
Proof. exact (a_ty_mode_compat__tc (ptyp_all ptyp_unit)). Qed.

(** (b) the P0-FILL condition — the inherited painting of [∀a.unit] IS the
    counterpart, so the fill is the congruent descent. *)
Lemma cexR_p0_fill :
  {{ nil ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl nil cexR_P0)) ⊳ cexR_Q }}ad.
Proof.
  cbn. apply ad_refine_syn_all_intro with (L := empty).
  intros α Hα. cbn. apply ad_refine_syn__unit.
Qed.

(** (c) the increase is the identity on the empty context. *)
Lemma cexR_inc : nil ∷ nil ⊑ nil.
Proof. apply a_inc__empty. apply a_suffix__nil. Qed.

(** (d) …and the THIRD condition fails: [unit ⊳ ∀a.unit] has no rule — a
    refinement never invents a quantifier the subject does not have. *)
Lemma cexR_third_fails :
  {{ nil ⨟ empty ⊢ᵣₚ (msubst_pskl nil ⌊ cexR_R ⌋ˢ) ⊳ (bskl_to_pskl cexR_Q) }}ad ->
  False.
Proof. cbn. intros H. inversion H. Qed.

(* ===================================================================== *)
(*  §3  REPAIR CHECK — the LEAF-VALID join covers both configurations      *)
(*                                                                        *)
(*  Non-vacuity witnesses for the repaired motive: [ad_pat_sub_fuel] IS      *)
(*  derivable in both configurations above (each leaf's refinement is      *)
(*  [unit ⊳ unit]), so both are inside the repaired theorem's coverage.    *)
(*                                                                        *)
(*  ⚙ 2026-08-12: the §1/§2 witnesses over the leaf-FORGETTING mirror      *)
(*  [ad_pat_sub_g] went with that mirror.  These are what is left, and     *)
(*  they say the same thing: the configurations are derivable joins.       *)
(* ===================================================================== *)

Lemma cexL_join_fuel : forall n,
  ad_pat_sub_fuel (S n) a_sub_mode_ty mode_tc empty nil
    (msubst_uskl_syn nil cexL_R) cexL_Q.
Proof.
  intro n. cbn.
  eapply ad_pat_sub_fuel__forall_l_untagged
    with (Ψ' := empty) (ψ := uskl_unit).
  - discriminate.
  - clear; fsetdec.
  - clear; fsetdec.
  - apply a_tags_sort__ty;
      [ apply is_dskl__unit
      | apply d_tags_skl__unit; reflexivity
      | apply uskl_ghost_free__unit ].
  - cbn. apply a_wf_pskl__unit.
  - cbn. change cexL_Q with (pskl_to_bskl_inh pskl_unit).
    apply ad_pat_sub_fuel__check.
    + apply guarded_uskl__unit.
    + apply guarded_pskl__unit.
    + apply ad_consis_join_inh_intro.
      * cbn. apply ad_pat_consis__unit. clear; fsetdec.
      * cbn. apply ad_refine_pskl__unit.
Qed.

Lemma cexR_join_fuel : forall n,
  ad_pat_sub_fuel (S n) a_sub_mode_ty mode_tc empty nil
    (msubst_uskl_syn nil cexR_R) cexR_Q.
Proof.
  intro n. cbn.
  apply ad_pat_sub_fuel__forall_r with (L := empty).
  intros α Hα. cbn.
  change bskl_unit with (pskl_to_bskl_inh pskl_unit).
  apply ad_pat_sub_fuel__check.
  - apply guarded_uskl__unit.
  - apply guarded_pskl__unit.
  - apply ad_consis_join_inh_intro.
    + cbn. apply ad_pat_consis__unit. clear; fsetdec.
    + cbn. apply ad_refine_pskl__unit.
Qed.

