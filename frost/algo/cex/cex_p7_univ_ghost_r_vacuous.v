(** ⚠️ THE MOTIVE'S THIRD SOLUTION PREMISE MAKES P7b's Sub-UnivGhostR ROW
    VACUOUS.  The row is still PROVABLE (by contradiction, and it is Qed:
    [a_sub_complete_hole_p0_precision]'s neighbour
    [a_sub_complete_univ_ghost_r] in prop_sub_complete_thm.v), but the
    mechanized completeness theorem therefore says NOTHING about the
    solutions that row describes, whereas the paper's statement does.

    WHERE THE PREMISE COMES FROM.  The paper's generalised
    thm:complete-subtyping (subtyping-proofs.tex:3054-3074) gives a solution
    TWO conditions:

        (join)     typsub^N_M[Ψ] Θ ⊢ syn(κS) ⊑ bid Q
        (P0-fill)  Θ ⊢ inh(κP0) ⤳syn bid Q

    DESIGN-completeness-subtyping.md §1 added a THIRD — the SUBJECT's own
    refinement [⊢ᵣₚᵃ κ⌊R⌋ˢ ⊳ ⌊Q⌋] — as "lesson 1", on the grounds that it is
    what soundness produces for every algorithmic output, so that the
    sound/complete pair still characterises the algorithm exactly.

    THAT GROUND HOLDS FOR CONSISTENCY AND FAILS FOR SUBTYPING.
    [a_consis_sound] (prop_consis_sound.v:5582) really does export
    [Θ1 ⨟ ∅ ⊢ᵣₚᵃ P ⊳ P'].  [a_sub_sound_thm] (prop_decorate_key.v:3326)
    exports NO such conjunct — and it could not, because algorithmic
    [UnivGhostR] ([a_sub__univ_ghost_r]) outputs [∀◇.P] from the input [P],
    and refinement has no rule putting a [∀◇] on the RIGHT of a non-ghost
    left-hand side.

    §1 CONTENTS.  The general fact (whatever refines into a [∀◇] is itself a
    [◇] or a [∀◇]) lives in prop_sub_complete_thm.v as
    [ad_refine_pskl_f_tophole_r_shape]; §2 below is the CONCRETE witness that
    the excluded configuration is otherwise perfectly derivable, i.e. that the
    exclusion is a real loss of coverage and not a vacuity that was there
    anyway.

    WHAT THE AUTHORS MUST DECIDE.  Either (a) the third premise is dropped for
    subtyping and Sub-Infer / Sub-Check reacquire the subject refinement they
    need for their [a_consis_complete_thm] call some other way, or (b) it is
    kept and the theorem is documented as not covering ∀◇-counterpart
    solutions, or (c) it is weakened to hold modulo the ∀◇s that UnivGhostR /
    UnivGhostL insert.  Registered in docs/PAPER-GAPS.md. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_extra.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo_sub.
Require Import src.frost.algo.def_decl_algo_sub_hyg.
Require Import src.frost.algo.prop_consis_sound.
Require Import src.frost.algo.prop_sub_complete_thm.

Set Implicit Arguments.

(* ===================================================================== *)
(*  §1  THE EXCLUSION, in the exact shape P7b's Sub-UnivGhostR row has     *)
(* ===================================================================== *)

(** The row's subject is [guarded_uskl] and its counterpart is [∀◇.Q0], so the
    third premise reads [κ⌊R⌋ˢ ⊳ ∀◇.⌊Q0⌋] with a GUARDED left-hand side — and
    that is underivable.  No well-formedness is needed anywhere. *)
Lemma p7_univ_ghost_r_third_premise_impossible :
  forall F Θ Δ κ R P Q0,
    ⌊ R ⌋ˢ = P ->
    guarded_uskl (msubst_uskl_syn κ R) ->
    ad_refine_pskl_f F Θ Δ (msubst_pskl κ P) (bskl_to_pskl (bskl_tophole Q0)) ->
    False.
Proof.
  intros F Θ Δ κ R P Q0 HeqP Hg Hrp. cbn in Hrp.
  destruct (guarded_uskl_erase_not_ghost Hg) as [Hnh Hnt].
  rewrite uskl_to_pskl_msubst_uskl_syn, HeqP in Hnh, Hnt.
  destruct (ad_refine_pskl_f_tophole_r_shape Hrp) as [Hc | [P' Hc]];
    [ exact (Hnh Hc) | exact (Hnt P' Hc) ].
Qed.

Print Assumptions p7_univ_ghost_r_third_premise_impossible.

(* ===================================================================== *)
(*  §2  NON-VACUITY — the paper's TWO conditions are satisfiable there     *)
(*                                                                        *)
(*  So the third premise really does REMOVE coverage.  The witness is the  *)
(*  smallest possible: [Θ0 = Θ = ·], [κ = ι], subject [unit], and the      *)
(*  declarative UnivGhostR run [· ⊢ syn{unit} ⩽ ∀◇.unit].                  *)
(* ===================================================================== *)

Definition cex_R : uskl := uskl_unit.
Definition cex_Q : bskl := bskl_tophole bskl_unit.

(** (a) the JOIN condition — the declarative Sub-UnivGhostR derivation *)
Lemma cex_join :
  ad_pat_sub_g 0 a_sub_mode_sk mode_tc empty nil
    (msubst_uskl_syn nil cex_R) cex_Q.
Proof.
  cbn. apply ad_pat_sub_g__univ_ghost_r.
  - reflexivity.
  - apply guarded_uskl__unit.
  - apply guarded_bskl__unit.
  - apply is_sskl__unit.
  - apply ad_pat_consis__unit; reflexivity.
Qed.

(** (b) the P0-FILL condition, at the [P0 = □] that [skmod[SK]{P0}{TC}]
    prescribes for this row *)
Lemma cex_p0_fill :
  ad_refine_syn_f empty nil empty
    (pskl_to_bskl_inh (msubst_pskl nil pskl_hole)) cex_Q.
Proof.
  cbn. unfold cex_Q.
  change (bskl_tophole bskl_unit)
    with (pskl_to_bskl_syn (pskl_tophole pskl_unit)).
  apply ad_refine_syn_f__hole.
  - cbn. clear; fsetdec.
  - apply a_wf_pskl__tophole;
      [ apply guarded_pskl__unit | apply a_wf_pskl__unit ].
Qed.

(** (c) the increase is the identity on the empty context *)
Lemma cex_inc : nil ∷ nil ⊑ nil.
Proof. apply a_inc__empty. apply a_suffix__nil. Qed.

(** (d) …and the THIRD condition is the one that fails. *)
Lemma cex_third_fails :
  ad_refine_pskl_f empty nil empty
    (msubst_pskl nil ⌊ cex_R ⌋ˢ) (bskl_to_pskl cex_Q) ->
  False.
Proof.
  intros H.
  eapply (p7_univ_ghost_r_third_premise_impossible nil cex_R eq_refl);
    [ cbn; apply guarded_uskl__unit | exact H ].
Qed.

Print Assumptions cex_join.
Print Assumptions cex_p0_fill.
Print Assumptions cex_third_fails.
