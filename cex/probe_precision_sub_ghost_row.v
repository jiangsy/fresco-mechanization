(** PROBE — the GHOST row of [lemma:precision-sub] (proofs.tex:69-78).

    Section D, scouting item 3 (docs/HANDOFF-section-d.md §3).

    THE WORRY THIS PROBE RETIRES.  §3 flagged the statement as possibly false
    at [P' = □], because "the only applicable subtyping row is
    [ad_pat_sub__ghost], whose target must be an INHERITED PAINTING
    [pskl_to_bskl_inh P] and which carries [mod_comp_sk] — so for an arbitrary
    [Q] produced by the [P] derivation the conclusion is not immediate".

    ⭐ THE ANSWER: [□ ⊑ P] is far more restrictive than it looks, and it hands
    back precisely the Ghost row's fill.  [ad_precise P Q] is
    [inh{P} ⊳ inh{Q}], so at [P = □] the subject is [◇] and the only two rows
    are [ad_refine_syn__hole] — whose fill is a SYNTHESISED painting — and
    [__flex_r].  Since [pskl_to_bskl_inh] paints ∀ as [bskl_all_inh] while
    [pskl_to_bskl_syn] paints it [bskl_all_syn], the two images meet exactly
    on the [pskl_all_syn]-free skeletons.  So:

      · [□ ⊑ P] yields a Θ-well-scoped [P1] with [inh P = syn P1]
        ([ad_precise_hole_inv]) — exactly what [ad_pat_sub__ghost] wants; and
      · [□ ⊑ ∀X.P] is outright FALSE ([ad_precise_hole_all_absurd]), so the
        Ghost row never faces a quantified counterpart.

    ⚠️ A SECOND CANDIDATE COUNTEREXAMPLE, ALSO REFUTED (recorded so it is not
    re-tried).  [ad_pat_sub__flex_mono] is FUNCTION-mode only, so a DEFINED
    flexible [α̂ ⊑ 1] looked like it would strand [α̂ ⩽ ∀◇.1] at [M = TC].  It
    does not: [ad_pat_sub__univ_ghost_r] admits ANY *guarded* subject, and a
    variable IS guarded, so that row covers flexible subjects outside function
    mode.  §2 below records the positive derivation.

    ⛔ WHAT IS ACTUALLY LEFT for a full proof of lemma:precision-sub: the
    [Ψ [=] ∅] side condition of the Ghost row (automatic — a
    [pskl_to_uskl P] subject is TAG-free, so no [uskl_all_etag] and hence no
    tag-introducing row can fire at the root) and a [mod_comp_sk] transport
    along the precision.  Neither is the flagged obstruction. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_extra.
Require Import src.frost.coercions.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.decorated_algo.def_decl_algo.
Require Import src.frost.decorated_algo.def_decorated.
Require Import src.frost.decorated_algo.def_decl_algo_sub.
Require Import src.frost.algo.prop_precise.

Set Implicit Arguments.

(* ===================================================================== *)
(*  §1  [□ ⊑ P] inversion                                                 *)
(* ===================================================================== *)

Lemma refine_syn_hole_inv : forall Θ Δ S T,
  Θ ⨟ Δ ⊢ᵣᵃᵈ S ⊳ T ->
  S = bskl_hole ->
  exists P1, T = pskl_to_bskl_syn P1 /\ Θ ⨟ empty ⊢ₚₛᵃ P1.
Proof.
  intros Θ Δ S T H. induction H; intros HS; try discriminate HS.
  - (* __hole : the fill IS a synthesised painting *)
    eexists; split; [ reflexivity | eassumption ].
  - (* __flex_r : a flexible's two paintings agree *)
    match goal with Hb : binds ?a (abind_flex_mono_def ?t) _ |- _ =>
      exists (pskl_var_f a); split; [ reflexivity | ];
      apply a_wf_pskl__var; right; right; right; exists t; exact Hb
    end.
Qed.

Lemma ad_precise_hole_inv : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚᵣᵃᵈ pskl_hole ⊑ P ->
  exists P1, pskl_to_bskl_inh P = pskl_to_bskl_syn P1
             /\ Θ ⨟ empty ⊢ₚₛᵃ P1.
Proof. intros Θ Δ P H. exact (refine_syn_hole_inv H eq_refl). Qed.

Lemma ad_precise_hole_all_absurd : forall Θ Δ P,
  ~ (Θ ⨟ Δ ⊢ₚᵣᵃᵈ pskl_hole ⊑ (pskl_all_syn P)).
Proof.
  intros Θ Δ P H. destruct (ad_precise_hole_inv H) as [P1 [Heq _]].
  cbn in Heq. destruct P1; cbn in Heq; discriminate.
Qed.

(* ===================================================================== *)
(*  §2  The refuted second candidate: a flexible subject at [M = TC]      *)
(* ===================================================================== *)

Section FlexSubjectAtCheck.

  Variable α : atom.
  Definition psTh : aenv := (α ~ abind_flex_mono_def ptyp_unit) ++ nil.

  Lemma ps_precise : psTh ⨟ empty ⊢ₚᵣᵃᵈ (pskl_var_f α) ⊑ pskl_unit.
  Proof.
    unfold ad_precise. cbn.
    apply ad_refine_syn__flex_l with (τ := ptyp_unit);
      [ unfold psTh; eauto | cbn; apply ad_refine_syn__unit ].
  Qed.

  (** the [P]-side derivation *)
  Lemma ps_hyp :
    empty ⨟ psTh ⊢ᵃᵈ[ a_sub_mode_sk | mode_tc ]
      (pskl_to_uskl pskl_unit) ⩽ (bskl_tophole bskl_unit).
  Proof.
    cbn. apply ad_pat_sub__univ_ghost_r;
      [ reflexivity | apply guarded_uskl__unit | apply guarded_bskl__unit
      | apply is_sskl__unit | apply ad_pat_consis__unit; reflexivity ].
  Qed.

  (** ⭐ … and the [P']-side one EXISTS after all: UnivGhostR takes any
      guarded subject, and the flexible is reached through the consistency
      premise's own FlexL. *)
  Lemma ps_concl :
    empty ⨟ psTh ⊢ᵃᵈ[ a_sub_mode_sk | mode_tc ]
      (pskl_to_uskl (pskl_var_f α)) ⩽ (bskl_tophole bskl_unit).
  Proof.
    cbn. apply ad_pat_sub__univ_ghost_r;
      [ reflexivity | apply guarded_uskl__var | apply guarded_bskl__unit
      | apply is_sskl__unit | ].
    apply ad_pat_consis__flex_l with (τ := ptyp_unit);
      [ unfold psTh; eauto | cbn; apply ad_pat_consis__unit; reflexivity ].
  Qed.

End FlexSubjectAtCheck.
