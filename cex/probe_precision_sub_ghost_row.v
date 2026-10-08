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

      · [□ ⊑ P] yields a [P1] with [inh P = syn P1], Θ-well-scoped under
        the RHS presupposition [Θ ⨟ Δ ⊢ₚₛ P] ([ad_precise_hole_inv]) —
        exactly what [ad_pat_sub__ghost] wants; and
      · [□ ⊑ ∀X.P] is outright FALSE ([ad_precise_hole_all_absurd]), so the
        Ghost row never faces a quantified counterpart.

    ⚠️ RETRACTED 2026-10-08: the scoping half of [ad_precise_hole_inv] no
    longer comes from the refinement alone — the paper-faithful
    [ad_refine_syn__hole] dropped its [Θ ⨟ ∅ ⊢ₚₛ fill] premise (scoping is
    the judgement's presupposition), so [ad_precise_hole_inv] now takes the
    RHS presupposition [{{ Θ ⨟ Δ ⊢ₚₛ P }}a] and [refine_syn_hole_inv]
    concludes only the shape [T = syn P1].  The ∀ refutation is unchanged.

    ⚠️ A SECOND CANDIDATE COUNTEREXAMPLE, ALSO REFUTED (recorded so it is not
    re-tried).  [ad_pat_sub__flex_mono] is FUNCTION-mode only, so a DEFINED
    flexible [α̂ ⊑ 1] looked like it would strand [α̂ ⩽ ∀◇.1] at [M = TC].  It
    does not: [ad_pat_sub__univ_ghost_r] admits ANY *guarded* subject, and a
    variable IS guarded, so that row covers flexible subjects outside function
    mode.  §2 below records the positive derivation.

    ⛔ WHAT IS ACTUALLY LEFT for a full proof of lemma:precision-sub: the
    [Ψ [=] ∅] side condition of the Ghost row (automatic — a
    [pskl_to_uskl P] subject is TAG-free, so no [uskl_all_tag] and hence no
    tag-introducing row can fire at the root) and a [mod_comp_sk] transport
    along the precision.  Neither is the flagged obstruction. *)

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
Require Import src.fresco.algo.prop_precise.
Require Import src.fresco.algo.prop_refine.
Require Import src.fresco.algo.sub.look.prop_extract.   (* pskl_inh_eq_syn_inv *)

Set Implicit Arguments.

(* ===================================================================== *)
(*  §1  [□ ⊑ P] inversion                                                 *)
(* ===================================================================== *)

(** The inversion proper: the target of a ◇ source is a SYNTHESISED painting.
    Its scoping is no longer read off the rule — the paper-faithful
    [ad_refine_syn__hole] only asks [Δ ∩ ftv P [=] ∅], and well-formedness of
    the two sides is the judgement's PRESUPPOSITION. *)
Lemma refine_syn_hole_inv : forall Θ Δ S T,
  {{ Θ ⨟ Δ ⊢ᵣ S ⊳ T }}ad ->
  S = bskl_hole ->
  exists P1, T = pskl_to_bskl_syn P1.
Proof.
  intros Θ Δ S T H. induction H; intros HS; try discriminate HS.
  - (* __hole : the fill IS a synthesised painting *)
    eexists; reflexivity.
  - (* __flex_r : a flexible's two paintings agree *)
    match goal with |- exists _, bskl_var_f ?a = _ =>
      exists (pskl_var_f a); reflexivity
    end.
Qed.

(** The Ghost row's fill, scoped by the RHS presupposition [Θ ⨟ Δ ⊢ₚₛ P]:
    a closed-Δ reading of it is free ([a_wf_pskl_delta_mono] at [Δ = ∅]). *)
Lemma ad_precise_hole_inv : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚᵣ pskl_hole ⊑ P }}ad ->
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  exists P1, pskl_to_bskl_inh P = pskl_to_bskl_syn P1
             /\ {{ Θ ⨟ empty ⊢ₚₛ P1 }}a.
Proof.
  intros Θ Δ P H Hwf. destruct (refine_syn_hole_inv H eq_refl) as [P1 Heq].
  exists P1; split; [ exact Heq | ].
  rewrite <- (proj1 (@pskl_inh_eq_syn_inv _ _ Heq)).
  apply (a_wf_pskl_delta_mono Hwf). intros α _ Hα. fsetdec.
Qed.

Lemma ad_precise_hole_all_absurd : forall Θ Δ P,
  ~ ({{ Θ ⨟ Δ ⊢ₚᵣ pskl_hole ⊑ (pskl_all_syn P) }}ad).
Proof.
  intros Θ Δ P H. destruct (refine_syn_hole_inv H eq_refl) as [P1 Heq].
  cbn in Heq. destruct P1; cbn in Heq; discriminate.
Qed.

(* ===================================================================== *)
(*  §2  The refuted second candidate: a flexible subject at [M = TC]      *)
(* ===================================================================== *)

Section FlexSubjectAtCheck.

  Variable α : atom.
  Definition psTh : aenv := (α ~ abind_flex_mono_def ptyp_unit) ++ nil.

  Lemma ps_precise : {{ psTh ⨟ empty ⊢ₚᵣ (pskl_var_f α) ⊑ pskl_unit }}ad.
  Proof.
    unfold ad_precise. cbn.
    apply ad_refine_syn__flex_l with (τ := ptyp_unit);
      [ unfold psTh; eauto | cbn; apply ad_refine_syn__unit ].
  Qed.

  (** the [P]-side derivation *)
  Lemma ps_hyp :
    {{ empty ⨟ psTh ⊢ˢ[ a_sub_mode_sk | mode_tc ]
      (pskl_to_uskl pskl_unit) ⩽ (bskl_tophole bskl_unit) }}ad.
  Proof.
    cbn. apply ad_pat_sub__univ_ghost_r;
      [ reflexivity | apply guarded_uskl__unit | apply guarded_bskl__unit
      | apply is_sskl__unit
      | split;
        [ apply ad_pat_consis__unit; reflexivity
        | (* the leaf presupposition, carried by the join *)
          cbn; apply ad_refine_pskl__unit ] ].
  Qed.

  (** ⭐ … and the [P']-side one EXISTS after all: UnivGhostR takes any
      guarded subject, and the flexible is reached through the consistency
      premise's own FlexL. *)
  Lemma ps_concl :
    {{ empty ⨟ psTh ⊢ˢ[ a_sub_mode_sk | mode_tc ]
      (pskl_to_uskl (pskl_var_f α)) ⩽ (bskl_tophole bskl_unit) }}ad.
  Proof.
    cbn. apply ad_pat_sub__univ_ghost_r;
      [ reflexivity | apply guarded_uskl__var | apply guarded_bskl__unit
      | apply is_sskl__unit | ].
    split.
    - apply ad_pat_consis__flex_l with (τ := ptyp_unit);
        [ unfold psTh; eauto | cbn; apply ad_pat_consis__unit; reflexivity ].
    - (* the leaf presupposition: the flexible is reached by refinement's own
         FlexL, exactly as the consistency premise reaches it *)
      cbn. apply ad_refine_pskl__flex_l with (τ := ptyp_unit);
        [ unfold psTh; eauto | cbn; apply ad_refine_pskl__unit ].
  Qed.

End FlexSubjectAtCheck.
