(** ⚠️ "A SYNTHESISED COUNTERPART TURNS CONSISTENCY INTO A PRECISION" IS FALSE —
    and what rescues P7b is the mechanization's OWN third solution premise.

    DESIGN-completeness-subtyping.md §9.1.1 identified the lemma that P7b's
    Sub-Infer and Sub-UnivGhostR rows share.  Both carry [is_sskl Q] on the rule
    and both return the input skeleton at the input context, so all that is left
    of either case is

        Ψ ⨟ Θ ⊢ₛᵃ R ∼ Q  →  is_sskl Q  →  Θ ⨟ Δ ⊢ₚₛᵃ ⌊Q⌋
          →  a_wf_aenv Θ  →  Θ ⨟ Δ ⊢ₚᵣᵃ ⌊R⌋ˢ ⊑ ⌊Q⌋

    the paper's step at :3181 / :3288.  It does not hold.

    THE WITNESS, and the one line of it that matters.  Take

        R = ∀◇.  (a ∀ whose body is the GHOST)      Q = ∀α. α

    Consistency relates them: its ∀ rule opens BOTH sides at a fresh α and puts
    that α into Θ, after which the [__hole] row fills the ghost with α — legal,
    because α IS in the context there.

    Precision cannot.  Refinement opens a ∀ into Δ, not Θ
    ([ad_refine_syn__all] descends at [add α Δ] with Θ FIXED), and its ghost-fill
    row [__hole] requires the fill to be well formed at [Θ ⨟ ∅] — where a
    Δ-variable is not in scope.  So the ∀-body obligation [◇ ⊑ α] is
    underivable, and with it the whole precision.

    That asymmetry is not an accident of the encoding: it is the SAME
    Θ-versus-Δ asymmetry that forces the F-indexed mirror [ad_refine_syn_f] to
    exist at all (prop_consis_sound.v:346, "a set F forbidden in ghost fills").

    ✅ WHAT RESCUES P7b.  The second theorem below: on this witness the
    mechanization's THIRD solution premise — the SUBJECT's own refinement, which
    DESIGN §1 added as "lesson 1" and which the paper does not state — is
    UNSATISFIABLE, for exactly the same reason.  So the configuration never
    reaches Sub-Infer or Sub-UnivGhostR, and the shared lemma should be restated
    with that premise rather than dropped.  It then stops being a fact about
    consistency at all and becomes a COLOUR bridge from [ad_refine_pskl_f] to
    [ad_precise_f], with consistency supplying only what the bridge's own ghost
    rows need. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_extra.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.prop_precise.        (* ad_precise *)
Require Import src.frost.algo.prop_consis_sound.   (* ad_refine_pskl_f *)

Set Implicit Arguments.

(* ===================================================================== *)
(*  The witness — [∀◇.] against [∀α. α], over the EMPTY context            *)
(* ===================================================================== *)

(** Subject: a ∀ whose body is the ghost. *)
Definition Rw : uskl := uskl_all_syn uskl_hole.

(** Counterpart: the synthesised [∀α. α]. *)
Definition Qw : bskl := bskl_all_syn (bskl_var_b 0).

Lemma Qw_sskl : is_sskl Qw.
Proof.
  apply is_sskl__all with (L := empty); intros α _; cbn; apply is_sskl__var.
Qed.

Lemma Qw_erase_wf : forall Δ, nil ⨟ Δ ⊢ₚₛᵃ (bskl_to_pskl Qw).
Proof.
  intros Δ; cbn.
  apply a_wf_pskl__all with (L := empty); intros α _; cbn.
  apply a_wf_pskl__var; left; clear; fsetdec.
Qed.

(** Consistency DOES relate them: its ∀ rule puts the fresh binder into Θ, and
    the ghost is then filled with that very binder. *)
Lemma cex_consis : empty ⨟ nil ⊢ₛᵃ Rw ∼ Qw.
Proof.
  unfold Rw, Qw.
  apply ad_pat_consis__forall_syn with (L := empty); intros α _; cbn.
  change (bskl_var_f α) with (pskl_to_bskl_inh (pskl_var_f α)).
  apply ad_pat_consis__hole;
    [ clear; fsetdec
    | apply a_wf_pskl__var; right; left; simpl; auto ].
Qed.

(* ===================================================================== *)
(*  …and precision does not: the ∀-body obligation is [◇ ⊑ α] with α in Δ  *)
(*                                                                        *)
(*  Both directions below are the SAME two-row inversion — [__hole], whose *)
(*  fill is checked at [Θ ⨟ ∅], and [__flex_r], which needs a definition   *)
(*  in Θ.  Either way the variable must be bound in the CONTEXT, which a   *)
(*  Δ-binder is not.                                                      *)
(* ===================================================================== *)

Lemma refine_syn_hole_var : forall Θ Δ Qs Qt,
  Θ ⨟ Δ ⊢ᵣᵃ Qs ⊳ Qt ->
  Qs = bskl_hole ->
  forall α, Qt = bskl_var_f α ->
  a_binds_tvar α Θ.
Proof.
  intros Θ Δ Qs Qt H; induction H; intros Heqs α0 Heqt;
    try discriminate Heqs; try discriminate Heqt.
  - (* __hole : the fill IS the variable, and it is checked at [Θ ⨟ ∅] *)
    destruct P; cbn in Heqt; try discriminate Heqt.
    inversion Heqt; subst.
    inversion H as [ | Θv Δv αv Hd | | | | ]; subst.
    destruct Hd as [HΔ | Htv]; [ clear - HΔ; fsetdec | exact Htv ].
  - (* __flex_r : a DEFINITION in Θ *)
    inversion Heqt; subst. right; right; exists τ; assumption.
Qed.

Lemma refine_pskl_f_hole_var : forall F Θ Δ Ps Pt,
  ad_refine_pskl_f F Θ Δ Ps Pt ->
  Ps = pskl_hole ->
  forall α, Pt = pskl_var_f α ->
  a_binds_tvar α Θ.
Proof.
  intros F Θ Δ Ps Pt H; induction H; intros Heqs α0 Heqt;
    try discriminate Heqs; try discriminate Heqt.
  - (* __hole *)
    subst.
    inversion H0 as [ | Θv Δv αv Hd | | | | ]; subst.
    destruct Hd as [HΔ | Htv]; [ clear - HΔ; fsetdec | exact Htv ].
  - (* __flex_r *)
    inversion Heqt; subst. right; right; exists τ; assumption.
Qed.

Lemma cex_not_precise : forall Δ,
  ~ nil ⨟ Δ ⊢ₚᵣᵃ (uskl_to_pskl Rw) ⊑ (bskl_to_pskl Qw).
Proof.
  intros Δ H; unfold ad_precise, Rw, Qw in H; cbn in H.
  inversion H as [ | | | L Θa Δa Qa Pa Hfam | | | | | | ]; subst.
  pick fresh α for L.
  specialize (Hfam α ltac:(clear - Fr; fsetdec)); cbn in Hfam.
  pose proof (@refine_syn_hole_var _ _ _ _ Hfam eq_refl α eq_refl) as Hb.
  destruct Hb as [Hb | [Hb | [τ Hb]]]; inversion Hb.
Qed.

(* ===================================================================== *)
(*  The refutation                                                        *)
(* ===================================================================== *)

Definition p7_sskl_precise_property : Prop :=
  forall Ψ Θ R Q,
    Ψ ⨟ Θ ⊢ₛᵃ R ∼ Q ->
    a_wf_aenv Θ ->
    is_sskl Q ->
    forall Δ, Θ ⨟ Δ ⊢ₚₛᵃ (bskl_to_pskl Q) ->
    Θ ⨟ Δ ⊢ₚᵣᵃ (uskl_to_pskl R) ⊑ (bskl_to_pskl Q).

Theorem p7_sskl_precise_is_false : ~ p7_sskl_precise_property.
Proof.
  intros Hprop.
  apply (@cex_not_precise empty).
  apply (Hprop empty nil Rw Qw cex_consis a_wf_aenv__nil Qw_sskl empty
               (Qw_erase_wf empty)).
Qed.

(* ===================================================================== *)
(*  …and why P7b is NOT affected: the third solution premise excludes it   *)
(* ===================================================================== *)

(** The mechanization's third premise (DESIGN §1, "lesson 1") asks the SUBJECT
    to refine to the counterpart's erasure.  On this witness it cannot: the
    obligation is again [◇ ⊳ α] with the binder in Δ, and refinement's ghost
    fill is checked at [Θ ⨟ ∅].  So the configuration never reaches Sub-Infer
    or Sub-UnivGhostR at all. *)
Theorem cex_excluded_by_subject_refinement : forall F Δ,
  ~ ad_refine_pskl_f F nil Δ (uskl_to_pskl Rw) (bskl_to_pskl Qw).
Proof.
  intros F Δ H; unfold Rw, Qw in H; cbn in H.
  inversion H as [ | | | L Θa Δa Pa Qa Hfam | | | | | | ]; subst.
  pick fresh α for L.
  specialize (Hfam α ltac:(clear - Fr; fsetdec)); cbn in Hfam.
  pose proof (@refine_pskl_f_hole_var _ _ _ _ _ Hfam eq_refl α eq_refl) as Hb.
  destruct Hb as [Hb | [Hb | [τ Hb]]]; inversion Hb.
Qed.

Print Assumptions p7_sskl_precise_is_false.
Print Assumptions cex_excluded_by_subject_refinement.
