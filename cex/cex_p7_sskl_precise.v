(** ⚠️ A TEMPTING SHORTCUT IS FALSE — but the PAPER does not take it.

    RETRACTION FIRST.  An earlier version of this header said this refutes
    `thm:complete-subtyping`'s Sub-Infer / Sub-UnivGhostR step.  It does not.
    The paper (subtyping-proofs.tex:3134) says

      "The consistency premise, together with ⌊S⌋ = P and
       Cref{thm:complete-consistency}, gives Θ ⊢ precise{θP}{Q}."

    — i.e. it invokes thm:complete-consistency, a THEOREM (mechanized as
    [a_consis_complete]), on the consistency problem (Θ0; □; P).  That route
    is sound, and all it needs besides the theorem is
    [a_consis_ghost_p0_output] (prop_sub_complete_thm.v, Qed): at [P0 = □] the
    algorithmic consistency OUTPUT is the SUBJECT, so the theorem's precision —
    which is about the run's output — IS a precision about [P].

    WHAT IS ACTUALLY REFUTED, then, is the SHORTCUT: proving that precision
    directly from the consistency premise, without going through completeness.

        {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad  →  is_sskl Q  →  {{ Θ ⨟ Δ ⊢ₚₛ ⌊Q⌋ }}a
          →  {{ ⊢ Θ }}a  →  {{ Θ ⨟ Δ ⊢ₚᵣ ⌊R⌋ˢ ⊑ ⌊Q⌋ }}ad

    THE WITNESS.  Take [R = ∀◇.] (a ∀ whose body is the GHOST) and [Q = ∀α. α].
    Consistency relates them: its ∀ rule opens BOTH sides at a fresh α and puts
    that α into Θ, after which the [__ghost] row fills the ghost with α — legal,
    because α IS in the context there.  Precision cannot: refinement opens a ∀
    into Δ as well as Θ ([ad_refine_syn__all] descends at
    [(α ~ tvar) ++ Θ ⨟ add α Δ]), and its ghost-fill row requires the fill to
    avoid Δ ([Δ ∩ ftv fill [=] ∅]) — which a Δ-variable does not.  So
    [◇ ⊑ α] is underivable, and with it the whole precision.  (Re-checked
    2026-10-08 under the paper-faithful refinement rules: the claim stands;
    only the reason moved from "α not in scope" to "α ∈ Δ".)

    That asymmetry is not an encoding artefact: it is the Θ-versus-Δ
    asymmetry of the paper's own rules (consistency binds a ∀ in Θ only,
    refinement in Θ and Δ).

    The second theorem below shows the mechanization's THIRD solution premise —
    the SUBJECT's own refinement, DESIGN §1's "lesson 1", which the paper does
    not state — is UNSATISFIABLE on this witness.  So the shortcut could be
    RESCUED by threading that premise; it is simply not needed, because
    completeness of consistency already gets there.  Kept as a standing warning:
    the shortcut looks available and is not. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.def_shapes.
Require Import src.fresco.coercions.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo.prop_precise.        (* ad_precise *)
Require Import src.fresco.algo.consis.prop_soundness_consis.

Set Implicit Arguments.

(* ===================================================================== *)
(*  The witness — [∀◇.] against [∀α. α], over the EMPTY context            *)
(* ===================================================================== *)

(** Subject: a ∀ whose body is the ghost. *)
Definition Rw : uskl := uskl_all_syn uskl_ghost.

(** Counterpart: the synthesised [∀α. α]. *)
Definition Qw : bskl := bskl_all_syn (bskl_var_b 0).

Lemma Qw_sskl : is_sskl Qw.
Proof.
  apply is_sskl__all with (L := empty); intros α _; cbn; apply is_sskl__var.
Qed.

Lemma Qw_erase_wf : forall Δ, {{ nil ⨟ Δ ⊢ₚₛ (bskl_to_pskl Qw) }}a.
Proof.
  intros Δ; cbn.
  apply a_wf_pskl__all with (L := empty); intros α _; cbn.
  apply a_wf_pskl__var; left; simpl; auto.
Qed.

(** Consistency DOES relate them: its ∀ rule puts the fresh binder into Θ, and
    the ghost is then filled with that very binder. *)
Lemma cex_consis : {{ empty ⨟ nil ⊢ˢ Rw ∼ Qw }}ad.
Proof.
  unfold Rw, Qw.
  apply ad_pat_consis__forall_syn with (L := empty); intros α _; cbn.
  change (bskl_var_f α) with (pskl_to_bskl_inh (pskl_var_f α)).
  apply ad_pat_consis__ghost;
    [ clear; fsetdec
    ].
Qed.

(* ===================================================================== *)
(*  …and precision does not: the ∀-body obligation is [◇ ⊑ α] with α in Δ  *)
(*                                                                        *)
(*  Both directions below are the SAME two-row inversion — [__ghost], whose *)
(*  fill must avoid Δ, and [__flex_r], which needs a flexible definition   *)
(*  in Θ.  A ∀-binder is in Δ and bound as a plain tvar, so neither fires. *)
(* ===================================================================== *)

Lemma refine_syn_ghost_var : forall Θ Δ Qs Qt,
  {{ Θ ⨟ Δ ⊢ᵣ Qs ⊳ Qt }}ad ->
  Qs = bskl_ghost ->
  forall α, Qt = bskl_var_f α ->
  α `notin` Δ \/ exists τ, binds α (abind_flex_mono_def τ) Θ.
Proof.
  intros Θ Δ Qs Qt H; induction H; intros Heqs α0 Heqt;
    try discriminate Heqs; try discriminate Heqt.
  - (* __ghost : the fill IS the variable, and it must avoid Δ *)
    destruct P; cbn in Heqt; try discriminate Heqt.
    inversion Heqt; subst. left; intros Hin.
    assert (Hx : α0 `in` (Δ ∩ ftvar_in_pskl (pskl_var_f α0)))
      by (cbn; clear - Hin; fsetdec).
    rewrite H in Hx; clear - Hx; fsetdec.
  - (* __flex_r : a DEFINITION in Θ *)
    inversion Heqt; subst. right; exists τ; assumption.
Qed.

Lemma refine_pskl_ghost_var : forall Θ Δ Ps Pt,
  {{ Θ ⨟ Δ ⊢ᵣₚ Ps ⊳ Pt }}ad ->
  Ps = pskl_ghost ->
  forall α, Pt = pskl_var_f α ->
  α `notin` Δ \/ exists τ, binds α (abind_flex_mono_def τ) Θ.
Proof.
  intros Θ Δ Ps Pt H; induction H; intros Heqs α0 Heqt;
    try discriminate Heqs; try discriminate Heqt.
  - (* __ghost : the fill must avoid Δ *)
    subst. left; intros Hin.
    assert (Hx : α0 `in` (Δ ∩ ftvar_in_pskl (pskl_var_f α0)))
      by (cbn; clear - Hin; fsetdec).
    rewrite H in Hx; clear - Hx; fsetdec.
  - (* __flex_r *)
    inversion Heqt; subst. right; exists τ; assumption.
Qed.

Lemma cex_not_precise : forall Δ,
  ~ {{ nil ⨟ Δ ⊢ₚᵣ (uskl_to_pskl Rw) ⊑ (bskl_to_pskl Qw) }}ad.
Proof.
  intros Δ H; unfold ad_precise, Rw, Qw in H; cbn in H.
  inversion H as [ | | | L Θa Δa Qa Pa Hia Hfam | | | | | | ]; subst.
  pick fresh α for L.
  specialize (Hfam α ltac:(clear - Fr; fsetdec)); cbn in Hfam.
  pose proof (@refine_syn_ghost_var _ _ _ _ Hfam eq_refl α eq_refl) as Hb.
  destruct Hb as [Hb | [τ Hb]];
    [ apply Hb; clear; fsetdec
    | apply binds_cons_1 in Hb; destruct Hb as [[_ Hb] | Hb];
      [ discriminate Hb | inversion Hb ] ].
Qed.

(* ===================================================================== *)
(*  The refutation                                                        *)
(* ===================================================================== *)

Definition p7_sskl_precise_property : Prop :=
  forall Ψ Θ R Q,
    {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
    {{ ⊢ Θ }}a ->
    is_sskl Q ->
    forall Δ, {{ Θ ⨟ Δ ⊢ₚₛ (bskl_to_pskl Q) }}a ->
    {{ Θ ⨟ Δ ⊢ₚᵣ (uskl_to_pskl R) ⊑ (bskl_to_pskl Q) }}ad.

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
    fill must avoid Δ.  So the configuration never reaches Sub-Infer
    or Sub-UnivGhostR at all. *)
Theorem cex_excluded_by_subject_refinement : forall Δ,
  ~ {{ nil ⨟ Δ ⊢ᵣₚ (uskl_to_pskl Rw) ⊳ (bskl_to_pskl Qw) }}ad.
Proof.
  intros Δ H; unfold Rw, Qw in H; cbn in H.
  inversion H as [ | | | L Θa Δa Pa Qa Hfam | | | | | | ]; subst.
  pick fresh α for L.
  specialize (Hfam α ltac:(clear - Fr; fsetdec)); cbn in Hfam.
  pose proof (@refine_pskl_ghost_var _ _ _ _ Hfam eq_refl α eq_refl) as Hb.
  destruct Hb as [Hb | [τ Hb]];
    [ apply Hb; clear; fsetdec
    | apply binds_cons_1 in Hb; destruct Hb as [[_ Hb] | Hb];
      [ discriminate Hb | inversion Hb ] ].
Qed.

