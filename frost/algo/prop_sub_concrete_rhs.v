(** THE EQUIVALENCE P7b's Sub-Check AND Sub-ForallR ACTUALLY NEED.

    `subtyping-proofs.tex:3243` records, inside P7b's Sub-ForallR case, a
    property the authors mark with their own TODO:

        in algo subtyping, when input P_0 is a concrete type, RHS of
        subtyping is always P_0

    ⚠️ THAT IS FALSE — machine-checked, cex/cex_p7_concrete_rhs.v.  Consistency's
    [FlexL] returns the SUBJECT, and algorithmic [Arrow] copies that output into
    its own, so at [P_0 = unit → unit] (concrete, and flexible-FREE) against the
    subject [α̂ → unit] the RHS is [α̂ → unit].

    But the paper's two cases never needed the syntactic reading: both argue via
    the EQUIVALENCE — "P'_0 is equivalent to P_0" (:3181), "P'_0 and P_1 are
    equivalent through Q" (:3238) — and the equivalence is exactly what the run's
    OUTPUT CONTEXT supplies ([α̂ ≔ unit] in the witness).  This file proves that
    reading, on the consistency side, which is what Sub-Check consumes.

    THE RELATION IS ALREADY IN THE DEVELOPMENT.  [a_pskl_tyequiv] (≡ˢ,
    def_meta.v:172) is "the [a_tyequiv] equational theory lifted to skeletons:
    definitions of flexible variables unfold, ghosts are inert".  It was
    introduced for [a_inc]'s GMM-style SEMANTIC middles, and it is precisely the
    relation the two rows that break syntactic equality live in.

    THE PROOF IS ON THE REFINEMENT, NOT ON CONSISTENCY.  [a_consis_sound]
    already exports [Θ1 ⨟ ∅ ⊢ᵣᵃ inh{P0} ⊳ Qt] with [⌊Qt⌋ = P'] — the output
    REFINES FROM the input skeleton — so all that is left is: refinement out of
    a GHOST-FREE source only ever unfolds definitions.  That is one induction
    with no context threading at all, because refinement keeps its context
    fixed (the one row that extends it, [__tophole_fill], needs a ghost on the
    left and is excluded). *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_extra.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.ltac_utils.      (* destruct_if *)
Require Import src.frost.prop_basic.        (* bskl_to_pskl_pskl_to_bskl_{syn,inh} *)
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.     (* ≡ˢ *)
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.prop_precise.   (* bskl_to_pskl_open *)
Require Import src.frost.algo.prop_pat_sub.   (* {pskl,bskl}_ghost_free *)
Require Import src.frost.algo.prop_consis_sound.  (* a_consis_sound *)

Set Implicit Arguments.

(* ===================================================================== *)
(*  §1  Ghost-freeness of the paintings the flexible-lookup rows land on   *)
(* ===================================================================== *)

(** A TYPE has no ghosts, whatever it is — no monotype side condition, unlike
    [mono_ptyp_to_bskl_syn_ghost_free] (prop_pat_sub.v). *)
Lemma ptyp_to_pskl_ghost_free : forall A, pskl_ghost_free (ptyp_to_pskl A).
Proof. intros A; induction A; cbn; tauto. Qed.

Lemma pskl_to_bskl_syn_ghost_free : forall P,
  pskl_ghost_free P -> bskl_ghost_free (pskl_to_bskl_syn P).
Proof. intros P; induction P; cbn; tauto. Qed.

Lemma ptyp_to_bskl_syn_ghost_free : forall A,
  bskl_ghost_free (ptyp_to_bskl_syn A).
Proof.
  intros A; unfold ptyp_to_bskl_syn;
    apply pskl_to_bskl_syn_ghost_free; apply ptyp_to_pskl_ghost_free.
Qed.

(* ===================================================================== *)
(*  §2  REFINEMENT OUT OF A GHOST-FREE SOURCE ONLY UNFOLDS DEFINITIONS     *)
(*                                                                        *)
(*  Read the rows.  [__unit] / [__var] are identities; [__arrow] / [__all] *)
(*  are congruences; [__hole] and the three [__tophole_*] rows all demand  *)
(*  a GHOST on the left and are excluded outright.  That leaves exactly    *)
(*  the two flexible-lookup rows — and those are [a_pskl_tyequiv__flex_def] *)
(*  verbatim, one on each side.                                           *)
(* ===================================================================== *)

Lemma ad_refine_syn_ghost_free_equiv : forall Θ Δ Q' Q,
  Θ ⨟ Δ ⊢ᵣᵃ Q' ⊳ Q ->
  bskl_ghost_free Q' ->
  Θ ⊢ (bskl_to_pskl Q') ≡ˢ (bskl_to_pskl Q).
Proof.
  intros Θ Δ Q' Q H; induction H; intros Hgf; cbn in Hgf |- *.
  - (* unit *) apply a_pskl_tyequiv__refl; apply lc_pskl_unit.
  - (* var *) apply a_pskl_tyequiv__refl; apply lc_pskl_var_f.
  - (* arrow *)
    destruct Hgf as [Hg1 Hg2].
    apply a_pskl_tyequiv__arrow;
      [ apply IHad_refine_syn1 | apply IHad_refine_syn2 ]; assumption.
  - (* all : both sides are inherited ∀s, which ⌊·⌋ paints the same *)
    apply a_pskl_tyequiv__all with (L := L); intros α Hα.
    rewrite <- 2 bskl_to_pskl_open.
    apply H0; [ exact Hα | apply bskl_ghost_free_open_rec; exact Hgf ].
  - (* hole : a GHOST on the left *) tauto.
  - (* tophole_remove *) tauto.
  - (* tophole_fill *) tauto.
  - (* tophole_keep *) tauto.
  - (* flex_l : the source variable unfolds to its definition *)
    eapply a_pskl_tyequiv__trans;
      [ apply a_pskl_tyequiv__flex_def; exact H | ].
    replace (ptyp_to_pskl τ) with (bskl_to_pskl (ptyp_to_bskl_syn τ))
      by (unfold ptyp_to_bskl_syn; apply bskl_to_pskl_pskl_to_bskl_syn).
    apply IHad_refine_syn; apply ptyp_to_bskl_syn_ghost_free.
  - (* flex_r : the TARGET variable does, so the same rule read backwards *)
    eapply a_pskl_tyequiv__trans;
      [ | apply a_pskl_tyequiv__sym; apply a_pskl_tyequiv__flex_def; exact H ].
    replace (ptyp_to_pskl τ) with (bskl_to_pskl (ptyp_to_bskl_syn τ))
      by (unfold ptyp_to_bskl_syn; apply bskl_to_pskl_pskl_to_bskl_syn).
    apply IHad_refine_syn; exact Hgf.
Qed.

Print Assumptions ad_refine_syn_ghost_free_equiv.

(* ===================================================================== *)
(*  §3  WHAT P7b's Sub-Check WILL CITE                                    *)
(*                                                                        *)
(*  The paper's step at :3181 — since P_0 is a concrete type, aconsis     *)
(*  gives that P'_0 is equivalent to P_0 — in the OUTPUT context, which is *)
(*  where the definition the equivalence uses was recorded.                *)
(* ===================================================================== *)

Corollary a_consis_concrete_output_equiv : forall Θ0 P0 P P' Θ1,
  Θ0 ⊢ₐ[ P0 ] P ∼ P' ⊣ Θ1 ->
  a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P ->
  pskl_ghost_free P0 ->                (* the paper's "P_0 is a concrete type" *)
  Θ1 ⊢ P0 ≡ˢ P'.
Proof.
  intros Θ0 P0 P P' Θ1 Hc Hwf HwfP0 HwfP Hgf.
  destruct (a_consis_sound Hc Hwf HwfP0 HwfP)
    as (_ & (Qt & HeQt & _ & Hrs) & _).
  subst P'.
  pose proof (ad_refine_syn_ghost_free_equiv Hrs
                (pskl_to_bskl_inh_ghost_free P0 Hgf)) as Heq.
  rewrite bskl_to_pskl_pskl_to_bskl_inh in Heq. exact Heq.
Qed.

Print Assumptions a_consis_concrete_output_equiv.

(* ===================================================================== *)
(*  §4  THE TWO ≡ˢ TRANSPORTS THE [a_sub]-LEVEL STATEMENT WILL NEED       *)
(*                                                                        *)
(*  ≡ˢ reads the context at ONE rule only ([__flex_def], a [binds] of a    *)
(*  DEFINED flexible), so both transports are one induction with nothing   *)
(*  in them but that lookup.                                              *)
(* ===================================================================== *)

(** (a) MONOTONICITY along [⊴].  This is what [a_sub__arrow] needs: the
    domain's equivalence is read off at Θ1 (§3) but the conclusion lives at
    Θ2.  [a_isub]'s second component — "a definition, once made, is never
    rewritten" (def_meta.v:255) — is exactly and only what the proof uses. *)
Lemma a_pskl_tyequiv_isub_mono : forall Θ P Q,
  Θ ⊢ P ≡ˢ Q ->
  forall Θ', Θ ⊴ Θ' ->
  Θ' ⊢ P ≡ˢ Q.
Proof.
  intros Θ P Q H; induction H; intros Θ' Hle.
  - apply a_pskl_tyequiv__refl; assumption.
  - apply a_pskl_tyequiv__sym; auto.
  - eapply a_pskl_tyequiv__trans; eauto.
  - apply a_pskl_tyequiv__flex_def;
      destruct Hle as [_ Hdef]; eapply Hdef; eassumption.
  - apply a_pskl_tyequiv__arrow; auto.
  - apply a_pskl_tyequiv__all with (L := L); auto.
  - apply a_pskl_tyequiv__tophole; auto.
Qed.

(** …and the plain context extension, for the walk rules of [a_sub_flex]
    ([__depend] / [__skip] / [__skip_rigid] all re-attach a head entry). *)
Lemma a_pskl_tyequiv_weaken : forall Θ P Q,
  Θ ⊢ P ≡ˢ Q ->
  forall Θ', (forall α τ, binds α (abind_flex_mono_def τ) Θ ->
                          binds α (abind_flex_mono_def τ) Θ') ->
  Θ' ⊢ P ≡ˢ Q.
Proof.
  intros Θ P Q H; induction H; intros Θ' Hdef.
  - apply a_pskl_tyequiv__refl; assumption.
  - apply a_pskl_tyequiv__sym; auto.
  - eapply a_pskl_tyequiv__trans; eauto.
  - apply a_pskl_tyequiv__flex_def; eapply Hdef; eassumption.
  - apply a_pskl_tyequiv__arrow; auto.
  - apply a_pskl_tyequiv__all with (L := L); auto.
  - apply a_pskl_tyequiv__tophole; auto.
Qed.

(** (b) SUBSTITUTING A DEFINITION IS INVISIBLE TO ≡ˢ.  This is what
    [a_sub_flex__assign] needs: its premise runs at [P0[τ/β̂]] while the
    conclusion is about [P0], and the two are related by exactly the rule
    that records the definition. *)
Lemma mono_ptyp_to_pskl_lc : forall τ, mono_ptyp τ -> lc_pskl (ptyp_to_pskl τ).
Proof.
  intros τ H; induction H; cbn;
    [ apply lc_pskl_unit | apply lc_pskl_var_f | apply lc_pskl_arrow; assumption ].
Qed.

Lemma a_pskl_tyequiv_subst_flex_def : forall Θ β τ P,
  binds β (abind_flex_mono_def τ) Θ ->
  mono_ptyp τ ->            (* what [a_wf_aenv_binds_def_mono] gives at any call site *)
  lc_pskl P ->
  Θ ⊢ P ≡ˢ (subst_pskl_in_pskl (ptyp_to_pskl τ) β P).
Proof.
  intros Θ β τ P Hb Hm Hlc; induction Hlc; cbn.
  - (* unit *) apply a_pskl_tyequiv__refl; apply lc_pskl_unit.
  - (* var *)
    destruct_if; [ subst; apply a_pskl_tyequiv__flex_def; exact Hb | ].
    apply a_pskl_tyequiv__refl; apply lc_pskl_var_f.
  - (* arrow *) apply a_pskl_tyequiv__arrow; assumption.
  - (* all *)
    apply a_pskl_tyequiv__all with (L := singleton β); intros α Hα.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ apply H0
      | clear - Hα; intro Heq; subst; fsetdec
      | apply mono_ptyp_to_pskl_lc; exact Hm ].
  - (* hole *) apply a_pskl_tyequiv__refl; apply lc_pskl_hole.
  - (* tophole *) apply a_pskl_tyequiv__tophole; assumption.
Qed.

Print Assumptions a_pskl_tyequiv_subst_flex_def.

(** ⚠️ STILL OPEN, and it is the OTHER half: the [a_sub]-level statement
    Sub-ForallR needs (the paper's "P'_0 and P_1 are equivalent through Q",
    :3238).  It is a MUTUAL induction with [a_sub_flex], and §4 supplies the two
    transports that make it more than a transcription of §2:

    - [a_sub__arrow] threads [Θ0 → Θ1 → Θ2], so the domain's equivalence — read
      off at Θ1 by §3 — has to be transported to Θ2: [a_pskl_tyequiv_isub_mono],
      whose [⊴] premise is [a_consis_sound]'s first conjunct.
    - [a_sub_flex__assign] runs its premise at [P0[τ/β̂]], not at [P0], so the IH
      returns an equivalence about the SUBSTITUTED skeleton; the gap closes by
      [a_pskl_tyequiv_subst_flex_def], at the definition the rule walked past.
      (Ghost-freeness survives the substitution: [ptyp_to_pskl τ] has no ghosts,
      §1.)  The walk rows re-attach a head entry, which is
      [a_pskl_tyequiv_weaken].

    What is left to build is the induction itself and its wf threading: the
    statement needs [Θ0 ⨟ ∅ ⊢ₚₛᵃ P0] and [⊢ₚₛᵃ P] at every step, i.e. the
    [a_sub]-side preservation facts, plus [Θ1 ⊴ Θ2] out of the [a_sub] premise
    of [__arrow] (the consistency side has it from [a_consis_sound]). *)
