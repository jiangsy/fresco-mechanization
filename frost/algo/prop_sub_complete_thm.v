(** P7 — COMPLETENESS OF SUBTYPING.  THE MOTIVE, LOCKED.

    This file carries the two motives of the P7 bundle and nothing else yet.
    DESIGN-completeness-subtyping.md §1 says to LOCK the motive before writing
    the induction (it is the μ-bundle lesson), and §9 fixes the shape:

    | | mech name | paper | measure |
    |---|---|---|---|
    | P7a | [a_sub_flex_complete] | lemma:complete-flex-subtyping (:2836) | the contexts [Θ0 ∣ Ξ] |
    | P7b | [a_sub_complete_gen]  | generalised thm:complete-subtyping (:3050) | lex(fuel, ∣Ψ∣) |
    | P7c | [a_sub_complete_thm]  | thm (algorithmic.tex:1446) | instantiate R := P, Ψ := ∅ |

    P7a's proof is "by induction on the contexts of the subtyping judgement,
    MUTUALLY with the generalised version of thm:complete-subtyping below", and
    P7b's [P = α̂ ∧ M = FN M'] case calls P7a at [Ξ = ·].  So they are ONE
    bundle; [a_consis_complete_thm]'s 3-way mutual block is the shape precedent.

    THREE DECISIONS, and two of them CORRECT DESIGN §1 as written.

    (1) THE FUEL JUDGMENT IS [ad_pat_sub_g], NOT [ad_pat_sub_n].  §1's skeleton
        named [ad_pat_sub_n]; the development settled on the TAG-HYGIENIC fuel
        mirror instead (def_decl_algo_sub_hyg.v), because precision-substitution
        — which the ForallL case applies to its premise to get the derivation it
        hands the IH — is FALSE over [_n] (the paper's "fresh Ψ'" means GLOBALLY
        fresh, and [_n] renders it only as freshness from the tag context, which
        does not survive the Arrow split).  P5's [ad_pat_sub_precise_upre] and
        ALL FIVE P6 lemmas are stated over [_g], so P7 must be too.

    (2) THE CONCLUSION KEEPS [a_consis_complete_thm]'s FACTORED SHAPE — the
        [forall κ1, is_id_msubst κ1 → … → exists ζ] wrapper — rather than the
        paper's flat [exists θ1].  This is not a stylistic choice and it is
        not optional: [a_inc_equiv] is POSITIONAL (def_meta.v:268 pairs the two
        metasubstitutions' entries key-by-key against Θ0's entries), so a flat
        [a_inc_equiv Θ0 κ ζ Θ] with [ζ ∷ Θ1 ⊑ Θ] is not even the right shape —
        ζ is keyed by Θ1, which has entries Θ0 does not, and (at Flex-Solve)
        in the middle rather than at the end.  The factored form says the same
        thing the paper's [inc[θ≡θ1]{Θ0}{Θ}] does while staying well-formed:
        the restriction of ζ along an identity κ1 is what is compared to κ.
        Four of P7b's seven cases are applications of [a_consis_complete_thm],
        and they pass this conclusion straight through.

    (3) THE THIRD SOLUTION PREMISE STAYS (§1's "lesson 1"): besides the
        subtyping derivation and the P0-fill, the SUBJECT's own refinement
        [⊢ᵣₚᵃ κ⌊R⌋ˢ ⊳ ⌊Q⌋].  It is exactly what [a_consis_sound] /
        [a_sub_sound_thm] PRODUCE for every algorithmic output, so the
        sound/complete pair still characterises the algorithm exactly.

    The wf / mode premises are P6-L's and [a_sub_sound_thm]'s verbatim, which is
    what lets the two be composed without re-deriving side conditions. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_extra.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.
Require Import src.frost.prop_basic.              (* bskl_to_pskl_pskl_to_bskl_{syn,inh} *)
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo_sub.
Require Import src.frost.algo.def_decl_algo_sub_hyg.
Require Import src.frost.algo.prop_refine.        (* lc_pskl_to_bskl_inh *)
Require Import src.frost.algo.prop_consis_complete. (* ad_precise_f *)
Require Import src.frost.algo.prop_consis_precise. (* pskl_no_forall *)
Require Import src.frost.algo.prop_metasubst.     (* opt_axiom_factor *)
Require Import src.frost.algo.prop_precise.       (* ad_precise, ⊢ₚᵣᵃ *)
Require Import src.frost.algo.prop_flex.          (* a_decls *)
Require Import src.frost.algo.prop_consis_sound.  (* ad_refine_{syn,pskl}_f *)

Set Implicit Arguments.

(* ===================================================================== *)
(*  P7b — the generalised thm:complete-subtyping (subtyping-proofs:3054)   *)
(* ===================================================================== *)

(** Given a subtyping problem [(Θ0;N;M;P0;P)], a tag context Ψ, an unresolved
    skeleton [R] with [⌊R⌋ˢ = P], and a solution [(κ ∷ Θ0 ⊑ Θ ; Q)], the
    algorithm succeeds and its output is ⊑-optimal.

    [n] is the fuel of the declarative derivation — the paper's "derivation
    height of [typsub]" — and the induction is lex([n], |Ψ|).  The ForallL case
    is why it must be fuel and not structure: its IH is applied to the
    derivation PRODUCED by precision-substitution, which is no structural
    sub-derivation of the conclusion, but which precision-substitution
    preserves the fuel of exactly. *)
Definition sub_complete_concl
  (n : nat) (NM : a_sub_mode) (M : mode)
  (Θ0 : aenv) (P0 P : pskl) (R : uskl) (Ψ : atoms)
  (Θ : aenv) (κ : metasubst) (Q : bskl) : Prop :=
  (* ---- inputs are well formed, and mode-compatible with P0 ---- *)
  a_wf_aenv Θ0 -> a_wf_aenv Θ ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->   (* skmod[SK]{P0}{M} *)
  (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->   (* skmod[TY]{P0}{M} *)
  (* ---- the unresolved subject erases to the algorithm's input ---- *)
  ⌊ R ⌋ˢ = P ->
  (* ---- the solution: an increase, and its three conditions ---- *)
  κ ∷ Θ0 ⊑ Θ ->
  ad_pat_sub_g n NM M Ψ Θ (msubst_uskl_syn κ R) Q ->
  ad_refine_syn_f empty Θ empty (pskl_to_bskl_inh (msubst_pskl κ P0)) Q ->
  ad_refine_pskl_f empty Θ empty (msubst_pskl κ P) (bskl_to_pskl Q) ->
  (* ---- the algorithm succeeds, and its solution is the least ---- *)
  exists P1 Θ1,
    a_sub NM M P0 Θ0 P P1 Θ1 /\
    (forall κ1, is_id_msubst κ1 -> κ1 ∷ Θ0 ⊑ Θ1 ->
       exists ζ,
         ζ ∷ Θ1 ⊑ Θ /\
         a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ /\
         Θ ⨟ empty ⊢ₚᵣᵃ
           (msubst_bskl ζ (pskl_to_bskl_syn P1)) ⊑ (bskl_to_pskl Q)).

(* ===================================================================== *)
(*  P7a — lemma:complete-flex-subtyping (subtyping-proofs:2836)            *)
(* ===================================================================== *)

(** The flexible-variable half.  The subject is the bare flexible [α̂], so the
    declarative premise is about its IMAGE [κα̂] — a MONOTYPE, painted into the
    subject sort; there is no [R] and no erasure premise.

    THE CONTEXT IS SPLIT.  [a_sub_flex NM M P0 Θ0 Ξ α P1 Θ1] keeps the
    entries the flex walk has already passed in [Ξ] and the rest in [Θ0]; the
    FULL context is [Ξ ++ Θ0] (check [a_sub_flex__depend]: its conclusion is at
    [(β~flex) ++ Θ0] with suffix [Ξ], its premise at [Θ0] with suffix
    [Ξ ++ (β~flex)] — the same list either way).  [a_sub__flex_mono] enters at
    [Ξ = ·], which is the paper's [Θ0 ∣ ·].

    The measure is the CONTEXT [Θ0 ∣ Ξ]: the walk rules shrink [Θ0] at fixed
    fuel, and Flex-Solve / Flex-Assign re-enter P7b at fuel ≤ n (their subtyping
    premise comes from Arrow-inversion, so strictly smaller).  Combined:
    lex(n, |Θ0|). *)
Definition sub_flex_complete_concl
  (n : nat) (NM : a_sub_mode) (M : mode)
  (Θ0 Ξ : aenv) (α : atom) (P0 : pskl) (Ψ : atoms)
  (Θ : aenv) (κ : metasubst) (Q : bskl) : Prop :=
  a_decls Ξ ->                                  (* Ξ holds only flexible decls *)
  a_wf_aenv (Ξ ++ Θ0) -> a_wf_aenv Θ ->
  (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P0 ->
  a_flex_tvar (Ξ ++ Θ0) α ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat (mode_fn M) P0) ->
  (NM = a_sub_mode_ty -> a_ty_mode_compat (mode_fn M) P0) ->
  κ ∷ (Ξ ++ Θ0) ⊑ Θ ->
  (* the subject is [syn{κα̂}] — a monotype painting, not an unresolved R *)
  ad_pat_sub_g n NM (mode_fn M) Ψ Θ
    (ptyp_to_uskl_syn (msubst_lookup κ α)) Q ->
  ad_refine_syn_f empty Θ empty
    (pskl_to_bskl_inh (msubst_pskl κ P0)) Q ->
  ad_refine_pskl_f empty Θ empty
    (ptyp_to_pskl (msubst_lookup κ α)) (bskl_to_pskl Q) ->
  exists P1 Θ1,
    a_sub_flex NM M P0 Θ0 Ξ α P1 Θ1 /\
    (forall κ1, is_id_msubst κ1 -> κ1 ∷ (Ξ ++ Θ0) ⊑ Θ1 ->
       exists ζ,
         ζ ∷ Θ1 ⊑ Θ /\
         a_inc_equiv (Ξ ++ Θ0) κ (msubst_compose ζ κ1) Θ /\
         Θ ⨟ empty ⊢ₚᵣᵃ
           (msubst_bskl ζ (pskl_to_bskl_syn P1)) ⊑ (bskl_to_pskl Q)).

(* ===================================================================== *)
(*  The bundle's statement, for reference while the cases are written      *)
(* ===================================================================== *)

(** What the induction will establish — named after
    [a_sub_decorate_bundle] (prop_decorate_key.v), the house shape for a
    two-half [a_sub] / [a_sub_flex] statement.  Both halves are quantified over
    the SAME fuel [n], and the lexicographic order is (n, |Θ0|) — see the note
    on [sub_flex_complete_concl]. *)
Definition a_sub_complete_bundle : Prop :=
  forall n,
    (forall NM M Θ0 P0 P R Ψ Θ κ Q,
       sub_complete_concl n NM M Θ0 P0 P R Ψ Θ κ Q) /\
    (forall NM M Θ0 Ξ α P0 Ψ Θ κ Q,
       sub_flex_complete_concl n NM M Θ0 Ξ α P0 Ψ Θ κ Q).

(** Sanity: the motives are well formed at the sorts the judgments actually
    use, and the bundle statement elaborates.  (No proof is attempted here —
    this file is the locked motive; the cases live in the follow-up.) *)
Check sub_complete_concl.
Check sub_flex_complete_concl.
Check a_sub_complete_bundle.

(* ===================================================================== *)
(*  THE LEAF PLUMBING — three facts every axiom-node case reuses           *)
(* ===================================================================== *)

(** A syn painting commutes with the metasubstitution.  Both sides agree at
    the only interesting node, a free variable, where each is the syn painting
    of the image. *)
Lemma msubst_bskl_pskl_to_bskl_syn : forall κ P,
  msubst_bskl κ (pskl_to_bskl_syn P) = pskl_to_bskl_syn (msubst_pskl κ P).
Proof. intros κ P; induction P; cbn; f_equal; auto. Qed.

(** [κR = ◇] forces [R = ◇]: a variable's image is a monotype PAINTING, which
    is unit / var / arrow, never a ghost. *)
Lemma msubst_uskl_syn_hole_inv : forall κ R,
  msubst_uskl_syn κ R = uskl_hole -> R = uskl_hole.
Proof.
  intros κ R; destruct R; cbn; try discriminate; [ | reflexivity ].
  unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn.
  destruct (msubst_lookup κ α); cbn; discriminate.
Qed.

(** Against a [◇] SUBJECT the counterpart is an INHERITED painting of its own
    erasure.  Only two consistency rows have that subject: [__hole], whose
    counterpart IS such a painting, and [__flex_r], whose counterpart is a bare
    variable — and a variable is painted the same either way. *)
Lemma ad_pat_consis_hole_target_inh : forall Ψ Θ Q,
  Ψ ⨟ Θ ⊢ₛᵃ uskl_hole ∼ Q ->
  pskl_to_bskl_inh (bskl_to_pskl Q) = Q.
Proof.
  intros Ψ Θ Q H; inversion H; subst;
    [ rewrite bskl_to_pskl_pskl_to_bskl_inh | ]; reflexivity.
Qed.

(** …and the same at the subtyping level.  With [N = SK] and a [◇] subject only
    [__infer] (which hands it to consistency) and [__ghost] (whose counterpart
    is an inherited painting on the rule) can fire: [__univ_ghost_r] wants
    [guarded_uskl ◇], and every other row wants another subject shape or
    [N = TY]. *)
Lemma ad_pat_sub_g_hole_target_inh : forall n M Ψ Θ Q,
  ad_pat_sub_g n a_sub_mode_sk M Ψ Θ uskl_hole Q ->
  pskl_to_bskl_inh (bskl_to_pskl Q) = Q.
Proof.
  intros n M Ψ Θ Q H; inversion H; subst.
  - (* __infer *) eapply ad_pat_consis_hole_target_inh; eassumption.
  - (* __univ_ghost_r : [guarded_uskl ◇] is impossible *)
    match goal with Hg : guarded_uskl uskl_hole |- _ => inversion Hg end.
  - (* __ghost *) rewrite bskl_to_pskl_pskl_to_bskl_inh; reflexivity.
Qed.

(* ===================================================================== *)
(*  P7b, THE ◇-SUBJECT CASE (paper's Sub-Ghost, and Sub-Infer at [N = SK]) *)
(*                                                                        *)
(*  The paper (:3468) does Sub-Ghost as: [P = □]; algorithmic [Ghost] gives *)
(*  [Θ0 ⊢[SK][M][P0] □ ⩽ P0 ⊣ Θ0]; and the refinement premise IS the       *)
(*  precision conclusion "by definition".  Both hold here.                *)
(*                                                                        *)
(*  The case is WIDER THAN ONE RULE.  At [N = SK] a [◇] subject admits      *)
(*  [__infer] as well as [__ghost] — but both algorithmic rules return the  *)
(*  INPUT SKELETON at the INPUT CONTEXT ([a_sub__infer] is [a_sub__ghost]   *)
(*  at [M = TI], since [skmod] forces [P0 = □] there), so one witness       *)
(*  serves both and no inversion is needed for the RUN.  The derivation is  *)
(*  inverted only to learn the counterpart's COLOUR, which the precision    *)
(*  conclusion needs.                                                       *)
(* ===================================================================== *)

Lemma a_sub_complete_ghost : forall n M Θ0 P0 P R Ψ Θ κ Q,
  msubst_uskl_syn κ R = uskl_hole ->
  sub_complete_concl n a_sub_mode_sk M Θ0 P0 P R Ψ Θ κ Q.
Proof.
  intros n M Θ0 P0 P R Ψ Θ κ Q Hsubj.
  unfold sub_complete_concl.
  intros Hwf0 Hwfth HwfP0 HwfP HmodSK HmodTY HeqP Hinc Hsub Hrs Hrp.
  (* the subject is the hole, so the algorithm's input is [□] *)
  pose proof (msubst_uskl_syn_hole_inv κ R Hsubj) as HR; subst R.
  cbn in HeqP; subst P.
  (* the counterpart is an inherited painting — read off the derivation *)
  assert (HQ : pskl_to_bskl_inh (bskl_to_pskl Q) = Q)
    by (rewrite Hsubj in Hsub;
        eapply ad_pat_sub_g_hole_target_inh; exact Hsub).
  (* the run: [Ghost], which returns the input skeleton unchanged *)
  exists P0, Θ0. split; [ apply a_sub__ghost | ].
  intros κ1 Hid Hinc1. exists κ.
  destruct (opt_axiom_factor Hwf0 Hid Hinc1 Hinc) as [Hout Hfact].
  split; [ exact Hout | split; [ exact Hfact | ] ].
  (* precision IS the P0-fill premise, once both sides are repainted *)
  unfold ad_precise.
  rewrite msubst_bskl_pskl_to_bskl_syn.
  rewrite bskl_to_pskl_pskl_to_bskl_syn.
  rewrite HQ.
  eapply ad_refine_syn_f_forget; exact Hrs.
Qed.

Print Assumptions a_sub_complete_ghost.

(* ===================================================================== *)
(*  P7b, THE ◈-SUBJECT CASE (paper's Sub-GhostG)                          *)
(*                                                                        *)
(*  Same shape as the ◇ case and for the same three reasons; only the      *)
(*  subject constructor and the admissible rows change.  ⌊◈⌋ˢ is again     *)
(*  [□], so the algorithm's input is again [□] and [Ghost] again returns    *)
(*  the input skeleton.                                                    *)
(* ===================================================================== *)

Lemma msubst_uskl_syn_holeg_inv : forall κ R,
  msubst_uskl_syn κ R = uskl_holeg -> R = uskl_holeg.
Proof.
  intros κ R; destruct R; cbn; try discriminate; [ | reflexivity ].
  unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn.
  destruct (msubst_lookup κ α); cbn; discriminate.
Qed.

Lemma ad_pat_consis_holeg_target_inh : forall Ψ Θ Q,
  Ψ ⨟ Θ ⊢ₛᵃ uskl_holeg ∼ Q ->
  pskl_to_bskl_inh (bskl_to_pskl Q) = Q.
Proof. intros Ψ Θ Q H; inversion H; subst; reflexivity. Qed.

Lemma ad_pat_sub_g_holeg_target_inh : forall n M Ψ Θ Q,
  ad_pat_sub_g n a_sub_mode_sk M Ψ Θ uskl_holeg Q ->
  pskl_to_bskl_inh (bskl_to_pskl Q) = Q.
Proof.
  intros n M Ψ Θ Q H; inversion H; subst.
  - (* __infer *) eapply ad_pat_consis_holeg_target_inh; eassumption.
  - (* __univ_ghost_r : [guarded_uskl ◈] is impossible *)
    match goal with Hg : guarded_uskl uskl_holeg |- _ => inversion Hg end.
  - (* __ghostg : the counterpart is [◇] on the rule *) reflexivity.
Qed.

Lemma a_sub_complete_ghostg : forall n M Θ0 P0 P R Ψ Θ κ Q,
  msubst_uskl_syn κ R = uskl_holeg ->
  sub_complete_concl n a_sub_mode_sk M Θ0 P0 P R Ψ Θ κ Q.
Proof.
  intros n M Θ0 P0 P R Ψ Θ κ Q Hsubj.
  unfold sub_complete_concl.
  intros Hwf0 Hwfth HwfP0 HwfP HmodSK HmodTY HeqP Hinc Hsub Hrs Hrp.
  pose proof (msubst_uskl_syn_holeg_inv κ R Hsubj) as HR; subst R.
  cbn in HeqP; subst P.
  assert (HQ : pskl_to_bskl_inh (bskl_to_pskl Q) = Q)
    by (rewrite Hsubj in Hsub;
        eapply ad_pat_sub_g_holeg_target_inh; exact Hsub).
  exists P0, Θ0. split; [ apply a_sub__ghost | ].
  intros κ1 Hid Hinc1. exists κ.
  destruct (opt_axiom_factor Hwf0 Hid Hinc1 Hinc) as [Hout Hfact].
  split; [ exact Hout | split; [ exact Hfact | ] ].
  unfold ad_precise.
  rewrite msubst_bskl_pskl_to_bskl_syn.
  rewrite bskl_to_pskl_pskl_to_bskl_syn.
  rewrite HQ.
  eapply ad_refine_syn_f_forget; exact Hrs.
Qed.

Print Assumptions a_sub_complete_ghostg.

(* ===================================================================== *)
(*  WHAT THE REMAINING IH-FREE ROWS NEED.  RETRACTION FIRST.              *)
(*                                                                        *)
(*  An earlier version of this note claimed the lemma below does not hold  *)
(*  as stated, because of a COLOUR mismatch between precision (which       *)
(*  paints ∀s INHERITED on both sides) and refinement (which fills a ghost *)
(*  SYNTHESISED).  THAT WAS WRONG, twice, and both errors are ones this    *)
(*  repo already warns about:                                             *)
(*                                                                        *)
(*   · The ∀◇ row was said to be stuck because                             *)
(*     [ad_refine_syn__tophole_keep] wants [guarded_bskl] of the target's  *)
(*     body, which a NESTED [∀◇] is not.  But a nested [∀◇] is not         *)
(*     WELL-FORMED: [a_wf_pskl__tophole] carries [guarded_pskl] on the     *)
(*     body.  This is exactly docs/WF-SIDE-CONDITIONS.md's rule — check    *)
(*     the paper's EXTERNAL wf before calling anything false.              *)
(*   · The colour difference is REAL but it is not a mismatch: it is       *)
(*     reconciled by [is_sskl], which forbids [bskl_all_inh].  At the      *)
(*     [__hole] row that forces the fill ∀-FREE, where the syn and inh     *)
(*     paintings COINCIDE; at the [__forall_syn] rows the source is a ∀    *)
(*     too, so [ad_refine_syn__all] applies with both sides painted        *)
(*     inherited.  No row actually disagrees.                             *)
(*                                                                        *)
(*  WHICH ROWS SHARE IT — also narrower than first recorded.  [__infer]    *)
(*  and [__univ_ghost_r] both carry [is_sskl Q] ON THE RULE, and their     *)
(*  algorithmic counterparts return the INPUT skeleton (or [∀◇.] of it) at *)
(*  the INPUT context, so [ζ := κ] + [opt_axiom_factor] leave only         *)
(*                                                                        *)
(*      Ψ ⨟ Θ ⊢ₛᵃ R ∼ Q  →  is_sskl Q  →  Θ ⨟ Δ ⊢ₚₛᵃ ⌊Q⌋                 *)
(*        →  a_wf_aenv Θ  →  ⌊R⌋ˢ ⊑ ⌊Q⌋                                   *)
(*                                                                        *)
(*  Sub-Check is NOT one of them: its counterpart is [pskl_to_bskl_inh B]  *)
(*  for a merely GUARDED B, which is [is_sskl] only when B is ∀-free.  It  *)
(*  takes the paper's own route instead — [a_consis_complete_thm] for the  *)
(*  run and the precision, then [a_consis_concrete_output_equiv]           *)
(*  (prop_sub_concrete_rhs.v) to move that precision from the consistency  *)
(*  OUTPUT to [P0].                                                       *)
(*                                                                        *)
(*  THE ONE REAL TECHNICALITY, verified by inspection.  Consistency puts   *)
(*  a ∀'s fresh binder in Θ; refinement puts it in Δ                       *)
(*  ([ad_refine_syn__all] descends at [add α Δ] with Θ FIXED).  So the     *)
(*  [__forall_syn] rows need the Θ→Δ move — and the PLAIN move is FALSE:   *)
(*  [ad_refine_syn__hole]'s fill [P] may mention the stripped binder and   *)
(*  its wf premise is at [Δ = ∅], so [α ∈ Δ] does not save it.  That is    *)
(*  why the F-indexed mirror exists: [ad_refine_syn_f_strip]               *)
(*  (prop_consis_sound.v:750) does the move under [α ∈ F].  So state the   *)
(*  lemma over [ad_precise_f] and forget at the end — exactly how          *)
(*  [a_consis_complete_thm] is structured.                                 *)
(*                                                                        *)
(*  Row-by-row the rest is mechanical: unit / var are reflexivity and      *)
(*  [__var]; arrow is a congruence ([is_sskl] and wf both split);          *)
(*  [forall_inh_*] are [is_sskl]-impossible; [ghostg] is [__hole] at       *)
(*  [P := □]; [tophole] / [topholeg] are [__tophole_keep] with wf giving   *)
(*  the guard; [tophole_drop] is [__tophole_remove]; and [flex_l] /        *)
(*  [flex_r] are the matching [__flex_*], where the definition is a        *)
(*  MONOtype ([a_wf_aenv_binds_def_mono]) so the two paintings coincide    *)
(*  again.                                                                 *)
(*                                                                        *)
(*  See DESIGN-completeness-subtyping.md §9.1.1.                           *)
(* ===================================================================== *)


