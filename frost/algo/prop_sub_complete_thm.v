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
Require Import src.frost.algo.prop_inc.           (* a_binds_tvar_weaken_mid *)
Require Import src.frost.algo.prop_refine.        (* lc_pskl_to_bskl_inh, a_wf_pskl_delta_mono *)
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



(* ===================================================================== *)
(*  THE CORRECTED PATH'S FIRST UNIT — moving a Δ-binder into Θ             *)
(*                                                                        *)
(*  The corrected shape of the shared lemma (DESIGN §9.1.1) threads the    *)
(*  SUBJECT's own refinement alongside the consistency derivation.  Those  *)
(*  two disagree about where a ∀'s binder goes: consistency opens into Θ,  *)
(*  refinement into Δ.  One direction of the reconciliation already        *)
(*  existed — [ad_refine_syn_f_strip] moves Θ→Δ, under the [F]-hygiene     *)
(*  that keeps ghost fills off the binder.  Here is the other, which the   *)
(*  threading needs and which requires NO hygiene condition at all: adding *)
(*  a Θ-binder only ADDS scope.                                           *)
(*                                                                        *)
(*  Both are stated in MID-INSERTION form, and that is forced rather than  *)
(*  general-for-its-own-sake: [ad_refine_pskl_f__tophole_fill] extends Θ   *)
(*  AT THE HEAD with its own binder, so a head-only statement would need   *)
(*  the IH at [(α1,α0),Θ] where the goal wants [(α0,α1),Θ].  The two have  *)
(*  the same [binds] graph, but neither judgment carries a congruence for  *)
(*  that — whereas the mid form simply absorbs the head into the LEFT      *)
(*  block and goes through.  The head form is the [Θ1 := ·] corollary.     *)
(*                                                                        *)
(*  [a_wf_pskl_reassoc_mid] is the same statement for well-formedness, and *)
(*  is what the refinement's own [__hole] row consumes.  Note the existing *)
(*  [a_wf_pskl_reassoc] (prop_consis_sound.v:1727) is the head-only form,  *)
(*  which suffices there only because wf's ∀ rule puts its binder in Δ.    *)
(* ===================================================================== *)

Lemma binds_insert_mid : forall (x : atom) (b : abind) Θ1 e Θ2,
  binds x b (Θ1 ++ Θ2) -> binds x b (Θ1 ++ e ++ Θ2).
Proof.
  intros x b Θ1 e Θ2 H; unfold binds in *;
    apply in_or_app; destruct (in_app_or _ _ _ H) as [Hin | Hin];
    [ left; exact Hin | right; apply in_or_app; right; exact Hin ].
Qed.

Lemma a_binds_tvar_insert_mid : forall α Θ1 e Θ2,
  a_binds_tvar α (Θ1 ++ Θ2) -> a_binds_tvar α (Θ1 ++ e ++ Θ2).
Proof.
  intros α Θ1 e Θ2 [Hb | [Hb | [τ Hb]]];
    [ left | right; left | right; right; exists τ ];
    apply binds_insert_mid; exact Hb.
Qed.

Lemma a_wf_pskl_reassoc_mid : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  forall Θ1 Θ2 α, Θ = Θ1 ++ Θ2 ->
  (Θ1 ++ (α ~ abind_tvar) ++ Θ2) ⨟ (remove α Δ) ⊢ₚₛᵃ P.
Proof.
  intros Θ Δ P H; induction H; intros Θ1 Θ2 α0 ->.
  - (* unit *) apply a_wf_pskl__unit.
  - (* var : a Δ-hit at α0 becomes the inserted Θ-entry *)
    apply a_wf_pskl__var.
    destruct H as [HΔ | Htv].
    + destruct (α == α0) as [-> | Hne].
      * right; left; unfold binds; apply in_or_app; right; simpl; left;
          reflexivity.
      * left; clear - HΔ Hne; fsetdec.
    + right; apply a_binds_tvar_insert_mid; exact Htv.
  - (* arrow *) apply a_wf_pskl__arrow; auto.
  - (* all : the opened binder is picked apart from α0 *)
    apply a_wf_pskl__all with (L := L `union` singleton α0); intros α Hα.
    eapply a_wf_pskl_delta_mono;
      [ apply (H0 α ltac:(clear - Hα; fsetdec) Θ1 Θ2 α0 eq_refl)
      | clear; fsetdec ].
  - (* hole *) apply a_wf_pskl__hole.
  - (* tophole : its body is checked at [Δ = ∅] *)
    apply a_wf_pskl__tophole; [ exact H | ].
    eapply a_wf_pskl_delta_mono;
      [ apply (IHa_wf_pskl Θ1 Θ2 α0 eq_refl) | clear; fsetdec ].
Qed.

Lemma ad_refine_pskl_f_reassoc_mid : forall F Θ Δ P Q,
  ad_refine_pskl_f F Θ Δ P Q ->
  forall Θ1 Θ2 α, Θ = Θ1 ++ Θ2 ->
  ad_refine_pskl_f F (Θ1 ++ (α ~ abind_tvar) ++ Θ2) (remove α Δ) P Q.
Proof.
  intros F Θ Δ P Q H; induction H; intros Θ1 Θ2 α0 ->.
  - (* unit *) apply ad_refine_pskl_f__unit.
  - (* var : as in the wf transport *)
    apply ad_refine_pskl_f__var.
    destruct H as [HΔ | Htv].
    + destruct (α == α0) as [-> | Hne].
      * right; left; unfold binds; apply in_or_app; right; simpl; left;
          reflexivity.
      * left; clear - HΔ Hne; fsetdec.
    + right; apply a_binds_tvar_insert_mid; exact Htv.
  - (* arrow *) apply ad_refine_pskl_f__arrow; auto.
  - (* all *)
    apply ad_refine_pskl_f__all with (L := L `union` singleton α0);
      intros α Hα.
    eapply ad_refine_pskl_f_delta_mono;
      [ apply (H0 α ltac:(clear - Hα; fsetdec) Θ1 Θ2 α0 eq_refl)
      | clear; fsetdec ].
  - (* hole : the fill's wf moves by the transport above *)
    apply ad_refine_pskl_f__hole; [ exact H | ].
    eapply a_wf_pskl_delta_mono;
      [ apply (a_wf_pskl_reassoc_mid H0 Θ1 Θ2 α0 eq_refl) | clear; fsetdec ].
  - (* tophole_remove *) apply ad_refine_pskl_f__tophole_remove; auto.
  - (* tophole_fill : ITS binder joins Θ above the insertion point, so the
       induction is run with the head absorbed into the LEFT block — which is
       exactly why this transport has to be the mid-insertion form *)
    apply ad_refine_pskl_f__tophole_fill with (L := L `union` singleton α0);
      intros α Hα.
    apply (H0 α ltac:(clear - Hα; fsetdec) ((α ~ abind_tvar) ++ Θ1) Θ2 α0);
      simpl_env; reflexivity.
  - (* tophole_keep *) apply ad_refine_pskl_f__tophole_keep; auto.
  - (* flex_l *)
    eapply ad_refine_pskl_f__flex_l; [ | auto ].
    apply binds_insert_mid; exact H.
  - (* flex_r *)
    eapply ad_refine_pskl_f__flex_r; [ | auto ].
    apply binds_insert_mid; exact H.
Qed.

(** The head form, which is what the threading actually applies. *)
Corollary ad_refine_pskl_f_reassoc : forall F Θ Δ P Q,
  ad_refine_pskl_f F Θ Δ P Q ->
  forall α, ad_refine_pskl_f F ((α ~ abind_tvar) ++ Θ) (remove α Δ) P Q.
Proof.
  intros F Θ Δ P Q H α.
  apply (ad_refine_pskl_f_reassoc_mid H nil Θ α); simpl_env; reflexivity.
Qed.

Print Assumptions ad_refine_pskl_f_reassoc.

(* ===================================================================== *)
(*  THE GHOST-ROW FACT — what the threaded induction needs at [__hole]     *)
(*                                                                        *)
(*  Precision fills a ghost with a SYNTHESISED painting                    *)
(*  ([ad_refine_syn_f__hole] emits [pskl_to_bskl_syn]), so at a ghost the  *)
(*  two paintings agree only if the fill is ∀-FREE                         *)
(*  ([pskl_no_forall_inh_eq_syn]).  Against a ghost SUBJECT that is        *)
(*  exactly what consistency delivers: only three of its rows have such a  *)
(*  subject, and each pins the counterpart to an INHERITED painting, a     *)
(*  bare ghost, or a variable — after which [is_sskl], which forbids       *)
(*  [bskl_all_inh], leaves no ∀ anywhere.                                  *)
(*                                                                        *)
(*  Context-FREE, which is the point: the threading can use it without     *)
(*  having to move the consistency derivation between Θ and Δ.             *)
(* ===================================================================== *)

Lemma is_sskl_inh_no_forall : forall P,
  is_sskl (pskl_to_bskl_inh P) -> pskl_no_forall P.
Proof.
  intros P; induction P; cbn; intros H; try exact I.
  - (* arrow *) inversion H; subst; split; auto.
  - (* all_syn : its inherited painting IS a [bskl_all_inh] *) inversion H.
  - (* tophole *) inversion H; subst; auto.
Qed.

Lemma ad_pat_consis_ghost_subject_no_forall : forall Ψ Θ R Q,
  Ψ ⨟ Θ ⊢ₛᵃ R ∼ Q ->
  is_sskl Q ->
  uskl_to_pskl R = pskl_hole ->
  pskl_no_forall (bskl_to_pskl Q).
Proof.
  intros Ψ Θ R Q H; induction H; intros Hsk Heq; cbn in Heq |- *;
    try discriminate Heq.
  - (* __ghostg : the counterpart is [◇] *) exact I.
  - (* __hole : an INHERITED painting, and [is_sskl] makes it ∀-free *)
    rewrite bskl_to_pskl_pskl_to_bskl_inh.
    apply is_sskl_inh_no_forall; exact Hsk.
  - (* __flex_r : a bare variable *) exact I.
Qed.

Print Assumptions ad_pat_consis_ghost_subject_no_forall.

(* ===================================================================== *)
(*  F-GROWTH — the other half of what the strip needs                     *)
(*                                                                        *)
(*  [ad_refine_syn_f_strip] moves a Θ-binder into Δ only when that binder  *)
(*  is in [F], i.e. forbidden in ghost fills.  Every ∀ row of the threaded *)
(*  induction opens a FRESH binder and then wants to strip it, so it must  *)
(*  first put that binder into [F] — and [_fmono] only ever SHRINKS F.     *)
(*                                                                        *)
(*  Growing F is sound for a binder the context does not know: a ghost     *)
(*  fill is well formed at [Θ ⨟ ∅], so its free variables live in [dom Θ]  *)
(*  ([a_wf_pskl_ftv_tvarish]) and a fresh α is not among them.  This is    *)
(*  exactly the invariant the SUBJECT-refinement premise carries and the   *)
(*  consistency derivation does not — consistency's own ∀ rule puts the    *)
(*  binder INTO Θ, after which a fill may legitimately mention it, which   *)
(*  is what [cex/cex_p7_sskl_precise.v] exploits.                          *)
(* ===================================================================== *)

Lemma a_wf_pskl_ftv_dom : forall Θ P,
  Θ ⨟ empty ⊢ₚₛᵃ P ->
  forall α, α `in` ftvar_in_pskl P -> α `in` dom Θ.
Proof.
  intros Θ P Hwf α Hα.
  destruct (@a_wf_pskl_ftv_tvarish _ _ _ Hwf α Hα) as [HΔ | Htv];
    [ clear - HΔ; fsetdec | ].
  destruct Htv as [Hb | [Hb | [τ Hb]]]; eapply binds_In; exact Hb.
Qed.

Lemma ad_refine_pskl_f_fgrow : forall F Θ Δ P Q,
  ad_refine_pskl_f F Θ Δ P Q ->
  forall α, α `notin` dom Θ ->
  ad_refine_pskl_f (add α F) Θ Δ P Q.
Proof.
  intros F Θ Δ P Q H; induction H; intros α0 Hα0.
  - (* unit *) apply ad_refine_pskl_f__unit.
  - (* var *) apply ad_refine_pskl_f__var; assumption.
  - (* arrow *) apply ad_refine_pskl_f__arrow; auto.
  - (* all : Θ does not move *)
    apply ad_refine_pskl_f__all with (L := L); intros α Hα; auto.
  - (* hole : the fill is Θ-scoped, and α0 is not in Θ *)
    apply ad_refine_pskl_f__hole; [ | exact H0 ].
    apply inter_empty_pointwise; intros β Hβ.
    destruct (AtomSetProperties.In_dec β (ftvar_in_pskl Q)) as [Hin | Hni].
    + assert (Hdom : β `in` dom Θ) by (eapply a_wf_pskl_ftv_dom; eassumption).
      assert (Hne : β <> α0) by (intros ->; clear - Hdom Hα0; fsetdec).
      clear - H Hin Hne Hβ; fsetdec.
    + clear - Hni Hβ; fsetdec.
  - (* tophole_remove *) apply ad_refine_pskl_f__tophole_remove; auto.
  - (* tophole_fill : ITS binder is picked apart from α0 *)
    apply ad_refine_pskl_f__tophole_fill
      with (L := L `union` singleton α0 `union` dom Θ);
      intros α Hα.
    apply H0; [ clear - Hα; fsetdec | simpl; clear - Hα Hα0; fsetdec ].
  - (* tophole_keep *) apply ad_refine_pskl_f__tophole_keep; auto.
  - (* flex_l *) eapply ad_refine_pskl_f__flex_l; [ exact H | auto ].
  - (* flex_r *) eapply ad_refine_pskl_f__flex_r; [ exact H | auto ].
Qed.

Print Assumptions ad_refine_pskl_f_fgrow.

(** …and the plain Θ-weakening the same rows need, which falls out of the
    reassoc above once the [remove] is absorbed by Δ-monotonicity. *)
Corollary ad_refine_pskl_f_weaken_tvar : forall F Θ Δ P Q,
  ad_refine_pskl_f F Θ Δ P Q ->
  forall α, ad_refine_pskl_f F ((α ~ abind_tvar) ++ Θ) Δ P Q.
Proof.
  intros F Θ Δ P Q H α.
  eapply ad_refine_pskl_f_delta_mono;
    [ apply (ad_refine_pskl_f_reassoc H α) | clear; fsetdec ].
Qed.

Corollary a_wf_pskl_weaken_tvar : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  forall α, ((α ~ abind_tvar) ++ Θ) ⨟ Δ ⊢ₚₛᵃ P.
Proof.
  intros Θ Δ P H α.
  eapply a_wf_pskl_delta_mono;
    [ apply (a_wf_pskl_reassoc H α) | clear; fsetdec ].
Qed.

(* ===================================================================== *)
(*  THE THREADED INDUCTION — the kit is complete except ONE ROW           *)
(*                                                                        *)
(*  Route (settled by building the transports, not by guessing): induct on *)
(*  the CONSISTENCY derivation, carry the SUBJECT-refinement premise, and  *)
(*  at each ∀ row                                                         *)
(*                                                                        *)
(*    · invert the refinement's [__all]        → premise at [Θ ⨟ add α Δ]  *)
(*    · [ad_refine_pskl_f_fgrow]               → at [add α F]              *)
(*    · [ad_refine_pskl_f_weaken_tvar]         → at [(α:tvar),Θ]           *)
(*    · run the IH                              → precision at [(α:tvar),Θ] *)
(*    · [ad_refine_syn_f_strip]  (α ∈ add α F ∩ add α Δ)  → back at Θ      *)
(*    · [ad_refine_syn_f_fmono]                → back at F                 *)
(*                                                                        *)
(*  The ghost rows take their fill's well-formedness from the REFINEMENT   *)
(*  premise (Θ-scoped, so [fgrow] applies) rather than from consistency —  *)
(*  consistency's ∀ rule puts the binder INTO Θ, after which a fill may    *)
(*  legitimately mention it, and that is precisely what                    *)
(*  [cex/cex_p7_sskl_precise.v] exploits.  ∀-freeness of the fill comes    *)
(*  from [ad_pat_consis_ghost_subject_no_forall].                          *)
(*                                                                        *)
(*  ONE ROW IS STILL OPEN, and it is small and exactly stated.  At         *)
(*  consistency's [__tophole] / [__topholeg] the goal is                   *)
(*  [∀◇.⌊R0⌋ ⊑ ∀◇.⌊Q'⌋], which [ad_refine_syn_f__tophole_keep] reduces to  *)
(*  the IH at [(R0, Q')] — with the guard supplied by the target's wf.     *)
(*  The refinement premise, however, need not decompose the same way:      *)
(*  inverting it at [(∀◇.⌊R0⌋, ∀◇.⌊Q'⌋)] gives [__tophole_keep] (which IS  *)
(*  the premise the IH wants) OR [__tophole_remove] (which gives           *)
(*  [⌊R0⌋ ⊳ ∀◇.⌊Q'⌋] instead).  In the second case neither judgment can    *)
(*  re-wrap: consistency has no rule adding a [∀◇] to the COUNTERPART      *)
(*  without a matching one on the subject.  So the threading needs either  *)
(*  a normalisation of the refinement premise at ∀◇ (prefer [__tophole_    *)
(*  keep] where the target has one) or an IH tolerating the extra [∀◇].    *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  THE PAPER'S OWN ROUTE FOR Sub-Infer / Sub-UnivGhostR, AND THE ONE      *)
(*  LEMMA IT NEEDS                                                        *)
(*                                                                        *)
(*  Re-reading :3134, the paper does NOT read a precision off the          *)
(*  consistency premise.  It invokes thm:complete-consistency — which is   *)
(*  mechanized, [a_consis_complete_thm] — on the consistency problem       *)
(*  [(Θ0; □; P)], and takes the precision from THAT.  Since [skmod] forces *)
(*  [P0 = □] in both rows, the only thing needed to line the two up is     *)
(*  that the algorithmic consistency OUTPUT at [P0 = □] is the SUBJECT.    *)
(*                                                                        *)
(*  And it is, on the nose: of the fifteen [a_consis] rows only three      *)
(*  admit [P0 = □] — [__ghost] (whose subject IS [□]), [__ghost_r], and    *)
(*  [__flex_l] — and each returns its own subject.  [__univ_ghost2] is the *)
(*  only row that does not fix [P0]'s shape, and its [guarded_pskl P0]     *)
(*  premise excludes the ghost.                                           *)
(* ===================================================================== *)

Lemma a_consis_hole_p0_output : forall F Δ1 Δ2 Θ0 P0 P P' Θ1,
  a_consis F Δ1 Δ2 Θ0 P0 P P' Θ1 ->
  P0 = pskl_hole ->
  P' = P.
Proof.
  intros F Δ1 Δ2 Θ0 P0 P P' Θ1 H; induction H; intros Heq;
    try discriminate Heq.
  - (* __ghost : the subject is the ghost, the output is [P0] *) exact Heq.
  - (* __univ_ghost2 : [guarded_pskl □] is impossible *)
    subst; match goal with Hg : guarded_pskl pskl_hole |- _ => inversion Hg end.
  - (* __flex_l : the output is the subject variable *) reflexivity.
  - (* __ghost_r : the output IS the subject *) reflexivity.
Qed.

Print Assumptions a_consis_hole_p0_output.

(* ===================================================================== *)
(*  Sub-Infer / Sub-UnivGhostR, ASSEMBLED — and the ONE piece still open   *)
(*                                                                        *)
(*  Following the paper (:3134), the two rows go:                         *)
(*                                                                        *)
(*   1. [skmod] forces [P0 = □] (both [a_sk_mode_compat] and              *)
(*      [a_ty_mode_compat] pin [mode_ti] to the ghost);                    *)
(*   2. [a_sub__infer] gives the run, output [P] at context [Θ0] — so the  *)
(*      two increase conjuncts are [ζ := κ] + [opt_axiom_factor] again;    *)
(*   3. the DECORATED consistency premise undecorates:                     *)
(*      [ad_pat_consis_strip_tags] (prop_consis_precise.v:275) turns       *)
(*      [Ψ ⨟ Θ ⊢ₛᵃ κR ∼ Q] into [∅ ⨟ Θ ⊢ₛᵃ pskl_to_uskl ⌊κR⌋ˢ ∼ Q], and   *)
(*      [⌊κR⌋ˢ = κ⌊R⌋ˢ = κP] by a one-line commutation;                    *)
(*   4. [a_consis_complete_thm] on the problem [(Θ0; □; P)] — its other    *)
(*      two premises ARE this motive's refinement premises at [P0 = □];    *)
(*   5. [a_consis_hole_p0_output] (above) says the run's output is [P], so *)
(*      the theorem's precision IS a precision about [P].                  *)
(*                                                                        *)
(*  STEP 5 LANDS THE PRECISION UNDER THE THEOREM'S OWN ζ, NOT UNDER κ, and *)
(*  that is the one piece still missing.  The package gives                *)
(*  [a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ], and                        *)
(*  [msubst_compose_id_pskl] collapses the composite on a Θ0-scoped        *)
(*  skeleton, so [a_inc_equiv_msubst_pskl] yields                          *)
(*                                                                        *)
(*      Θ ⊢ (msubst_pskl κ P) ≡ˢ (msubst_pskl ζ P)                        *)
(*                                                                        *)
(*  — after which the goal needs precision to TRANSPORT along ≡ˢ in its    *)
(*  left argument:                                                        *)
(*                                                                        *)
(*      Θ ⊢ P1 ≡ˢ P2  →  Θ ⨟ Δ ⊢ₚᵣᵃ P2 ⊑ X  →  Θ ⨟ Δ ⊢ₚᵣᵃ P1 ⊑ X         *)
(*                                                                        *)
(*  It is true and it is the RIGHT lemma — ≡ˢ unfolds flexible definitions *)
(*  and refinement's [__flex_l] / [__flex_r] rows do exactly that — but it *)
(*  is not a one-liner: ≡ˢ is an equivalence CLOSURE, so the induction has *)
(*  to carry both directions at once (an [<->]), and its [__flex_def] row  *)
(*  needs [a_wf_aenv Θ] for the definition's uniqueness and monotypeness.   *)
(*  That single lemma is what stands between here and both rows.           *)
(*                                                                        *)
(*  (The alternative — take the theorem's ζ as the witness and repair the  *)
(*  increase conjuncts instead — trades this for restricting [ζ ∷ Θ1c ⊑ Θ] *)
(*  back to Θ0, which is not free either: at [P0 = □] the consistency run  *)
(*  may be [__flex_l], whose output context is an [a_assign] result rather *)
(*  than a suffix extension of Θ0.  [is_id_inc_unique] does settle that    *)
(*  route's [a_inc_equiv] conjunct, if anyone prefers it.)                 *)
(* ===================================================================== *)
