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
Require Import src.frost.algo.prop_compose.       (* a_inc_{dom_flex,lookup_wf,lookup_mono}, msubst_pskl_open *)
Require Import src.frost.algo.prop_normal.        (* a_inc_equiv_lookup (the a_binds_tvar form) *)
Require Import src.frost.algo.prop_mono_bridge.   (* ptyp_to_bskl_inh_syn_eq *)
Require Import src.frost.algo.prop_precise_recover. (* tyequiv_mono_refine_syn *)
Require Import src.frost.algo.prop_pat_sub.       (* uskl_to_pskl_ptyp_to_uskl_syn *)

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
    preserves the fuel of exactly.

    THE SOLUTION NOTION (repaired 2026-07-30).  The paper gives a solution
    TWO conditions (join + P0-fill, subtyping-proofs.tex:3054-3074), which is
    NOT enough: the capture configuration [(P0=◇, P=∀X.◇, Q=∀X.X)] passes
    both, yet the optimality conclusion is underivable and the Sub-Infer /
    Sub-Check cases genuinely need the AUGMENTED thm:complete-consistency's
    third condition (the subject's refinement) at each consistency leaf.
    The first repair attempt stated that condition ONCE, at the ROOT
    ([⊢ᵣₚᵃ κ⌊R⌋ˢ ⊳ ⌊Q⌋] as a third motive premise) — REFUTED: refinement is
    a lockstep relation, so a root condition excludes every solution whose
    sides disagree at a head through ForallL / ForallR / UnivGhostR, i.e.
    instantiation and generalisation themselves (machine-checked,
    cex/cex_p7_univ_ghost_r_vacuous.v + cex/cex_p7_third_premise_forall.v).
    The repair moves the condition INTO THE JOIN, at the consistency leaves
    where it is consumed: the join is now the LEAF-VALID mirror
    [ad_pat_sub_gv] (def_decl_algo_sub_hyg.v), and there is no third root
    premise.  [ad_pat_sub_gv_forget] recovers the plain [_g] mirror for
    every P5/P6 invocation. *)
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
  (* ---- the solution: an increase, the LEAF-VALID join, the P0-fill ---- *)
  κ ∷ Θ0 ⊑ Θ ->
  ad_pat_sub_gv n NM M Ψ Θ (msubst_uskl_syn κ R) Q ->
  ad_refine_syn_f empty Θ empty (pskl_to_bskl_inh (msubst_pskl κ P0)) Q ->
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
  (* the subject is [syn{κα̂}] — a monotype painting, not an unresolved R;
     the join is the LEAF-VALID mirror (see [sub_complete_concl]'s note) *)
  ad_pat_sub_gv n NM (mode_fn M) Ψ Θ
    (ptyp_to_uskl_syn (msubst_lookup κ α)) Q ->
  ad_refine_syn_f empty Θ empty
    (pskl_to_bskl_inh (msubst_pskl κ P0)) Q ->
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

(** At the empty forbidden set the hygienic refinement IS the plain one; this
    is the converse of [ad_refine_pskl_f_forget], used to hand the join's
    leaf refinements to [a_consis_complete_thm] (whose premises are [_f]). *)
Lemma ad_refine_pskl_f_empty_intro : forall Θ Δ P Q,
  Θ ⨟ Δ ⊢ᵣₚᵃ P ⊳ Q ->
  ad_refine_pskl_f empty Θ Δ P Q.
Proof.
  intros Θ Δ P Q H; induction H.
  - apply ad_refine_pskl_f__unit.
  - apply ad_refine_pskl_f__var; assumption.
  - apply ad_refine_pskl_f__arrow; assumption.
  - eapply ad_refine_pskl_f__all; eauto.
  - apply ad_refine_pskl_f__hole; [ clear; fsetdec | assumption ].
  - apply ad_refine_pskl_f__tophole_remove; assumption.
  - eapply ad_refine_pskl_f__tophole_fill; eauto.
  - apply ad_refine_pskl_f__tophole_keep; assumption.
  - eapply ad_refine_pskl_f__flex_l; eauto.
  - eapply ad_refine_pskl_f__flex_r; eauto.
Qed.

(** At [M = TI] the leaf-valid join always yields the subject's refinement
    into the counterpart: [__infer] carries it on the rule, and the two ghost
    subjects rebuild it from their own rule premises ([◇]'s fill is the
    counterpart's erasure, well-formed by the rule; [◈]'s counterpart is [◇]).
    Every other row is excluded by its mode. *)
Lemma ad_pat_sub_gv_ti_refine : forall n NM Ψ Θ R Q,
  ad_pat_sub_gv n NM mode_ti Ψ Θ R Q ->
  Θ ⨟ empty ⊢ᵣₚᵃ ⌊ R ⌋ˢ ⊳ (bskl_to_pskl Q).
Proof.
  intros n NM Ψ Θ R Q H; inversion H; subst; try congruence.
  (* __infer is closed by [congruence] (the goal IS the rule's premise);
     the two ghost subjects remain. *)
  - (* __ghost *)
    cbn. rewrite bskl_to_pskl_pskl_to_bskl_inh.
    apply ad_refine_pskl__hole. assumption.
  - (* __ghostg *)
    cbn. apply ad_refine_pskl__hole. apply a_wf_pskl__hole.
Qed.

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
  intros Hwf0 Hwfth HwfP0 HwfP HmodSK HmodTY HeqP Hinc Hsub Hrs.
  apply ad_pat_sub_gv_forget in Hsub.
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
  intros Hwf0 Hwfth HwfP0 HwfP HmodSK HmodTY HeqP Hinc Hsub Hrs.
  apply ad_pat_sub_gv_forget in Hsub.
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
(*  skeleton, so what is wanted is                                        *)
(*                                                                        *)
(*      Θ ⨟ Δ ⊢ₚᵣᵃ (msubst_pskl κ P) ⊑ (msubst_pskl σ P)                  *)
(*        given  a_inc_equiv Θ0 κ σ Θ  and  Θ0 ⨟ Δ0 ⊢ₚₛᵃ P                *)
(*                                                                        *)
(*  — "PRECISION IS STABLE UNDER EQUIVALENT METASUBSTITUTIONS" — after     *)
(*  which [ad_refine_syn_trans] composes it with the theorem's precision.  *)
(*                                                                        *)
(*  ⚠️ NOTE THIS IS NOT THE GENERAL ≡ˢ TRANSPORT.  An earlier reading of    *)
(*  this gap asked for                                                    *)
(*    [Θ ⊢ P1 ≡ˢ P2 → Θ ⨟ Δ ⊢ₚᵣᵃ P2 ⊑ X → Θ ⨟ Δ ⊢ₚᵣᵃ P1 ⊑ X],            *)
(*  which is awkward because ≡ˢ is an equivalence CLOSURE (the induction   *)
(*  has to carry both directions, and its [trans] row needs wf of a MIDDLE *)
(*  skeleton nobody supplies).  The statement above avoids all of that: it *)
(*  inducts on the WF OF [P], and the equivalence it needs is not a        *)
(*  general ≡ˢ but congruence over P's own structure with ≡ᵗ-MONOTYPES at  *)
(*  the leaves — because a metasubstitution's images are monotypes.        *)
(*                                                                        *)
(*  Row by row that is: [unit] / [hole] are constructors; [arrow] / [all] / *)
(*  [tophole] are congruences (the last by [__tophole_keep], whose guard    *)
(*  wf supplies and [msubst] preserves); a Δ-bound or RIGID variable is    *)
(*  missed by both metasubstitutions ([msubst_lookup_notin]) so both sides *)
(*  are the same variable; and a FLEXIBLE variable is the only real case — *)
(*  [a_inc_equiv_lookup] gives [Θ ⊢ κα ≡ᵗ σα], [a_inc_lookup_mono] gives   *)
(*  both monotypes, and [tyequiv_mono_refine_syn]                          *)
(*  (prop_precise_recover.v:90) IS that case, already Qed.                 *)
(*                                                                        *)
(*  Side conditions it will want, both standard and both available at the  *)
(*  call site: [Δ0 ⊆ Δ], and Δ-binders fresh for the context (the same     *)
(*  condition [ad_refine_syn_trans] itself carries).                       *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  PRECISION IS STABLE UNDER EQUIVALENT METASUBSTITUTIONS                *)
(*                                                                        *)
(*  The induction is on the WELL-FORMEDNESS OF [P], not on ≡ˢ: the        *)
(*  equivalence actually in play is congruence over P's own structure with *)
(*  ≡ᵗ-MONOTYPES at the leaves, because a metasubstitution's images are    *)
(*  monotypes.  Inducting on ≡ˢ instead would have to carry both           *)
(*  directions (it is an equivalence CLOSURE) and its transitivity row     *)
(*  would need well-formedness of a middle skeleton nobody supplies.       *)
(*                                                                        *)
(*  Only ONE side condition survived writing it out — [Δ0 ⊆ Δ], which the  *)
(*  Δ-bound-variable leaf needs.  The Δ-freshness the plan also guessed at *)
(*  is NOT needed: the variable row splits on [α ∈ dom κ] / [α ∈ dom σ]    *)
(*  rather than on where α is bound, and BOTH answers are usable —         *)
(*  [a_inc_dom_flex] turns a hit into [a_binds_tvar α Θ0] (the ≡ᵗ route),  *)
(*  and a double miss makes both sides the SAME variable.                  *)
(* ===================================================================== *)

(** The variable leaf, for a source-visible α — RIGID or FLEXIBLE alike.
    [prop_normal.a_inc_equiv_lookup] is stated at [a_binds_tvar], so no case
    split is needed here: at a rigid α both images are α itself and the ≡ᵗ is
    reflexivity, which the same route absorbs. *)
Lemma a_inc_equiv_precise_msubst_var : forall Θ0 κ σ Θ Δ α,
  a_wf_aenv Θ0 -> a_wf_aenv Θ ->
  κ ∷ Θ0 ⊑ Θ -> σ ∷ Θ0 ⊑ Θ ->
  (forall α0, a_binds_tvar α0 Θ0 ->
     Θ ⊢ (msubst_lookup κ α0) ≡ᵗ (msubst_lookup σ α0)) ->
  a_binds_tvar α Θ0 ->
  Θ ⨟ Δ ⊢ₚᵣᵃ (msubst_pskl κ (pskl_var_f α)) ⊑ (msubst_pskl σ (pskl_var_f α)).
Proof.
  intros Θ0 κ σ Θ Δ α Hwf0 Hwfth Hκ Hσ Hie Hbt.
  assert (Hmκ : mono_ptyp (msubst_lookup κ α))
    by (eapply a_inc_lookup_mono; exact Hκ).
  assert (Hmσ : mono_ptyp (msubst_lookup σ α))
    by (eapply a_inc_lookup_mono; exact Hσ).
  unfold ad_precise; cbn [msubst_pskl].
  rewrite (ptyp_to_bskl_inh_syn_eq Hmκ), (ptyp_to_bskl_inh_syn_eq Hmσ).
  apply tyequiv_mono_refine_syn; try assumption.
  - (* the two images are ≡ᵗ — this IS what [a_inc_equiv] says, per variable *)
    apply Hie; exact Hbt.
  - (* κ's image is well formed in the target, so its variables are visible *)
    intros β Hβ.
    eapply a_wf_ptyp_ftv_tvarish; [ | exact Hβ ].
    eapply a_inc_lookup_wf; eassumption.
Qed.

Lemma a_inc_equiv_precise_msubst_gen : forall Θ0 Δ0 P,
  Θ0 ⨟ Δ0 ⊢ₚₛᵃ P ->
  forall κ σ Θ Δ,
    a_wf_aenv Θ0 -> a_wf_aenv Θ ->
    κ ∷ Θ0 ⊑ Θ -> σ ∷ Θ0 ⊑ Θ ->
    (forall α, a_binds_tvar α Θ0 ->
       Θ ⊢ (msubst_lookup κ α) ≡ᵗ (msubst_lookup σ α)) ->
    Δ0 [<=] Δ ->
    Θ ⨟ Δ ⊢ₚᵣᵃ (msubst_pskl κ P) ⊑ (msubst_pskl σ P).
Proof.
  intros Θ0 Δ0 P Hwf.
  induction Hwf as [ Θ0 Δ0 | Θ0 Δ0 α Hbt
                   | Θ0 Δ0 P1 P2 Hwf1 IH1 Hwf2 IH2
                   | L Θ0 Δ0 P0 Hwf0 IH0
                   | Θ0 Δ0
                   | Θ0 Δ0 P0 Hg Hwf0 IH0 ];
    intros κ σ Θ Δ Hwf0' Hwfth Hκ Hσ Hie Hsub.
  - (* unit *) unfold ad_precise; cbn. apply ad_refine_syn__unit.
  - (* var : [α ∈ Δ0] OR [a_binds_tvar α Θ0] — but the split that matters is
       whether the metasubstitutions SEE α, and either answer is usable *)
    destruct Hbt as [HΔ | Hbt];
      [ | eapply a_inc_equiv_precise_msubst_var with (Θ0 := Θ0); eassumption ].
    destruct (AtomSetProperties.In_dec α (dom κ)) as [Hκα | Hκα].
    + (* κ hits α, so α is a source flexible *)
      eapply a_inc_equiv_precise_msubst_var with (Θ0 := Θ0); try eassumption.
      destruct (a_inc_dom_flex Hκ Hκα) as [Hb | [τ Hb]];
        [ right; left | right; right; exists τ ]; exact Hb.
    + destruct (AtomSetProperties.In_dec α (dom σ)) as [Hσα | Hσα].
      * (* σ hits α : same conclusion, read off σ *)
        eapply a_inc_equiv_precise_msubst_var with (Θ0 := Θ0); try eassumption.
        destruct (a_inc_dom_flex Hσ Hσα) as [Hb | [τ Hb]];
          [ right; left | right; right; exists τ ]; exact Hb.
      * (* neither sees α : both sides are the SAME variable, and it is
           Δ-bound in the target *)
        unfold ad_precise; cbn [msubst_pskl].
        rewrite (@msubst_lookup_notin κ α Hκα), (@msubst_lookup_notin σ α Hσα).
        cbn. apply ad_refine_syn__var. left. clear - HΔ Hsub. fsetdec.
  - (* arrow : a congruence *)
    unfold ad_precise; cbn [msubst_pskl pskl_to_bskl_inh].
    apply ad_refine_syn__arrow;
      [ apply IH1 | apply IH2 ]; assumption.
  - (* all : a congruence, under a binder fresh for both metasubstitutions *)
    unfold ad_precise; cbn [msubst_pskl pskl_to_bskl_inh].
    apply ad_refine_syn__all
      with (L := L `union` dom κ `union` dom σ `union` dom Θ0 `union` dom Θ
                   `union` Δ `union` Δ0).
    intros α Hα.
    (* the two freshness facts are PINNED in named asserts: passed inline as
       [ltac:(fsetdec)] the goal still carries the binder as an evar, and
       fsetdec on an evar goal wedges *)
    assert (Hακ : α `notin` dom κ) by (clear - Hα; fsetdec).
    assert (Hασ : α `notin` dom σ) by (clear - Hα; fsetdec).
    rewrite <- (pskl_to_bskl_inh_open (msubst_pskl κ P0) α).
    rewrite <- (pskl_to_bskl_inh_open (msubst_pskl σ P0) α).
    rewrite <- (@msubst_pskl_open Θ0 κ Θ P0 α Hκ Hακ).
    rewrite <- (@msubst_pskl_open Θ0 σ Θ P0 α Hσ Hασ).
    apply IH0; try assumption; [ clear - Hα; fsetdec | ].
    clear - Hsub; fsetdec.
  - (* hole : [ad_refine_syn__hole] at the fill [□] *)
    unfold ad_precise; cbn.
    apply (@ad_refine_syn__hole Θ Δ pskl_hole). apply a_wf_pskl__hole.
  - (* tophole : [__tophole_keep], whose guard the wf premise supplies and
       the metasubstitution preserves *)
    unfold ad_precise; cbn [msubst_pskl pskl_to_bskl_inh].
    apply ad_refine_syn__tophole_keep.
    + apply guarded_pskl_to_bskl_inh.
      eapply guarded_pskl_msubst_inc; [ exact Hσ | exact Hg ].
    + apply IH0; try assumption. clear; fsetdec.
Qed.

(** The two [a_inc_equiv] instances.  Both directions are needed — Sub-Infer
    moves the precision FROM κ, Sub-Check moves it TO κ — and only the
    pointwise ≡ᵗ hypothesis makes the second free ([a_inc_equiv] itself is not
    obviously symmetric: [a_inc_equiv__flex_def]'s third premise mentions κ). *)
Corollary a_inc_equiv_precise_msubst : forall Θ0 Δ0 P κ σ Θ Δ,
  Θ0 ⨟ Δ0 ⊢ₚₛᵃ P ->
  a_wf_aenv Θ0 -> a_wf_aenv Θ ->
  κ ∷ Θ0 ⊑ Θ -> σ ∷ Θ0 ⊑ Θ ->
  a_inc_equiv Θ0 κ σ Θ ->
  Δ0 [<=] Δ ->
  Θ ⨟ Δ ⊢ₚᵣᵃ (msubst_pskl κ P) ⊑ (msubst_pskl σ P).
Proof.
  intros Θ0 Δ0 P κ σ Θ Δ HwfP Hwf0 Hwfth Hκ Hσ Hie Hsub.
  eapply a_inc_equiv_precise_msubst_gen; try eassumption.
  intros α Hbt. eapply prop_normal.a_inc_equiv_lookup; eassumption.
Qed.

Corollary a_inc_equiv_precise_msubst_flip : forall Θ0 Δ0 P κ σ Θ Δ,
  Θ0 ⨟ Δ0 ⊢ₚₛᵃ P ->
  a_wf_aenv Θ0 -> a_wf_aenv Θ ->
  κ ∷ Θ0 ⊑ Θ -> σ ∷ Θ0 ⊑ Θ ->
  a_inc_equiv Θ0 κ σ Θ ->
  Δ0 [<=] Δ ->
  Θ ⨟ Δ ⊢ₚᵣᵃ (msubst_pskl σ P) ⊑ (msubst_pskl κ P).
Proof.
  intros Θ0 Δ0 P κ σ Θ Δ HwfP Hwf0 Hwfth Hκ Hσ Hie Hsub.
  eapply a_inc_equiv_precise_msubst_gen; try eassumption.
  intros α Hbt. apply a_tyequiv__sym.
  eapply prop_normal.a_inc_equiv_lookup; eassumption.
Qed.

Print Assumptions a_inc_equiv_precise_msubst.
Print Assumptions a_inc_equiv_precise_msubst_flip.

(* ===================================================================== *)
(*  Sub-Infer AND Sub-UnivGhostR — THE PAPER'S OWN ROUTE (:3134)           *)
(*                                                                        *)
(*  Both rows have [skmod] forcing [P0 = □], both algorithmic counterparts *)
(*  return the INPUT skeleton (or [∀◇] of it) at the INPUT context, and    *)
(*  both take their precision from thm:complete-consistency —              *)
(*  [a_consis_complete_thm] — on the consistency problem [(Θ0; □; P)].     *)
(*  The two conjuncts about the increase are [ζ := κ] + [opt_axiom_factor] *)
(*  exactly as in [a_sub_complete_ghost].                                  *)
(* ===================================================================== *)

(** A refinement OUT OF the ghost has a well-formed target.  Only two rows
    have a [◇] source: [__hole], which carries the fill's well-formedness on
    the rule, and [__flex_r], whose target is a DEFINED flexible and so is
    [a_binds_tvar].  This is what supplies [ad_refine_syn_trans]'s external wf
    side condition at [P0 = □] — the condition refinement does NOT prove in
    general (cex_refine_not_transitive.v). *)
Lemma ad_refine_syn_hole_l_target_wf : forall Θ Δ Q,
  Θ ⨟ Δ ⊢ᵣᵃ bskl_hole ⊳ Q ->
  Θ ⨟ Δ ⊢ₚₛᵃ (bskl_to_pskl Q).
Proof.
  intros Θ Δ Q H.
  remember bskl_hole as Qh eqn:HQh.
  induction H; try discriminate HQh.
  - (* __hole *)
    rewrite bskl_to_pskl_pskl_to_bskl_syn.
    eapply a_wf_pskl_delta_mono; [ exact H | clear; fsetdec ].
  - (* __flex_r : the target is a defined flexible *)
    cbn. apply a_wf_pskl__var. right; right; eauto.
Qed.

Print Assumptions ad_refine_syn_hole_l_target_wf.

(** THE SHARED CORE.  At [P0 = □] the motive's three solution premises ARE
    thm:complete-consistency's, so its precision applies — and
    [a_consis_hole_p0_output] says the consistency run returns the SUBJECT, so
    that precision is about [P].  It arrives under the theorem's own ζ; the
    metasubstitution-stability lemma above moves it to κ, and
    [ad_refine_syn_trans] composes. *)
Lemma a_sub_complete_hole_p0_precision : forall Θ0 P Θ κ Q,
  a_wf_aenv Θ0 -> a_wf_aenv Θ ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P ->
  κ ∷ Θ0 ⊑ Θ ->
  empty ⨟ Θ ⊢ₛᵃ (pskl_to_uskl (msubst_pskl κ P)) ∼ Q ->
  ad_refine_syn_f empty Θ empty bskl_hole Q ->
  ad_refine_pskl_f empty Θ empty (msubst_pskl κ P) (bskl_to_pskl Q) ->
  Θ ⨟ empty ⊢ₚᵣᵃ (msubst_pskl κ P) ⊑ (bskl_to_pskl Q).
Proof.
  intros Θ0 P Θ κ Q Hwf0 Hwfth HwfP Hinc Hconsis Hrs Hrp.
  (* 1. thm:complete-consistency at [(Θ0; □; P)] *)
  destruct (a_consis_complete_thm empty Hwf0 (a_wf_pskl__hole Θ0 empty)
              HwfP Hinc Hwfth Hconsis Hrs Hrp)
    as [P1 [Θ1 [Hrun Hopt]]].
  (* 2. at [P0 = □] the run's output IS the subject *)
  pose proof (a_consis_hole_p0_output Hrun eq_refl) as HP1; subst P1.
  (* 3. the run is an identity increase into a well-formed Θ1 *)
  destruct (a_consis_sound_aux Hrun Hwf0 (a_wf_pskl__hole Θ0 empty) HwfP
              ltac:(intros α Hα; clear - Hα; fsetdec)
              ltac:(intros β τ Hb; apply inter_empty_pointwise;
                    intros α Hα; clear - Hα; fsetdec)
              ltac:(intros Θa β b Θb Heq Hne;
                    apply inter_empty_pointwise;
                    intros α Hα; clear - Hα; fsetdec))
    as [[[κ1 [Hid Hinc1]] _] [Hwf1 _]].
  (* 4. the package, at that identity *)
  destruct (Hopt κ1 Hid Hinc1) as [ζ [Hζ [Hie Hprec]]].
  (* 5. the theorem's precision, restated at [σ := ζ ∘ κ1] *)
  assert (Hσ : msubst_compose ζ κ1 ∷ Θ0 ⊑ Θ)
    by (eapply a_inc_compose; eassumption).
  assert (Hscope : a_scope_pskl Θ0 P)
    by (eapply a_wf_pskl_to_a_scope_pskl;
        [ exact HwfP | auto | intros α Hα; clear - Hα; fsetdec ]).
  assert (Heqσ : msubst_pskl (msubst_compose ζ κ1) P = msubst_pskl ζ P)
    by (exact (msubst_compose_id_pskl Hwf0 Hwf1 Hid Hinc1 Hζ Hscope)).
  unfold ad_precise in Hprec.
  rewrite msubst_bskl_pskl_to_bskl_syn, bskl_to_pskl_pskl_to_bskl_syn in Hprec.
  rewrite <- Heqσ in Hprec.
  (* 6. move it from σ to κ, and compose *)
  pose proof (a_inc_equiv_precise_msubst HwfP Hwf0 Hwfth Hinc Hσ Hie
                (Δ := empty) ltac:(clear; fsetdec)) as Hstab.
  unfold ad_precise in Hstab |- *.
  eapply ad_refine_syn_trans;
    [ exact Hprec | exact Hwfth | clear; intros α Hα; fsetdec | | exact Hstab ].
  rewrite bskl_to_pskl_pskl_to_bskl_inh.
  apply ad_refine_syn_hole_l_target_wf.
  eapply ad_refine_syn_f_forget; exact Hrs.
Qed.

Print Assumptions a_sub_complete_hole_p0_precision.

(** The one-line commutation the undecoration needs: erasing a
    metasubstituted subject is metasubstituting its erasure.  The only
    interesting node is a variable, where both sides are the image's
    [ptyp_to_pskl]. *)
Lemma uskl_to_pskl_msubst_uskl_syn : forall κ R,
  ⌊ msubst_uskl_syn κ R ⌋ˢ = msubst_pskl κ ⌊ R ⌋ˢ.
Proof.
  intros κ R; induction R; cbn; try reflexivity; try (f_equal; assumption).
  apply uskl_to_pskl_ptyp_to_uskl_syn.
Qed.

(** At [M = TI] every admissible row of [ad_pat_sub_g] carries a TAG-FREE
    consistency between the same two skeletons: [__infer] has it on the rule,
    and [__ghost] / [__ghostg] rebuild it from theirs.  Every other row is
    excluded by its mode ([M <> TI], [mode_tc], or [mode_fn M]). *)
Lemma ad_pat_sub_g_ti_consis : forall n NM Ψ Θ R Q,
  ad_pat_sub_g n NM mode_ti Ψ Θ R Q ->
  empty ⨟ Θ ⊢ₛᵃ R ∼ Q.
Proof.
  intros n NM Ψ Θ R Q H; inversion H; subst; try congruence;
    try assumption;                                       (* __infer *)
    try (apply ad_pat_consis__hole; [ reflexivity | assumption ]);  (* __ghost *)
    try (apply ad_pat_consis__ghostg; reflexivity).                 (* __ghostg *)
Qed.

(* --------------------------------------------------------------------- *)
(*  Sub-Infer                                                             *)
(* --------------------------------------------------------------------- *)

Lemma a_sub_complete_infer : forall n NM Θ0 P0 P R Ψ Θ κ Q,
  sub_complete_concl n NM mode_ti Θ0 P0 P R Ψ Θ κ Q.
Proof.
  intros n NM Θ0 P0 P R Ψ Θ κ Q.
  unfold sub_complete_concl.
  intros Hwf0 Hwfth HwfP0 HwfP HmodSK HmodTY HeqP Hinc Hsub Hrs.
  (* 0. the leaf refinement — carried by the join's TI leaf *)
  pose proof (ad_pat_sub_gv_ti_refine Hsub) as Hrp0.
  apply ad_refine_pskl_f_empty_intro in Hrp0.
  rewrite uskl_to_pskl_msubst_uskl_syn, HeqP in Hrp0.
  (* 1. [skmod] pins [P0 = □] — both mode-compatibility relations do *)
  assert (HP0 : P0 = pskl_hole).
  { destruct NM;
      [ pose proof (HmodTY eq_refl) as Hm | pose proof (HmodSK eq_refl) as Hm ];
      inversion Hm; reflexivity. }
  subst P0. cbn in Hrs.
  (* 2. the run: [Infer], which returns the input skeleton at the input ctx *)
  exists P, Θ0. split; [ apply a_sub__infer | ].
  intros κ1 Hid Hinc1. exists κ.
  destruct (opt_axiom_factor Hwf0 Hid Hinc1 Hinc) as [Hout Hfact].
  split; [ exact Hout | split; [ exact Hfact | ] ].
  (* 3. the precision, via thm:complete-consistency at [(Θ0; □; P)] *)
  unfold ad_precise.
  rewrite msubst_bskl_pskl_to_bskl_syn, bskl_to_pskl_pskl_to_bskl_syn.
  change (Θ ⨟ empty ⊢ₚᵣᵃ (msubst_pskl κ P) ⊑ (bskl_to_pskl Q)).
  (* the DECORATED premise undecorates *)
  pose proof (ad_pat_consis_strip_tags
                (ad_pat_sub_g_ti_consis (ad_pat_sub_gv_forget Hsub))) as Hc.
  rewrite uskl_to_pskl_msubst_uskl_syn, HeqP in Hc.
  exact (a_sub_complete_hole_p0_precision Hwf0 Hwfth HwfP Hinc Hc Hrs Hrp0).
Qed.

Print Assumptions a_sub_complete_infer.

(* ===================================================================== *)
(*  Sub-UnivGhostR — the row that FORCED the leaf-valid motive             *)
(*                                                                        *)
(*  Under the earlier ROOT-level subject-refinement premise this row was   *)
(*  VACUOUS: its counterpart is [∀◇.Q] and its subject GUARDED, and        *)
(*  refinement has no rule putting a [∀◇] on the RIGHT of a guarded left   *)
(*  ([ad_refine_pskl_f_tophole_r_shape] below; machine-checked coverage    *)
(*  loss in cex/cex_p7_univ_ghost_r_vacuous.v and, for the ForallL/ForallR *)
(*  analogues, cex/cex_p7_third_premise_forall.v).  The leaf-valid join    *)
(*  carries the refinement at the STRIPPED counterpart [Q] instead — which *)
(*  is exactly what the paper's own case does (:3282): invoke              *)
(*  thm:complete-consistency at [(Θ0; □; P)] against [Q], then wrap both   *)
(*  sides' [∀◇] around the resulting precision.                            *)
(* ===================================================================== *)

(** Whatever refines into a [∀◇] is itself a [◇] or a [∀◇].  No
    well-formedness is needed: the only recursive row, [__flex_l], unfolds a
    definition to a [ptyp] painting, and [ptyp_to_pskl] emits no ghost. *)
Lemma ad_refine_pskl_f_tophole_r_shape : forall F Θ Δ P Q,
  ad_refine_pskl_f F Θ Δ P (pskl_tophole Q) ->
  P = pskl_hole \/ exists P', P = pskl_tophole P'.
Proof.
  intros F Θ Δ P Q H.
  remember (pskl_tophole Q) as Qt eqn:HQ. revert Q HQ.
  induction H; intros Qx HQ; try discriminate HQ.
  - (* __hole *) left; reflexivity.
  - (* __tophole_remove *) right; eauto.
  - (* __tophole_keep *) right; eauto.
  - (* __flex_l : the unfolded definition is a painting, hence no ghost *)
    exfalso.
    destruct (IHad_refine_pskl_f Qx HQ) as [Hc | [P' Hc]];
      destruct τ; cbn in Hc; discriminate Hc.
Qed.

Print Assumptions ad_refine_pskl_f_tophole_r_shape.

(** A GUARDED unresolved skeleton erases to a guarded plain one, and in
    particular to no ghost. *)
Lemma guarded_uskl_erase_not_ghost : forall R,
  guarded_uskl R ->
  ⌊ R ⌋ˢ <> pskl_hole /\ (forall P, ⌊ R ⌋ˢ <> pskl_tophole P).
Proof.
  intros R H; inversion H; subst; cbn;
    (split; [ discriminate | intros; discriminate ]).
Qed.

(** A GUARDED metasubstituted subject has a guarded erasure.  Only the
    subject's own head matters: κ is structural at every non-variable node,
    and a variable's image is a monotype PAINTING, so a guarded [κR] forces
    [R] itself to be [unit] / a variable / an arrow. *)
Lemma guarded_uskl_msubst_erase : forall κ R,
  guarded_uskl (msubst_uskl_syn κ R) ->
  lc_pskl ⌊ R ⌋ˢ ->
  guarded_pskl ⌊ R ⌋ˢ.
Proof.
  intros κ R Hg Hlc; destruct R; cbn in Hg |- *;
    try (inversion Hg; fail);
    try (inversion Hlc; fail);
    [ apply guarded_pskl__unit
    | apply guarded_pskl__var
    | inversion Hlc; subst; apply guarded_pskl__arrow; assumption ].
Qed.

(** A [◇]-source fill into a [∀◇] strips to a fill into its body: the only
    hole-source row is [__hole], whose target is a syn painting — of a
    [pskl_tophole] here — and the painting's body inherits the wf and the
    hygiene from the whole. *)
Lemma ad_refine_syn_f_hole_tophole_inv : forall F Θ Δ Q,
  ad_refine_syn_f F Θ Δ bskl_hole (bskl_tophole Q) ->
  ad_refine_syn_f F Θ Δ bskl_hole Q.
Proof.
  intros F Θ Δ Q H; inversion H; subst.
  destruct P; cbn in *; try discriminate.
  match goal with HQ : bskl_tophole _ = bskl_tophole _ |- _ =>
    inversion HQ; subst end.
  match goal with Hwf : a_wf_pskl _ _ (pskl_tophole _) |- _ =>
    inversion Hwf; subst end.
  apply ad_refine_syn_f__hole; assumption.
Qed.

(** Guardedness survives the erase-and-repaint round trip (only the head
    constructor matters, both maps are structural at guarded heads, and both
    preserve local closure of the arrow's components). *)
Lemma guarded_bskl_inh_repaint : forall Q,
  guarded_bskl Q ->
  guarded_bskl (pskl_to_bskl_inh (bskl_to_pskl Q)).
Proof.
  intros Q H; inversion H; subst; cbn; constructor;
    apply lc_pskl_to_bskl_inh, lc_bskl_to_pskl; assumption.
Qed.

Lemma a_sub_complete_univ_ghost_r : forall n Θ0 P0 P R Ψ Θ κ Q,
  guarded_uskl (msubst_uskl_syn κ R) ->                        (* row premise *)
  guarded_bskl Q ->                                            (* row premise *)
  empty ⨟ Θ ⊢ₛᵃ (msubst_uskl_syn κ R) ∼ Q ->                   (* row premise *)
  Θ ⨟ empty ⊢ᵣₚᵃ ⌊ msubst_uskl_syn κ R ⌋ˢ ⊳ (bskl_to_pskl Q) -> (* leaf refinement *)
  sub_complete_concl n a_sub_mode_sk mode_tc Θ0 P0 P R Ψ Θ κ (bskl_tophole Q).
Proof.
  intros n Θ0 P0 P R Ψ Θ κ Q HgR HgQ Hrow Hrfn.
  unfold sub_complete_concl.
  intros Hwf0 Hwfth HwfP0 HwfP HmodSK HmodTY HeqP Hinc Hsub Hrs.
  (* 1. [skmod[SK]] pins [P0 = □] *)
  assert (HP0 : P0 = pskl_hole)
    by (pose proof (HmodSK eq_refl) as Hm; inversion Hm; reflexivity).
  subst P0. cbn in Hrs.
  (* 2. the subject skeleton is guarded, so the run is [UnivGhostR] *)
  assert (HgP : guarded_pskl P).
  { rewrite <- HeqP. eapply guarded_uskl_msubst_erase;
      [ exact HgR | rewrite HeqP; eapply a_wf_pskl_lc; exact HwfP ]. }
  exists (pskl_tophole P), Θ0.
  split; [ apply a_sub__univ_ghost_r; exact HgP | ].
  intros κ1 Hid Hinc1. exists κ.
  destruct (opt_axiom_factor Hwf0 Hid Hinc1 Hinc) as [Hout Hfact].
  split; [ exact Hout | split; [ exact Hfact | ] ].
  (* 3. the precision at the STRIPPED counterpart, via the shared core *)
  assert (Hc : empty ⨟ Θ ⊢ₛᵃ (pskl_to_uskl (msubst_pskl κ P)) ∼ Q).
  { pose proof (ad_pat_consis_strip_tags Hrow) as H.
    rewrite uskl_to_pskl_msubst_uskl_syn, HeqP in H. exact H. }
  assert (Hrs' : ad_refine_syn_f empty Θ empty bskl_hole Q)
    by (apply ad_refine_syn_f_hole_tophole_inv; exact Hrs).
  assert (Hrp : ad_refine_pskl_f empty Θ empty
                  (msubst_pskl κ P) (bskl_to_pskl Q)).
  { pose proof (ad_refine_pskl_f_empty_intro Hrfn) as H.
    rewrite uskl_to_pskl_msubst_uskl_syn, HeqP in H. exact H. }
  pose proof (a_sub_complete_hole_p0_precision Hwf0 Hwfth HwfP Hinc Hc Hrs' Hrp)
    as Hcore.
  (* 4. wrap both sides' [∀◇] *)
  unfold ad_precise in Hcore |- *.
  rewrite msubst_bskl_pskl_to_bskl_syn.
  cbn [msubst_pskl bskl_to_pskl pskl_to_bskl_inh].
  rewrite bskl_to_pskl_pskl_to_bskl_syn.
  apply ad_refine_syn__tophole_keep;
    [ apply guarded_bskl_inh_repaint; exact HgQ | exact Hcore ].
Qed.

Print Assumptions a_sub_complete_univ_ghost_r.

(* ===================================================================== *)
(*  Sub-Check — THE SAME SHAPE ONE LEVEL UP                               *)
(*                                                                        *)
(*  [a_consis_complete_thm] supplies BOTH the run (algorithmic [Check] is  *)
(*  a consistency run under [a_consis_chk]) and the two increase           *)
(*  conjuncts.  The PRECISION, on the other hand, is free: [a_sub__check]  *)
(*  outputs [P0] itself, so the goal is [κ'P0 ⊑ ⌊Q⌋] — and at [Q =         *)
(*  inh{B}] the motive's P0-FILL premise IS [κP0 ⊑ B] by definition of     *)
(*  [ad_precise].  All that is left is to move it from κ to the package's  *)
(*  ζ, which is the stability lemma again (in the FLIPPED direction) plus  *)
(*  [ad_refine_syn_trans].                                                 *)
(*                                                                        *)
(*  So this case does NOT need [a_consis_concrete_output_equiv] after all: *)
(*  the plan routed the precision through the consistency OUTPUT, but the  *)
(*  algorithm never returns that output — [a_sub__check] hides it          *)
(*  existentially inside [a_consis_chk] and returns [P0] (the note at      *)
(*  DESIGN §9.1's end already observed this; what it did not observe is    *)
(*  that the fill premise then closes the goal outright).                  *)
(*                                                                        *)
(*  TWO SIDE CONDITIONS THE MOTIVE DOES NOT CARRY, both external-wf in    *)
(*  the sense of docs/WF-SIDE-CONDITIONS.md, both to be supplied by the    *)
(*  bundle:                                                               *)
(*                                                                        *)
(*   · [guarded_pskl P0].  The DECLARATIVE [__check] row does not pin      *)
(*     [P0]'s shape, but the ALGORITHM dispatches on it: a ∀ [P0] is       *)
(*     [ForallR], not [Check].  This is the paper's own case split, not a  *)
(*     new hypothesis.                                                    *)
(*   · [Θ ⨟ ∅ ⊢ₚₛᵃ B], well-formedness of the COUNTERPART in the solution  *)
(*     context.  [ad_refine_syn_trans] needs it (refinement is not         *)
(*     transitive without it — cex_refine_not_transitive.v) and no         *)
(*     judgment produces it; the paper requires it in prose.  At [P0 = □]  *)
(*     it came for free ([ad_refine_syn_hole_l_target_wf]); here it does   *)
(*     not.                                                                *)
(* ===================================================================== *)

Lemma a_sub_complete_check : forall n Θ0 P0 P R Ψ Θ κ B,
  guarded_uskl (msubst_uskl_syn κ R) ->                       (* row premise *)
  guarded_pskl B ->                                           (* row premise *)
  Ψ ⨟ Θ ⊢ₛᵃ (msubst_uskl_syn κ R) ∼ (pskl_to_bskl_inh B) ->   (* row premise *)
  Θ ⨟ empty ⊢ᵣₚᵃ ⌊ msubst_uskl_syn κ R ⌋ˢ ⊳ B ->              (* leaf refinement *)
  guarded_pskl P0 ->                    (* the algorithm's Check/ForallR split *)
  Θ ⨟ empty ⊢ₚₛᵃ B ->                   (* external wf of the counterpart *)
  sub_complete_concl n a_sub_mode_ty mode_tc Θ0 P0 P R Ψ Θ κ (pskl_to_bskl_inh B).
Proof.
  intros n Θ0 P0 P R Ψ Θ κ B HgR HgB Hrow Hrfn HgP0 HwfB.
  unfold sub_complete_concl.
  intros Hwf0 Hwfth HwfP0 HwfP HmodSK HmodTY HeqP Hinc Hsub Hrs.
  (* the leaf refinement, in the [_f] shape thm:complete-consistency takes *)
  assert (Hrp : ad_refine_pskl_f empty Θ empty
                  (msubst_pskl κ P) (bskl_to_pskl (pskl_to_bskl_inh B))).
  { rewrite bskl_to_pskl_pskl_to_bskl_inh.
    pose proof (ad_refine_pskl_f_empty_intro Hrfn) as H.
    rewrite uskl_to_pskl_msubst_uskl_syn, HeqP in H. exact H. }
  (* the algorithm's input skeleton is guarded *)
  assert (HgP : guarded_pskl P).
  { rewrite <- HeqP. eapply guarded_uskl_msubst_erase;
      [ exact HgR | rewrite HeqP; eapply a_wf_pskl_lc; exact HwfP ]. }
  (* the DECORATED premise undecorates, then thm:complete-consistency runs *)
  assert (Hc : empty ⨟ Θ ⊢ₛᵃ (pskl_to_uskl (msubst_pskl κ P))
                            ∼ (pskl_to_bskl_inh B)).
  { pose proof (ad_pat_consis_strip_tags Hrow) as H.
    rewrite uskl_to_pskl_msubst_uskl_syn, HeqP in H. exact H. }
  destruct (a_consis_complete_thm empty Hwf0 HwfP0 HwfP Hinc Hwfth Hc Hrs Hrp)
    as [P1 [Θ1 [Hrun Hopt]]].
  destruct (a_consis_sound_aux Hrun Hwf0 HwfP0 HwfP
              ltac:(intros α Hα; clear - Hα; fsetdec)
              ltac:(intros β τ Hb; apply inter_empty_pointwise;
                    intros α Hα; clear - Hα; fsetdec)
              ltac:(intros Θa β b Θb Heq Hne;
                    apply inter_empty_pointwise;
                    intros α Hα; clear - Hα; fsetdec))
    as [_ [Hwf1 _]].
  (* the run: algorithmic [Check], whose output IS [P0] *)
  exists P0, Θ1. split;
    [ apply a_sub__check; [ exact HgP | exact HgP0 | exists P1; exact Hrun ] | ].
  intros κ1 Hid Hinc1.
  destruct (Hopt κ1 Hid Hinc1) as [ζ [Hζ [Hie Hprec]]].
  exists ζ. split; [ exact Hζ | split; [ exact Hie | ] ].
  (* the precision: the P0-FILL premise, moved from κ to ζ *)
  assert (Hσ : msubst_compose ζ κ1 ∷ Θ0 ⊑ Θ)
    by (eapply a_inc_compose; eassumption).
  assert (Hscope : a_scope_pskl Θ0 P0)
    by (eapply a_wf_pskl_to_a_scope_pskl;
        [ exact HwfP0 | auto | intros α Hα; clear - Hα; fsetdec ]).
  assert (Heqσ : msubst_pskl (msubst_compose ζ κ1) P0 = msubst_pskl ζ P0)
    by (exact (msubst_compose_id_pskl Hwf0 Hwf1 Hid Hinc1 Hζ Hscope)).
  pose proof (a_inc_equiv_precise_msubst_flip HwfP0 Hwf0 Hwfth Hinc Hσ Hie
                (Δ := empty) ltac:(clear; fsetdec)) as Hstab.
  rewrite Heqσ in Hstab.
  unfold ad_precise in Hstab |- *.
  rewrite msubst_bskl_pskl_to_bskl_syn, bskl_to_pskl_pskl_to_bskl_syn.
  rewrite bskl_to_pskl_pskl_to_bskl_inh.
  eapply ad_refine_syn_trans;
    [ eapply ad_refine_syn_f_forget; exact Hrs
    | exact Hwfth | clear; intros α Hα; fsetdec
    | rewrite bskl_to_pskl_pskl_to_bskl_inh; exact HwfB
    | exact Hstab ].
Qed.

Print Assumptions a_sub_complete_check.
