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
Require Import src.frost.algo.prop_decorate_sub.  (* lc_uskl_of_pskl *)
Require Import src.frost.algo.prop_normal.        (* a_inc_equiv_lookup (the a_binds_tvar form) *)
Require Import src.frost.algo.prop_mono_bridge.   (* ptyp_to_bskl_inh_syn_eq *)
Require Import src.frost.algo.prop_precise_recover. (* tyequiv_mono_refine_syn *)
Require Import src.frost.algo.prop_pat_sub.       (* uskl_to_pskl_ptyp_to_uskl_syn *)
Require Import src.frost.algo.prop_sub_msubst_equiv. (* ≡ᵘ + erasure + generation *)
Require Import src.frost.algo.prop_stability.     (* a_wf_pskl_isub *)
Require Import src.frost.algo.prop_inc_strengthen. (* a_assign_unify_consis_flex_preserve *)
Require Import src.frost.algo.prop_decorate_key.  (* a_sub_sound_thm *)

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
    every P5/P6 invocation.

    THE ≡ᵘ SLACK (2026-07-31).  The join is carried at an arbitrary subject
    [R'] with [Θ ⊢ R' ≡ᵘ κR] rather than at [κR] itself.  Sub-Arrow (and later
    ForallR / P7a) re-enter the IH after the domain's run has advanced Θ0 to
    Θ1 and swapped κ for the package's ζ1; the paper does this "informally by
    type equivalence" (its author's own margin note).  With the slack the IH
    takes the ORIGINAL join derivation and only the LEAVES transport, via
    [a_uskl_tyequiv_erase] + the pskl-level skl_tyequiv transports
    (prop_sub_msubst_equiv.v; prop_consis_complete.v). *)
Definition sub_complete_concl
  (n : nat) (NM : a_sub_mode) (M : mode)
  (Θ0 : aenv) (P0 P : pskl) (R R' : uskl) (Ψ : atoms)
  (Θ : aenv) (κ : metasubst) (Q : bskl) : Prop :=
  (* ---- inputs are well formed, and mode-compatible with P0 ---- *)
  a_wf_aenv Θ0 -> a_wf_aenv Θ ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->   (* skmod[SK]{P0}{M} *)
  (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->   (* skmod[TY]{P0}{M} *)
  (* ---- the unresolved subject erases to the algorithm's input ---- *)
  ⌊ R ⌋ˢ = P ->
  (* ---- the solution: an increase, the LEAF-VALID join (at a subject
          ≡ᵘ-equivalent to the κ-image), and the P0-fill ---- *)
  κ ∷ Θ0 ⊑ Θ ->
  Θ ⊢ R' ≡ᵘ (msubst_uskl_syn κ R) ->
  ad_pat_sub_gv n NM M Ψ Θ R' Q ->
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
  (Θ0 Ξ : aenv) (α : atom) (P0 : pskl) (R' : uskl) (Ψ : atoms)
  (Θ : aenv) (κ : metasubst) (Q : bskl) : Prop :=
  a_decls Ξ ->                                  (* Ξ holds only flexible decls *)
  a_wf_aenv (Ξ ++ Θ0) -> a_wf_aenv Θ ->
  (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P0 ->
  a_flex_tvar (Ξ ++ Θ0) α ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat (mode_fn M) P0) ->
  (NM = a_sub_mode_ty -> a_ty_mode_compat (mode_fn M) P0) ->
  κ ∷ (Ξ ++ Θ0) ⊑ Θ ->
  (* the subject is [syn{κα̂}] — a monotype painting, not an unresolved R;
     the join is the LEAF-VALID mirror at a ≡ᵘ-equivalent subject (see
     [sub_complete_concl]'s note) *)
  Θ ⊢ R' ≡ᵘ (ptyp_to_uskl_syn (msubst_lookup κ α)) ->
  ad_pat_sub_gv n NM (mode_fn M) Ψ Θ R' Q ->
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
    (forall NM M Θ0 P0 P R R' Ψ Θ κ Q,
       sub_complete_concl n NM M Θ0 P0 P R R' Ψ Θ κ Q) /\
    (forall NM M Θ0 Ξ α P0 R' Ψ Θ κ Q,
       sub_flex_complete_concl n NM M Θ0 Ξ α P0 R' Ψ Θ κ Q).

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

Lemma a_sub_complete_ghost : forall n M Θ0 P0 P R R' Ψ Θ κ Q,
  R' = uskl_hole ->
  sub_complete_concl n a_sub_mode_sk M Θ0 P0 P R R' Ψ Θ κ Q.
Proof.
  intros n M Θ0 P0 P R R' Ψ Θ κ Q HT.
  unfold sub_complete_concl.
  intros Hwf0 Hwfth HwfP0 HwfP HmodSK HmodTY HeqP Hinc Hrel Hsub Hrs.
  subst R'.
  (* a ghost is ≡ᵘ-inert, so the κ-image is the hole as well *)
  pose proof (a_uskl_tyequiv_hole_l_inv Hrel) as Hsubj.
  apply ad_pat_sub_gv_forget in Hsub.
  (* the subject is the hole, so the algorithm's input is [□] *)
  pose proof (msubst_uskl_syn_hole_inv κ R Hsubj) as HR; subst R.
  cbn in HeqP; subst P.
  (* the counterpart is an inherited painting — read off the derivation *)
  assert (HQ : pskl_to_bskl_inh (bskl_to_pskl Q) = Q)
    by (eapply ad_pat_sub_g_hole_target_inh; exact Hsub).
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

Lemma a_sub_complete_ghostg : forall n M Θ0 P0 P R R' Ψ Θ κ Q,
  R' = uskl_holeg ->
  sub_complete_concl n a_sub_mode_sk M Θ0 P0 P R R' Ψ Θ κ Q.
Proof.
  intros n M Θ0 P0 P R R' Ψ Θ κ Q HT.
  unfold sub_complete_concl.
  intros Hwf0 Hwfth HwfP0 HwfP HmodSK HmodTY HeqP Hinc Hrel Hsub Hrs.
  subst R'.
  pose proof (a_uskl_tyequiv_holeg_l_inv Hrel) as Hsubj.
  apply ad_pat_sub_gv_forget in Hsub.
  pose proof (msubst_uskl_syn_holeg_inv κ R Hsubj) as HR; subst R.
  cbn in HeqP; subst P.
  assert (HQ : pskl_to_bskl_inh (bskl_to_pskl Q) = Q)
    by (eapply ad_pat_sub_g_holeg_target_inh; exact Hsub).
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

Lemma a_sub_complete_infer : forall n NM Θ0 P0 P R R' Ψ Θ κ Q,
  sub_complete_concl n NM mode_ti Θ0 P0 P R R' Ψ Θ κ Q.
Proof.
  intros n NM Θ0 P0 P R R' Ψ Θ κ Q.
  unfold sub_complete_concl.
  intros Hwf0 Hwfth HwfP0 HwfP HmodSK HmodTY HeqP Hinc Hrel Hsub Hrs.
  (* the ≡ᵘ slack, erased at the algorithm's input *)
  pose proof (a_uskl_tyequiv_erase Hrel) as Herase.
  rewrite uskl_to_pskl_msubst_uskl_syn, HeqP in Herase.
  (* 0. the leaf refinement — carried by the join's TI leaf, moved to κP *)
  pose proof (ad_pat_sub_gv_ti_refine Hsub) as Hrp0.
  apply ad_refine_pskl_f_empty_intro in Hrp0.
  destruct (skl_tyequiv_refine_pskl_f_transport Herase Hwfth
              (fun x b Hb => Hb)) as [Hrpt _].
  pose proof (Hrpt _ _ _ Hrp0) as Hrp1.
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
  (* the DECORATED premise undecorates, then the slack moves it to κP *)
  pose proof (ad_pat_consis_strip_tags
                (ad_pat_sub_g_ti_consis (ad_pat_sub_gv_forget Hsub))) as Hc0.
  destruct (skl_tyequiv_consis_transport Herase Hwfth
              (fun x b Hb => Hb)) as [Hct _].
  pose proof (Hct _ _ Hc0) as Hc.
  exact (a_sub_complete_hole_p0_precision Hwf0 Hwfth HwfP Hinc Hc Hrs Hrp1).
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

Lemma a_sub_complete_univ_ghost_r : forall n Θ0 P0 P R R' Ψ Θ κ Q,
  guarded_uskl R' ->                                            (* row premise *)
  guarded_bskl Q ->                                            (* row premise *)
  empty ⨟ Θ ⊢ₛᵃ R' ∼ Q ->                                       (* row premise *)
  Θ ⨟ empty ⊢ᵣₚᵃ ⌊ R' ⌋ˢ ⊳ (bskl_to_pskl Q) ->                  (* leaf refinement *)
  sub_complete_concl n a_sub_mode_sk mode_tc Θ0 P0 P R R' Ψ Θ κ (bskl_tophole Q).
Proof.
  intros n Θ0 P0 P R R' Ψ Θ κ Q HgT HgQ Hrow Hrfn.
  unfold sub_complete_concl.
  intros Hwf0 Hwfth HwfP0 HwfP HmodSK HmodTY HeqP Hinc Hrel Hsub Hrs.
  (* the ≡ᵘ slack, erased at the algorithm's input *)
  pose proof (a_uskl_tyequiv_erase Hrel) as Herase.
  rewrite uskl_to_pskl_msubst_uskl_syn, HeqP in Herase.
  (* 1. [skmod[SK]] pins [P0 = □] *)
  assert (HP0 : P0 = pskl_hole)
    by (pose proof (HmodSK eq_refl) as Hm; inversion Hm; reflexivity).
  subst P0. cbn in Hrs.
  (* 2. the subject skeleton is guarded, so the run is [UnivGhostR] *)
  assert (HgP : guarded_pskl P).
  { rewrite <- HeqP. eapply guarded_uskl_msubst_erase;
      [ eapply a_uskl_tyequiv_guarded; [ exact Hrel | exact HgT ]
      | rewrite HeqP; eapply a_wf_pskl_lc; exact HwfP ]. }
  exists (pskl_tophole P), Θ0.
  split; [ apply a_sub__univ_ghost_r; exact HgP | ].
  intros κ1 Hid Hinc1. exists κ.
  destruct (opt_axiom_factor Hwf0 Hid Hinc1 Hinc) as [Hout Hfact].
  split; [ exact Hout | split; [ exact Hfact | ] ].
  (* 3. the precision at the STRIPPED counterpart, via the shared core;
        the slack moves both leaf facts from [R'] to [κP] *)
  assert (Hc : empty ⨟ Θ ⊢ₛᵃ (pskl_to_uskl (msubst_pskl κ P)) ∼ Q).
  { pose proof (ad_pat_consis_strip_tags Hrow) as H0.
    destruct (skl_tyequiv_consis_transport Herase Hwfth
                (fun x b Hb => Hb)) as [Hct _].
    exact (Hct _ _ H0). }
  assert (Hrs' : ad_refine_syn_f empty Θ empty bskl_hole Q)
    by (apply ad_refine_syn_f_hole_tophole_inv; exact Hrs).
  assert (Hrp : ad_refine_pskl_f empty Θ empty
                  (msubst_pskl κ P) (bskl_to_pskl Q)).
  { pose proof (ad_refine_pskl_f_empty_intro Hrfn) as H0.
    destruct (skl_tyequiv_refine_pskl_f_transport Herase Hwfth
                (fun x b Hb => Hb)) as [Hrpt _].
    exact (Hrpt _ _ _ H0). }
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

Lemma a_sub_complete_check : forall n Θ0 P0 P R R' Ψ Θ κ B,
  guarded_uskl R' ->                                           (* row premise *)
  guarded_pskl B ->                                           (* row premise *)
  Ψ ⨟ Θ ⊢ₛᵃ R' ∼ (pskl_to_bskl_inh B) ->                       (* row premise *)
  Θ ⨟ empty ⊢ᵣₚᵃ ⌊ R' ⌋ˢ ⊳ B ->                                (* leaf refinement *)
  guarded_pskl P0 ->                    (* the algorithm's Check/ForallR split *)
  Θ ⨟ empty ⊢ₚₛᵃ B ->                   (* external wf of the counterpart *)
  sub_complete_concl n a_sub_mode_ty mode_tc Θ0 P0 P R R' Ψ Θ κ (pskl_to_bskl_inh B).
Proof.
  intros n Θ0 P0 P R R' Ψ Θ κ B HgT HgB Hrow Hrfn HgP0 HwfB.
  unfold sub_complete_concl.
  intros Hwf0 Hwfth HwfP0 HwfP HmodSK HmodTY HeqP Hinc Hrel Hsub Hrs.
  (* the ≡ᵘ slack, erased at the algorithm's input *)
  pose proof (a_uskl_tyequiv_erase Hrel) as Herase.
  rewrite uskl_to_pskl_msubst_uskl_syn, HeqP in Herase.
  (* the leaf refinement, in the [_f] shape thm:complete-consistency takes *)
  assert (Hrp : ad_refine_pskl_f empty Θ empty
                  (msubst_pskl κ P) (bskl_to_pskl (pskl_to_bskl_inh B))).
  { rewrite bskl_to_pskl_pskl_to_bskl_inh.
    pose proof (ad_refine_pskl_f_empty_intro Hrfn) as H0.
    destruct (skl_tyequiv_refine_pskl_f_transport Herase Hwfth
                (fun x b Hb => Hb)) as [Hrpt _].
    exact (Hrpt _ _ _ H0). }
  (* the algorithm's input skeleton is guarded *)
  assert (HgP : guarded_pskl P).
  { rewrite <- HeqP. eapply guarded_uskl_msubst_erase;
      [ eapply a_uskl_tyequiv_guarded; [ exact Hrel | exact HgT ]
      | rewrite HeqP; eapply a_wf_pskl_lc; exact HwfP ]. }
  (* the DECORATED premise undecorates, then the slack moves it to κP *)
  assert (Hc : empty ⨟ Θ ⊢ₛᵃ (pskl_to_uskl (msubst_pskl κ P))
                            ∼ (pskl_to_bskl_inh B)).
  { pose proof (ad_pat_consis_strip_tags Hrow) as H0.
    destruct (skl_tyequiv_consis_transport Herase Hwfth
                (fun x b Hb => Hb)) as [Hct _].
    exact (Hct _ _ H0). }
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

(* ===================================================================== *)
(*  Sub-Arrow (paper :3295-3419) — thm:complete-consistency on the        *)
(*  DOMAIN, the fuel-n IH on the CODOMAIN at the domain package's ζ1,      *)
(*  mirroring the consistency Arrow case (prop_consis_complete.v:6631):    *)
(*  the codomain's premises transport SEMANTICALLY at the fixed Θ — the    *)
(*  fill along ≡ˢ, the join via the motive's ≡ᵘ slack — and the domain     *)
(*  precision moves ζ1 → ζ2 by the same ≡ˢ route (scope from              *)
(*  [ad_pat_consis_target_wf]; no new wf side conditions).                 *)
(* ===================================================================== *)

(** The syn mirror of [ad_refine_pskl_f_empty_intro]. *)
Lemma ad_refine_syn_f_empty_intro : forall Θ Δ Q Q',
  Θ ⨟ Δ ⊢ᵣᵃ Q ⊳ Q' ->
  ad_refine_syn_f empty Θ Δ Q Q'.
Proof.
  intros Θ Δ Q Q' H; induction H.
  - apply ad_refine_syn_f__unit.
  - apply ad_refine_syn_f__var; assumption.
  - apply ad_refine_syn_f__arrow; assumption.
  - eapply ad_refine_syn_f__all; eauto.
  - apply ad_refine_syn_f__hole; [ clear; fsetdec | assumption ].
  - apply ad_refine_syn_f__tophole_remove; assumption.
  - eapply ad_refine_syn_f__tophole_fill; eauto.
  - apply ad_refine_syn_f__tophole_keep; assumption.
  - eapply ad_refine_syn_f__flex_l; eauto.
  - eapply ad_refine_syn_f__flex_r; eauto.
Qed.

(** Every variable of a Δ-closed well-formed skeleton is Θ-bound. *)
Lemma a_wf_pskl_ftv_binds_tvar : forall Θ Δ P α,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  α `in` ftvar_in_pskl P ->
  α `in` Δ \/ a_binds_tvar α Θ.
Proof.
  intros Θ Δ P α Hwf; revert α; induction Hwf; intros α0 Hα; cbn in Hα.
  - exfalso; clear - Hα; fsetdec.
  - assert (Heq : α0 = α) by (clear - Hα; fsetdec). subst α0. exact H.
  - apply union_1 in Hα; destruct Hα as [Hα | Hα];
      [ apply IHHwf1 | apply IHHwf2 ]; exact Hα.
  - pick fresh β.
    assert (Hα' : α0 `in` ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f β)))
      by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_lower P (pskl_var_f β));
          clear - Hα H1; fsetdec).
    destruct (H0 β ltac:(clear - Fr; fsetdec) α0 Hα') as [Hin | Hb];
      [ | right; exact Hb ].
    left. assert (Hne : α0 <> β) by (clear - Fr Hα; fsetdec).
    clear - Hin Hne; fsetdec.
  - exfalso; clear - Hα; fsetdec.
  - destruct (IHHwf α0 Hα) as [Hin | Hb];
      [ exfalso; clear - Hin; fsetdec | right; exact Hb ].
Qed.

(** Composing with an identity collapses on the identity's domain. *)
Lemma msubst_compose_id_lookup : forall w ζ α,
  is_id_msubst w ->
  α `in` dom w ->
  msubst_lookup (msubst_compose ζ w) α = msubst_lookup ζ α.
Proof.
  induction w as [ | [β τ] w' IHw ]; intros ζ α Hid Hα; cbn in *.
  - exfalso; clear - Hα; fsetdec.
  - inversion Hid; subst.
    match goal with
    | Hie : is_id_entry _ |- _ =>
        unfold is_id_entry in Hie; cbn in Hie; subst τ
    end.
    lazymatch goal with
    | |- context [ if ?c then _ else _ ] => destruct c as [Heq | Hne]
    end.
    + subst. cbn. reflexivity.
    + apply IHw; [ assumption | clear - Hα Hne; fsetdec ].
Qed.

Lemma msubst_uskl_syn_compose_id : forall R w ζ,
  is_id_msubst w ->
  (forall α, α `in` ftvar_in_uskl R ->
     α `in` dom w \/ (α `notin` dom w /\ α `notin` dom ζ)) ->
  msubst_uskl_syn (msubst_compose ζ w) R = msubst_uskl_syn ζ R.
Proof.
  intros R w ζ Hid Hcov. apply msubst_uskl_syn_agree.
  intros α Hα. destruct (Hcov α Hα) as [Hin | [Hw Hζ]].
  - apply msubst_compose_id_lookup; assumption.
  - rewrite (msubst_lookup_notin ζ Hζ).
    apply msubst_lookup_notin.
    pose proof (dom_msubst_compose ζ w) as Hd.
    clear - Hw Hd; fsetdec.
Qed.

Lemma a_sub_complete_arrow : forall n NM M Θ0 P0 P Ra Rb R1' R2' Ψ Θ κ Q1 Q2,
  (forall NM' M' Θ0' P0' P' R'' T'' Ψ' Θ' κ' Q',
     sub_complete_concl n NM' M' Θ0' P0' P' R'' T'' Ψ' Θ' κ' Q') ->
  sub_complete_concl (S n) NM (mode_fn M) Θ0 P0 P (uskl_arrow Ra Rb)
    (uskl_arrow R1' R2') Ψ Θ κ (bskl_arrow Q1 Q2).
Proof.
  intros n NM M Θ0 P0 P Ra Rb R1' R2' Ψ Θ κ Q1 Q2 IH.
  unfold sub_complete_concl.
  intros Hwf0 Hwfth HwfP0 HwfP HmodSK HmodTY HeqP Hinc Hrel Hsub Hrs.
  cbn in HeqP. subst P.
  cbn in Hrel.
  destruct (a_uskl_tyequiv_arrow_arrow_inv Hwfth Hrel) as [Hrel1 Hrel2].
  (* the join's last rule is [__arrow]; read its fields off *)
  inversion Hsub; subst.
  match goal with
  | Hj : _ ⨟ Θ ⊢ₛᵃ R1' ∼ Q1,
    Hlf : Θ ⨟ empty ⊢ᵣₚᵃ ⌊ R1' ⌋ˢ ⊳ _,
    Hs2 : ad_pat_sub_gv _ _ _ _ Θ R2' Q2 |- _ =>
      rename Hj into Hj1; rename Hlf into Hrfn1; rename Hs2 into Hsub2
  end.
  (* P0 is an arrow, and the codomain keeps its mode-compatibility *)
  assert (Hsplit : exists P0a P0b, P0 = pskl_arrow P0a P0b /\
            (NM = a_sub_mode_sk -> a_sk_mode_compat M P0b) /\
            (NM = a_sub_mode_ty -> a_ty_mode_compat M P0b)).
  { destruct NM.
    - pose proof (HmodTY eq_refl) as Hm; inversion Hm; subst.
      do 2 eexists. split; [ reflexivity | ].
      split; [ intro Hc; discriminate Hc | intro; assumption ].
    - pose proof (HmodSK eq_refl) as Hm; inversion Hm; subst.
      do 2 eexists. split; [ reflexivity | ].
      split; [ intro; assumption | intro Hc; discriminate Hc ]. }
  destruct Hsplit as [P0a [P0b [-> [HmodSKb HmodTYb]]]].
  (* wf components *)
  assert (HwfP0a : Θ0 ⨟ empty ⊢ₚₛᵃ P0a) by (inversion HwfP0; assumption).
  assert (HwfP0b : Θ0 ⨟ empty ⊢ₚₛᵃ P0b) by (inversion HwfP0; assumption).
  assert (HwfPa : Θ0 ⨟ empty ⊢ₚₛᵃ ⌊ Ra ⌋ˢ) by (inversion HwfP; assumption).
  assert (HwfPb : Θ0 ⨟ empty ⊢ₚₛᵃ ⌊ Rb ⌋ˢ) by (inversion HwfP; assumption).
  (* the fill splits into the components *)
  cbn in Hrs.
  inversion Hrs; subst.
  match goal with
  | Ha : ad_refine_syn_f empty Θ empty
           (pskl_to_bskl_inh (msubst_pskl κ P0a)) Q1,
    Hb : ad_refine_syn_f empty Θ empty
           (pskl_to_bskl_inh (msubst_pskl κ P0b)) Q2 |- _ =>
      rename Ha into Hrs1; rename Hb into Hrs2
  end.
  (* ---- DOMAIN: thm:complete-consistency at (Θ0; P0a; ⌊Ra⌋) ---- *)
  pose proof (a_uskl_tyequiv_erase Hrel1) as Herase1.
  rewrite uskl_to_pskl_msubst_uskl_syn in Herase1.
  assert (Hc1 : empty ⨟ Θ ⊢ₛᵃ (pskl_to_uskl (msubst_pskl κ ⌊ Ra ⌋ˢ)) ∼ Q1).
  { pose proof (ad_pat_consis_strip_tags Hj1) as H0.
    destruct (skl_tyequiv_consis_transport Herase1 Hwfth
                (fun x b Hb => Hb)) as [Hct _].
    exact (Hct _ _ H0). }
  assert (Hrp1 : ad_refine_pskl_f empty Θ empty
                   (msubst_pskl κ ⌊ Ra ⌋ˢ) (bskl_to_pskl Q1)).
  { pose proof (ad_refine_pskl_f_empty_intro Hrfn1) as H0.
    destruct (skl_tyequiv_refine_pskl_f_transport Herase1 Hwfth
                (fun x b Hb => Hb)) as [Hrpt _].
    exact (Hrpt _ _ _ H0). }
  destruct (a_consis_complete_thm empty Hwf0 HwfP0a HwfPa Hinc Hwfth Hc1
              Hrs1 Hrp1)
    as [Q1' [Θ1 [Hrun1 Hopt1]]].
  (* the domain run's soundness: id-witness, wf, join at Θ1 *)
  destruct (a_consis_sound_aux Hrun1 Hwf0 HwfP0a HwfPa
              ltac:(intros α Hα; clear - Hα; fsetdec)
              ltac:(intros β τ Hb; apply inter_empty_pointwise;
                    intros α Hα; clear - Hα; fsetdec)
              ltac:(intros Θa β b Θb Heq Hne;
                    apply inter_empty_pointwise;
                    intros α Hα; clear - Hα; fsetdec))
    as [[[w1 [Hidw1 Hincw1]] Hdefs1] [Hwf1 [_ [_ [Hsol1 _]]]]].
  destruct (Hopt1 w1 Hidw1 Hincw1) as [ζ1 [Hζ1 [Hie1 Hprec1]]].
  (* ---- CODOMAIN premises at (Θ1, ζ1) ---- *)
  assert (HwfP0b1 : Θ1 ⨟ empty ⊢ₚₛᵃ P0b).
  { eapply a_wf_pskl_isub; [ exact HwfP0b | ].
    split; [ exists w1; split; assumption | exact Hdefs1 ]. }
  assert (HwfPb1 : Θ1 ⨟ empty ⊢ₚₛᵃ ⌊ Rb ⌋ˢ).
  { eapply a_wf_pskl_isub; [ exact HwfPb | ].
    split; [ exists w1; split; assumption | exact Hdefs1 ]. }
  assert (Hσ : msubst_compose ζ1 w1 ∷ Θ0 ⊑ Θ)
    by (eapply a_inc_compose; eassumption).
  assert (Hlcκ : msubst_lc κ) by (eapply a_inc_msubst_lc; exact Hinc).
  assert (Hlcζ1 : msubst_lc ζ1) by (eapply a_inc_msubst_lc; exact Hζ1).
  assert (Hlcc1 : msubst_lc (msubst_compose ζ1 w1))
    by (apply msubst_lc_compose;
        [ exact Hlcζ1 | eapply is_id_msubst_values_lc; exact Hidw1 ]).
  (* every variable of Rb is Θ0-bound *)
  assert (Hcov : forall α, α `in` ftvar_in_uskl Rb -> a_binds_tvar α Θ0).
  { intros α Hα.
    assert (Hα' : α `in` ftvar_in_pskl ⌊ Rb ⌋ˢ)
      by (rewrite ftvar_in_pskl_uskl_to_pskl; exact Hα).
    destruct (a_wf_pskl_ftv_binds_tvar HwfPb Hα') as [Hin | Hb];
      [ exfalso; clear - Hin; fsetdec | exact Hb ]. }
  (* a rigid is outside both identity and package domains *)
  assert (Hnotflex : forall α, binds α abind_tvar Θ0 ->
            α `notin` dom w1 /\ α `notin` dom ζ1).
  { intros α Hb. split.
    - intros Hα. pose proof (a_inc_dom_flex Hincw1 Hα) as Hf.
      destruct Hf as [Hb' | [τ Hb']];
        pose proof (binds_unique _ _ _ _ _ Hb Hb'
                      (a_wf_aenv_uniq Hwf0)) as Hc;
        discriminate Hc.
    - intros Hα. pose proof (a_inc_dom_flex Hζ1 Hα) as Hf.
      assert (Hb1 : binds α abind_tvar Θ1)
        by (eapply a_inc_binds_tvar; [ exact Hincw1 | exact Hb ]).
      destruct Hf as [Hb' | [τ Hb']];
        pose proof (binds_unique _ _ _ _ _ Hb1 Hb'
                      (a_wf_aenv_uniq Hwf1)) as Hc;
        discriminate Hc. }
  (* the SLACK for the IH: R2' is ≡ᵘ the ζ1-image of Rb *)
  assert (Hlcb : lc_uskl Rb)
    by (apply lc_uskl_of_pskl; eapply a_wf_pskl_lc; exact HwfPb).
  assert (Hgen : Θ ⊢ (msubst_uskl_syn κ Rb) ≡ᵘ
                     (msubst_uskl_syn (msubst_compose ζ1 w1) Rb)).
  { eapply a_inc_equiv_msubst_uskl;
      [ exact Hlcb
      | intros α Hα; left; apply Hcov; exact Hα
      | exact Hie1 | exact Hinc | exact Hσ | exact Hwf0 ]. }
  assert (Hcollapse : msubst_uskl_syn (msubst_compose ζ1 w1) Rb
                      = msubst_uskl_syn ζ1 Rb).
  { apply msubst_uskl_syn_compose_id; [ exact Hidw1 | ].
    intros α Hα. pose proof (Hcov α Hα) as Hb.
    destruct Hb as [Hb | [Hb | [τ Hb]]].
    - right. apply Hnotflex. exact Hb.
    - left. eapply a_inc_flex_dom;
        [ exact Hincw1 | exact Hwf0 | left; exact Hb ].
    - left. eapply a_inc_flex_dom;
        [ exact Hincw1 | exact Hwf0 | right; exists τ; exact Hb ]. }
  assert (Hslack : Θ ⊢ R2' ≡ᵘ (msubst_uskl_syn ζ1 Rb)).
  { rewrite <- Hcollapse.
    eapply a_uskl_tyequiv_trans; [ exact Hrel2 | exact Hgen ]. }
  (* the codomain FILL moves κ → ζ1 along ≡ˢ *)
  assert (HscP0b : a_scope_pskl Θ0 P0b)
    by (eapply a_wf_pskl_to_a_scope_pskl;
        [ exact HwfP0b | auto | intros α Hα; clear - Hα; fsetdec ]).
  assert (Heqb0 : Θ ⊢ (msubst_pskl κ P0b) ≡ˢ (msubst_pskl ζ1 P0b)).
  { replace (msubst_pskl ζ1 P0b)
      with (msubst_pskl (msubst_compose ζ1 w1) P0b)
      by (eapply msubst_compose_id_pskl;
          [ exact Hwf0 | exact Hwf1 | exact Hidw1 | exact Hincw1
          | exact Hζ1 | exact HscP0b ]).
    eapply a_inc_equiv_msubst_pskl;
      [ exact HscP0b | exact Hie1 | exact Hwf0 | exact Hlcκ | exact Hlcc1 ]. }
  destruct (skl_tyequiv_refine_syn_f_transport Heqb0 Hwfth
              (fun x b Hb => Hb)) as [Hrst _].
  pose proof (Hrst _ _ _ Hrs2) as Hrs2'.
  (* ---- the codomain IH ---- *)
  destruct (IH NM M Θ1 P0b (⌊ Rb ⌋ˢ) Rb R2' _ Θ ζ1 Q2
              Hwf1 Hwfth HwfP0b1 HwfPb1 HmodSKb HmodTYb eq_refl Hζ1
              Hslack Hsub2 Hrs2')
    as [Q2' [Θ2 [Hrun2 Hopt2]]].
  (* ---- assemble the run ---- *)
  exists (pskl_arrow Q1' Q2'), Θ2. split.
  { eapply a_sub__arrow; [ exact Hrun1 | exact Hrun2 ]. }
  (* ---- the optimality package ---- *)
  intros κf Hidf Hincf.
  destruct (a_sub_sound_thm Hrun2 Hwf1 HwfP0b1 HwfPb1 HmodSKb HmodTYb)
    as [[[w2 [Hidw2 Hincw2]] Hdefs2] [Hwf2 _]].
  destruct (Hopt2 w2 Hidw2 Hincw2) as [ζ2 [Hζ2 [Hie2 Hprec2]]].
  assert (Heqw : w1 = κf) by (eapply is_id_inc_unique; eauto).
  subst κf.
  exists ζ2. split; [ exact Hζ2 | ]. split.
  { eapply a_inc_equiv_glue with
      (Θmid := Θ1) (Θfin := Θ2) (κ1b := w2) (ζ1 := ζ1);
      [ exact Hwf0 | exact Hwf1 | exact Hwf2 | exact Hwfth
      | exact Hidw1 | exact Hidw2
      | intros α Hα;
        pose proof (a_inc_dom_flex Hincw1 Hα) as Hfα;
        eapply a_inc_flex_dom; [ exact Hincw2 | exact Hwf1 | ];
        eapply (proj2 (proj2 a_assign_unify_consis_flex_preserve));
          [ exact Hrun1 | exact Hfα ]
      | exact Hincw1 | exact Hincw2 | exact Hζ1 | exact Hζ2
      | exact Hie1 | exact Hie2 ]. }
  (* ---- the precision, componentwise; the domain moves ζ1 → ζ2 ---- *)
  assert (HscQ1' : a_scope_pskl Θ1 Q1').
  { destruct Hsol1 as [Qt1 [HeqQt1 [Hjoin1s _]]].
    rewrite <- HeqQt1.
    eapply ad_pat_consis_target_wf; exact Hjoin1s. }
  assert (Hlcζ2 : msubst_lc ζ2) by (eapply a_inc_msubst_lc; exact Hζ2).
  assert (Hlcc2 : msubst_lc (msubst_compose ζ2 w2))
    by (apply msubst_lc_compose;
        [ exact Hlcζ2 | eapply is_id_msubst_values_lc; exact Hidw2 ]).
  assert (Heqζ : Θ ⊢ (msubst_pskl ζ1 Q1') ≡ˢ (msubst_pskl ζ2 Q1')).
  { replace (msubst_pskl ζ2 Q1')
      with (msubst_pskl (msubst_compose ζ2 w2) Q1')
      by (eapply msubst_compose_id_pskl;
          [ exact Hwf1 | exact Hwf2 | exact Hidw2 | exact Hincw2
          | exact Hζ2 | exact HscQ1' ]).
    eapply a_inc_equiv_msubst_pskl;
      [ exact HscQ1' | exact Hie2 | exact Hwf1 | exact Hlcζ1 | exact Hlcc2 ]. }
  unfold ad_precise in Hprec1, Hprec2 |- *.
  rewrite msubst_bskl_pskl_to_bskl_syn in Hprec1, Hprec2 |- *.
  rewrite bskl_to_pskl_pskl_to_bskl_syn in Hprec1, Hprec2 |- *.
  cbn [msubst_pskl bskl_to_pskl pskl_to_bskl_inh].
  apply ad_refine_syn__arrow.
  - (* domain *)
    apply (ad_refine_syn_f_forget (F := empty)).
    destruct (skl_tyequiv_refine_syn_f_transport Heqζ Hwfth
                (fun x b Hb => Hb)) as [Hpt _].
    apply Hpt. apply ad_refine_syn_f_empty_intro. exact Hprec1.
  - (* codomain *)
    exact Hprec2.
Qed.

Print Assumptions a_sub_complete_arrow.

(* ===================================================================== *)
(*  Sub-ForallR (paper :3196-3258) — THE ENABLERS                          *)
(*                                                                        *)
(*  The paper's route: the fill pins [P0 = ∀α.P0']; the IH runs the body   *)
(*  at [Θ0,α ⊑ Θ,α]; the run's output is [P0] itself ((TY,TC) returns its  *)
(*  input) at a context [Ξ,α,Θ1] whose junk [Ξ] the exists-fresh           *)
(*  [a_sub__forall_r] discards.  The decomposition and every Barendregt    *)
(*  payload come from the run's own identity increase ([a_inc_tvar_inv]   *)
(*  and the id-dom-monotonicity below) — no context surgery.               *)
(* ===================================================================== *)

(** At (TY, TC) the algorithm returns its INPUT skeleton: [Check] and
    [ForallR] do so by their shape, [ForallL] passes its premise through at
    the same [P0], and every other row lives at another mode. *)
Lemma a_sub_ty_tc_output : forall P0 Θ0 P P1 Θ1,
  a_sub a_sub_mode_ty mode_tc P0 Θ0 P P1 Θ1 ->
  P1 = P0.
Proof.
  intros P0 Θ0 P P1 Θ1 H.
  remember a_sub_mode_ty as NM eqn:HNM.
  remember mode_tc as M eqn:HM.
  induction H; try discriminate HNM; try discriminate HM; auto.
Qed.

(** An IDENTITY increase loses no names: a flexible's id-image is the
    variable itself, well formed in the target; rigid and term entries
    reappear on the rules. *)
Lemma is_id_inc_dom_mono : forall κ Θ0 Θ,
  is_id_msubst κ ->
  κ ∷ Θ0 ⊑ Θ ->
  dom Θ0 [<=] dom Θ.
Proof.
  intros κ Θ0 Θ Hid Hinc; revert Hid; induction Hinc; intros Hid; simpl.
  - clear; fsetdec.
  - (* flex : the id image is the variable itself, wf in the target *)
    inversion Hid; subst.
    match goal with Hie : is_id_entry _ |- _ =>
      unfold is_id_entry in Hie; cbn in Hie; subst end.
    match goal with Hwfv : a_wf_ptyp _ (ptyp_var_f _) |- _ =>
      inversion Hwfv; subst end.
    match goal with Hbt : a_binds_tvar _ _ |- _ =>
      destruct Hbt as [Hb | [Hb | [τ0 Hb]]]; apply binds_In in Hb end;
    match goal with IH0 : is_id_msubst _ -> _ |- _ =>
      specialize (IH0 ltac:(assumption)) end;
    match goal with IH0 : dom _ [<=] dom _ |- _ =>
      clear - IH0 Hb; fsetdec end.
  - (* flex_def : same, at the id entry *)
    inversion Hid; subst.
    match goal with Hie : is_id_entry _ |- _ =>
      unfold is_id_entry in Hie; cbn in Hie; subst end.
    match goal with Hwfv : a_wf_ptyp _ (ptyp_var_f _) |- _ =>
      inversion Hwfv; subst end.
    match goal with Hbt : a_binds_tvar _ _ |- _ =>
      destruct Hbt as [Hb | [Hb | [τ0 Hb]]]; apply binds_In in Hb end;
    match goal with IH0 : is_id_msubst _ -> _ |- _ =>
      specialize (IH0 ltac:(assumption)) end;
    match goal with IH0 : dom _ [<=] dom _ |- _ =>
      clear - IH0 Hb; fsetdec end.
  - (* var_typ *)
    specialize (IHHinc Hid). rewrite ! dom_app. simpl.
    clear - IHHinc; fsetdec.
  - (* var_skl *)
    specialize (IHHinc Hid). rewrite ! dom_app. simpl.
    clear - IHHinc; fsetdec.
  - (* tvar *)
    specialize (IHHinc Hid). rewrite ! dom_app. simpl.
    clear - IHHinc; fsetdec.
Qed.

(** Peeling an [a_inc] along a declaration-only SOURCE prefix: the prefix's
    entries are consumed one κ-row each, so κ splits as a list. *)
Lemma a_inc_suffix_prefix_inv : forall Ξ Θ0 κ Θ',
  a_suffix Ξ ->
  κ ∷ (Ξ ++ Θ0) ⊑ Θ' ->
  exists κa κb, κ = κa ++ κb /\ dom κa [=] dom Ξ /\ κb ∷ Θ0 ⊑ Θ'.
Proof.
  intros Ξ; induction Ξ as [ | [x b] Ξ IH ]; intros Θ0 κ Θ' Hsuf Hinc.
  - exists nil, κ. simpl.
    split; [ reflexivity | split; [ clear; fsetdec | exact Hinc ] ].
  - inversion Hsuf as [ | x0 b0 Ξ0 Hsuf' Hb ]; subst.
    inversion Hb; subst; simpl in Hinc; inversion Hinc; subst.
    + (* flex_mono *)
      match goal with Hrest : _ ∷ Ξ ++ Θ0 ⊑ _ |- _ =>
        destruct (IH _ _ _ Hsuf' Hrest) as [κa [κb [-> [Hdom Hincb]]]] end.
      match goal with |- context [ (x, ?τ) :: κa ++ κb ] => idtac end.
      eexists ((x, _) :: κa), κb.
      split; [ reflexivity | split; [ | exact Hincb ] ].
      simpl. clear - Hdom; fsetdec.
    + (* flex_mono_def *)
      match goal with Hrest : _ ∷ Ξ ++ Θ0 ⊑ _ |- _ =>
        destruct (IH _ _ _ Hsuf' Hrest) as [κa [κb [-> [Hdom Hincb]]]] end.
      eexists ((x, _) :: κa), κb.
      split; [ reflexivity | split; [ | exact Hincb ] ].
      simpl. clear - Hdom; fsetdec.
Qed.

Lemma msubst_lookup_app_notin : forall κa κb β,
  β `notin` dom κa ->
  msubst_lookup (κa ++ κb) β = msubst_lookup κb β.
Proof.
  induction κa as [ | [x τ] κa IH ]; intros κb β Hβ; simpl.
  - reflexivity.
  - simpl in Hβ.
    lazymatch goal with
    | |- context [ if ?c then _ else _ ] => destruct c as [-> | Hne]
    end.
    + exfalso. clear - Hβ. fsetdec.
    + apply IH. clear - Hβ. fsetdec.
Qed.

(** Composing an identity with an extended substitution ignores the
    extension when its domain is elsewhere. *)
Lemma msubst_compose_id_app_agree : forall κf κa ζ,
  is_id_msubst κf ->
  (forall x, x `in` dom κf -> x `notin` dom κa) ->
  msubst_compose (κa ++ ζ) κf = msubst_compose ζ κf.
Proof.
  induction κf as [ | [x τ] κf IH ]; intros κa ζ Hid Hdisj; simpl.
  - reflexivity.
  - inversion Hid; subst.
    match goal with Hie : is_id_entry _ |- _ =>
      unfold is_id_entry in Hie; cbn in Hie; subst end.
    f_equal.
    + f_equal. simpl.
      apply msubst_lookup_app_notin.
      apply Hdisj. simpl. clear; fsetdec.
    + apply IH; [ assumption | ].
      intros y Hy. apply Hdisj. simpl. clear - Hy; fsetdec.
Qed.

Print Assumptions a_sub_ty_tc_output.
Print Assumptions is_id_inc_dom_mono.
Print Assumptions a_inc_suffix_prefix_inv.

(* ===================================================================== *)
(*  Fill inversion at a ∀-inh counterpart — pinning [P0 = ∀.P0']           *)
(*                                                                        *)
(*  The paper: "The refinement premise is [Θ ⊢ inh{θP0} ⊳ inh{∀α.Q}], by  *)
(*  which we have P0 = ∀α.P0'" (:3208).  Mechanically: only [__all] and a  *)
(*  [__tophole_remove] (∀◇-headed source, excluded by TY mode) reach an    *)
(*  inh-∀ target — [__hole]'s fill is a SYN painting, and the [__flex_l]   *)
(*  chain bottoms out in monotype paintings.                               *)
(* ===================================================================== *)

Lemma ad_refine_syn_f_all_inh_r_shape : forall F Θ Δ Qs B,
  ad_refine_syn_f F Θ Δ Qs (bskl_all_inh B) ->
  (exists A, Qs = bskl_all_inh A) \/ (exists Q0, Qs = bskl_tophole Q0).
Proof.
  intros F Θ Δ Qs B H.
  remember (bskl_all_inh B) as T eqn:HT. revert B HT.
  induction H; intros B0 HT; try discriminate HT.
  - (* all *) left; eauto.
  - (* hole : a SYN painting is never an inh ∀ *)
    destruct P; simpl in HT; discriminate HT.
  - (* tophole_remove *) right; eauto.
  - (* flex_l : the unfolded definition is a monotype painting *)
    exfalso.
    destruct (IHad_refine_syn_f _ HT) as [[A HA] | [Q0 HQ0]];
      destruct τ; simpl in *; try discriminate HA; try discriminate HQ0.
Qed.

Lemma pskl_to_bskl_inh_all_inh_inv : forall X A,
  pskl_to_bskl_inh X = bskl_all_inh A ->
  exists X0, X = pskl_all_syn X0 /\ A = pskl_to_bskl_inh X0.
Proof.
  intros X A HA; destruct X; simpl in HA; inversion HA; subst.
  eexists; split; reflexivity.
Qed.

Lemma pskl_to_bskl_inh_tophole_inv : forall X Q,
  pskl_to_bskl_inh X = bskl_tophole Q ->
  exists X0, X = pskl_tophole X0.
Proof.
  intros X Q HQ; destruct X; simpl in HQ; inversion HQ; subst.
  eexists; reflexivity.
Qed.

(** A metasubstituted skeleton with a ∀ head has a ∀-headed source: a
    variable's image is a MONOTYPE painting. *)
Lemma msubst_pskl_all_syn_inv : forall Θ0 κ Θ P0 X,
  κ ∷ Θ0 ⊑ Θ ->
  msubst_pskl κ P0 = pskl_all_syn X ->
  exists P0', P0 = pskl_all_syn P0' /\ X = msubst_pskl κ P0'.
Proof.
  intros Θ0 κ Θ P0 X Hinc Heq.
  destruct P0; simpl in Heq; try discriminate Heq.
  - (* var : the image is a monotype painting *)
    exfalso.
    pose proof (a_inc_lookup_mono α Hinc) as Hm.
    destruct (msubst_lookup κ α); simpl in Heq;
      try discriminate Heq; inversion Hm.
  - inversion Heq; subst. eexists; split; reflexivity.
Qed.

Lemma msubst_pskl_tophole_inv : forall Θ0 κ Θ P0 X,
  κ ∷ Θ0 ⊑ Θ ->
  msubst_pskl κ P0 = pskl_tophole X ->
  exists P0', P0 = pskl_tophole P0'.
Proof.
  intros Θ0 κ Θ P0 X Hinc Heq.
  destruct P0; simpl in Heq; try discriminate Heq; eauto.
  exfalso.
  pose proof (a_inc_lookup_mono α Hinc) as Hm.
  destruct (msubst_lookup κ α); simpl in Heq;
    try discriminate Heq; inversion Hm.
Qed.

(** An embedded TYPE has no ∀◇ head, and its ∀ head embeds a ∀ type. *)
Lemma ptyp_to_pskl_not_tophole : forall A X,
  ptyp_to_pskl A <> pskl_tophole X.
Proof. intros A X; destruct A; simpl; discriminate. Qed.

Lemma ptyp_to_pskl_all_syn_inv : forall A X,
  ptyp_to_pskl A = pskl_all_syn X ->
  exists A0, A = ptyp_all A0 /\ X = ptyp_to_pskl A0.
Proof.
  intros A X HX; destruct A; simpl in HX; inversion HX; subst.
  eexists; split; reflexivity.
Qed.

Print Assumptions ad_refine_syn_f_all_inh_r_shape.
Print Assumptions msubst_pskl_all_syn_inv.

(* ===================================================================== *)
(*  Δ→Θ reassociation for the SYN fill — the mirror of                    *)
(*  [ad_refine_pskl_f_reassoc_mid] above, needed to hand the ∀-inh fill's  *)
(*  opened body (which [__all] places in Δ) to the IH (whose motive keeps  *)
(*  Δ = ∅ and binds the opener as a context rigid).                        *)
(* ===================================================================== *)

Lemma ad_refine_syn_f_reassoc_mid : forall F Θ Δ Q Q',
  ad_refine_syn_f F Θ Δ Q Q' ->
  forall Θ1 Θ2 α, Θ = Θ1 ++ Θ2 ->
  ad_refine_syn_f F (Θ1 ++ (α ~ abind_tvar) ++ Θ2) (remove α Δ) Q Q'.
Proof.
  intros F Θ Δ Q Q' H; induction H; intros Θ1 Θ2 α0 ->.
  - (* unit *) apply ad_refine_syn_f__unit.
  - (* var : a Δ-hit at α0 becomes the inserted Θ-entry *)
    apply ad_refine_syn_f__var.
    destruct H as [HΔ | Htv].
    + destruct (α == α0) as [-> | Hne].
      * right; left; unfold binds; apply in_or_app; right; simpl; left;
          reflexivity.
      * left; clear - HΔ Hne; fsetdec.
    + right; apply a_binds_tvar_insert_mid; exact Htv.
  - (* arrow *) apply ad_refine_syn_f__arrow; auto.
  - (* all *)
    apply ad_refine_syn_f__all with (L := L `union` singleton α0);
      intros α Hα.
    eapply ad_refine_syn_f_delta_mono;
      [ apply (H0 α ltac:(clear - Hα; fsetdec) Θ1 Θ2 α0 eq_refl)
      | clear; fsetdec ].
  - (* hole : the fill's wf moves by the wf transport *)
    apply ad_refine_syn_f__hole; [ exact H | ].
    eapply a_wf_pskl_delta_mono;
      [ apply (a_wf_pskl_reassoc_mid H0 Θ1 Θ2 α0 eq_refl) | clear; fsetdec ].
  - (* tophole_remove *) apply ad_refine_syn_f__tophole_remove; auto.
  - (* tophole_fill : ITS binder joins Θ above the insertion point *)
    apply ad_refine_syn_f__tophole_fill with (L := L `union` singleton α0);
      intros α Hα.
    apply (H0 α ltac:(clear - Hα; fsetdec) ((α ~ abind_tvar) ++ Θ1) Θ2 α0);
      simpl_env; reflexivity.
  - (* tophole_keep *) apply ad_refine_syn_f__tophole_keep; auto.
  - (* flex_l *)
    eapply ad_refine_syn_f__flex_l; [ | auto ].
    apply binds_insert_mid; exact H.
  - (* flex_r *)
    eapply ad_refine_syn_f__flex_r; [ | auto ].
    apply binds_insert_mid; exact H.
Qed.

Corollary ad_refine_syn_f_reassoc : forall F Θ Δ Q Q',
  ad_refine_syn_f F Θ Δ Q Q' ->
  forall α, ad_refine_syn_f F ((α ~ abind_tvar) ++ Θ) (remove α Δ) Q Q'.
Proof.
  intros F Θ Δ Q Q' H α.
  apply (ad_refine_syn_f_reassoc_mid H nil Θ α); simpl_env; reflexivity.
Qed.

Print Assumptions ad_refine_syn_f_reassoc.

(* ===================================================================== *)
(*  F-GROWTH for the SYN fill (mirror of [ad_refine_pskl_f_fgrow])         *)
(* ===================================================================== *)

Lemma ad_refine_syn_f_fgrow : forall F Θ Δ Q Q',
  ad_refine_syn_f F Θ Δ Q Q' ->
  forall α, α `notin` dom Θ ->
  ad_refine_syn_f (add α F) Θ Δ Q Q'.
Proof.
  intros F Θ Δ Q Q' H; induction H; intros α0 Hα0.
  - apply ad_refine_syn_f__unit.
  - apply ad_refine_syn_f__var; assumption.
  - apply ad_refine_syn_f__arrow; auto.
  - apply ad_refine_syn_f__all with (L := L); intros α Hα; auto.
  - apply ad_refine_syn_f__hole; [ | exact H0 ].
    apply inter_empty_pointwise; intros β Hβ.
    destruct (AtomSetProperties.In_dec β (ftvar_in_pskl P)) as [Hin | Hni].
    + assert (Hdom : β `in` dom Θ) by (eapply a_wf_pskl_ftv_dom; eassumption).
      assert (Hne : β <> α0) by (intros ->; clear - Hdom Hα0; fsetdec).
      clear - H Hin Hne Hβ; fsetdec.
    + clear - Hni Hβ; fsetdec.
  - apply ad_refine_syn_f__tophole_remove; auto.
  - apply ad_refine_syn_f__tophole_fill
      with (L := L `union` singleton α0 `union` dom Θ);
      intros α Hα.
    apply H0; [ clear - Hα; fsetdec | simpl; clear - Hα Hα0; fsetdec ].
  - apply ad_refine_syn_f__tophole_keep; auto.
  - eapply ad_refine_syn_f__flex_l; [ exact H | auto ].
  - eapply ad_refine_syn_f__flex_r; [ exact H | auto ].
Qed.

(* ===================================================================== *)
(*  Sub-ForallR, THE ROW (paper :3196-3258)                                *)
(*                                                                        *)
(*  The join's [__forall_r] family is a ROW HYPOTHESIS (the bundle owes    *)
(*  the inversion, as for Arrow).  The fill pins [P0 = ∀.P0'] — with       *)
(*  [skmod[TY]] making [P0'] an embedded TYPE, which kills the ∀◇ branch   *)
(*  and keeps every ghost out of the precision (the rebind at the end is   *)
(*  the GHOST-FREE strip+rename).  The IH runs ONCE at a fresh binder —    *)
(*  exactly the exists-fresh [a_sub__forall_r]'s premise; the junk suffix, *)
(*  the Barendregt payloads and the optimality strips all come from the    *)
(*  run's own identity increase.                                           *)
(* ===================================================================== *)

Lemma a_sub_complete_forall_r : forall n Θ0 P0 P R R' Ψ Θ κ B L,
  (forall NM' M' Θ0' P0' P' R'' T'' Ψ' Θ' κ' Q',
     sub_complete_concl n NM' M' Θ0' P0' P' R'' T'' Ψ' Θ' κ' Q') ->
  (forall α, α `notin` L ->
     ad_pat_sub_gv n a_sub_mode_ty mode_tc Ψ ((α ~ abind_tvar) ++ Θ) R'
       (open_bskl_wrt_bskl B (bskl_var_f α))) ->
  sub_complete_concl (S n) a_sub_mode_ty mode_tc Θ0 P0 P R R' Ψ Θ κ
    (bskl_all_inh B).
Proof.
  intros n Θ0 P0 P R R' Ψ Θ κ B L IH Hjoin.
  unfold sub_complete_concl.
  intros Hwf0 Hwfth HwfP0 HwfP HmodSK HmodTY HeqP Hinc Hrel Hsub Hrs.
  pose proof (HmodTY eq_refl) as Hmty.
  assert (Hlcκ : msubst_lc κ) by (eapply a_inc_msubst_lc; exact Hinc).
  (* ---- 1. the fill pins [P0 = ∀.(ptyp_to_pskl A0)] ---- *)
  destruct (ad_refine_syn_f_all_inh_r_shape Hrs) as [[As HAs] | [Q0 HQ0]].
  2: { exfalso.
       destruct (@pskl_to_bskl_inh_tophole_inv _ _ HQ0) as [X0 HX0].
       destruct (@msubst_pskl_tophole_inv _ _ _ _ _ Hinc HX0) as [P0t HP0t].
       subst P0. inversion Hmty.
       match goal with
       | He : ptyp_to_pskl _ = pskl_tophole _ |- _ =>
           eapply ptyp_to_pskl_not_tophole; exact He
       | He : pskl_tophole _ = ptyp_to_pskl _ |- _ =>
           eapply ptyp_to_pskl_not_tophole; symmetry; exact He
       end. }
  destruct (@pskl_to_bskl_inh_all_inh_inv _ _ HAs) as [X [HX HAseq]].
  destruct (@msubst_pskl_all_syn_inv _ _ _ _ _ Hinc HX) as [P0' [HP0eq HXeq]].
  subst P0 X As.
  inversion Hmty; subst.
  match goal with
  | He : ptyp_to_pskl _ = pskl_all_syn _ |- _ => rename He into HA
  | He : pskl_all_syn _ = ptyp_to_pskl _ |- _ =>
      symmetry in He; rename He into HA
  end.
  destruct (@ptyp_to_pskl_all_syn_inv _ _ HA) as [A0 [HAeq HP0'eq]].
  subst.
  cbn [msubst_pskl pskl_to_bskl_inh] in Hrs.
  (* ---- 2. the ∀-inh fill's cofinite body family ---- *)
  inversion Hrs; subst.
  match goal with
  | Hn : forall α, α `notin` ?Lx -> ad_refine_syn_f _ _ _ _ _ |- _ =>
      rename Hn into Hfill
  end.
  match type of Hfill with
  | forall α, α `notin` ?Lx -> _ =>
      destruct (atom_fresh
        (L `union` Lx `union` dom Θ0 `union` dom Θ `union` dom κ
           `union` ftvar_in_pskl (ptyp_to_pskl A0) `union` ftvar_in_bskl B
           `union` ftvar_in_pskl ⌊ R ⌋ˢ)) as [α Fr]
  end.
  assert (HαΘ0 : α `notin` dom Θ0) by (clear - Fr; fsetdec).
  assert (HαΘ : α `notin` dom Θ) by (clear - Fr; fsetdec).
  assert (Hακ : α `notin` dom κ) by (clear - Fr; fsetdec).
  (* ---- 3. the IH's premises at the opened problem ---- *)
  assert (Hwf0' : a_wf_aenv ((α ~ abind_tvar) ++ Θ0))
    by (apply a_wf_aenv__tvar; [ exact HαΘ0 | exact Hwf0 ]).
  assert (Hwfth' : a_wf_aenv ((α ~ abind_tvar) ++ Θ))
    by (apply a_wf_aenv__tvar; [ exact HαΘ | exact Hwfth ]).
  assert (HwfP0α : ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ
                     (open_pskl_wrt_pskl (ptyp_to_pskl A0) (pskl_var_f α))).
  { eapply a_wf_pskl_all_syn_open_tvar;
      [ exact HwfP0 | clear - Fr; fsetdec ]. }
  assert (HwfPα : ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ ⌊ R ⌋ˢ)
    by (apply a_wf_pskl_weaken_tvar; exact HwfP).
  assert (HmodSKα : a_sub_mode_ty = a_sub_mode_sk ->
            a_sk_mode_compat mode_tc
              (open_pskl_wrt_pskl (ptyp_to_pskl A0) (pskl_var_f α)))
    by (intro Hc; discriminate Hc).
  assert (HmodTYα : a_sub_mode_ty = a_sub_mode_ty ->
            a_ty_mode_compat mode_tc
              (open_pskl_wrt_pskl (ptyp_to_pskl A0) (pskl_var_f α))).
  { intros _. rewrite <- ptyp_to_pskl_open. apply a_ty_mode_compat__tc. }
  assert (Hinc' : κ ∷ ((α ~ abind_tvar) ++ Θ0) ⊑ ((α ~ abind_tvar) ++ Θ)).
  { apply (a_inc__tvar (Ξ:=nil) α Hinc).
    apply a_decls_suffix. apply a_decls__nil. }
  assert (Hrel' : ((α ~ abind_tvar) ++ Θ) ⊢ R' ≡ᵘ (msubst_uskl_syn κ R))
    by (apply a_uskl_tyequiv_weaken_cons; exact Hrel).
  pose proof (Hjoin α ltac:(clear - Fr; fsetdec)) as Hjoinα.
  assert (Hrsα : ad_refine_syn_f empty ((α ~ abind_tvar) ++ Θ) empty
            (pskl_to_bskl_inh
               (msubst_pskl κ
                  (open_pskl_wrt_pskl (ptyp_to_pskl A0) (pskl_var_f α))))
            (open_bskl_wrt_bskl B (bskl_var_f α))).
  { pose proof (Hfill α ltac:(clear - Fr; fsetdec)) as Hf0.
    rewrite <- pskl_to_bskl_inh_open in Hf0.
    rewrite <- (msubst_pskl_open_lc (ptyp_to_pskl A0) Hlcκ Hακ) in Hf0.
    eapply ad_refine_syn_f_delta_mono;
      [ apply (ad_refine_syn_f_reassoc Hf0 α) | clear; fsetdec ]. }
  (* ---- 4. the IH, once ---- *)
  destruct (IH a_sub_mode_ty mode_tc ((α ~ abind_tvar) ++ Θ0)
              (open_pskl_wrt_pskl (ptyp_to_pskl A0) (pskl_var_f α))
              (⌊ R ⌋ˢ) R R' Ψ ((α ~ abind_tvar) ++ Θ) κ
              (open_bskl_wrt_bskl B (bskl_var_f α))
              Hwf0' Hwfth' HwfP0α HwfPα HmodSKα HmodTYα eq_refl Hinc'
              Hrel' Hjoinα Hrsα)
    as [P1 [Θo [Hrun Hopt]]].
  pose proof (a_sub_ty_tc_output Hrun) as ->.
  (* ---- 5. the run's id increase shapes the output ---- *)
  destruct (a_sub_sound_thm Hrun Hwf0' HwfP0α HwfPα HmodSKα HmodTYα)
    as [[[w1 [Hidw1 Hincw1]] Hdefs1] [HwfΘo _]].
  destruct (a_inc_tvar_inv Hincw1) as [Ξj [Θ1 [-> [Hsufj Hincw1']]]].
  assert (HuqΘo : uniq (Ξj ++ (α ~ abind_tvar) ++ Θ1))
    by (apply a_wf_aenv_uniq; exact HwfΘo).
  assert (HαΞj : α `notin` dom Ξj)
    by (clear - HuqΘo; simpl_env in HuqΘo; destruct_uniq;
        unfold disjoint in *; simpl_env in *; fsetdec).
  assert (HαΘ1 : α `notin` dom Θ1)
    by (clear - HuqΘo; simpl_env in HuqΘo; destruct_uniq;
        unfold disjoint in *; simpl_env in *; fsetdec).
  assert (Hdom01 : dom Θ0 [<=] dom Θ1)
    by (eapply is_id_inc_dom_mono; [ exact Hidw1 | exact Hincw1' ]).
  assert (HdisjΞ0 : forall γ, γ `in` dom Ξj -> γ `notin` dom Θ0).
  { intros γ Hγ Hc.
    assert (HγΘ1 : γ `in` dom Θ1) by (clear - Hdom01 Hc; fsetdec).
    clear - HuqΘo Hγ HγΘ1. simpl_env in HuqΘo. destruct_uniq.
    unfold disjoint in *. simpl_env in *. fsetdec. }
  assert (HuqJ : uniq (Ξj ++ Θ0)).
  { pose proof (a_wf_aenv_uniq Hwf0) as Huq0.
    pose proof HuqΘo as Huq'. simpl_env in Huq'. destruct_uniq.
    assert (Hdisj0 : disjoint Ξj Θ0)
      by (unfold disjoint in *; simpl_env in *; fsetdec).
    solve_uniq. }
  (* ---- 6. the run ---- *)
  exists (pskl_all_syn (ptyp_to_pskl A0)), Θ1.
  split.
  { eapply a_sub__forall_r with (α := α) (Ξ := Ξj);
      [ exact Hsufj | exact HuqJ | | exact Hrun ].
    rewrite dom_app.
    clear - Fr HαΞj HαΘ1. simpl in Fr. fsetdec. }
  (* ---- 7. optimality ---- *)
  intros κf Hidf Hincf.
  assert (Hincf' : κf ∷ ((α ~ abind_tvar) ++ Θ0) ⊑
                     (Ξj ++ (α ~ abind_tvar) ++ Θ1)).
  { apply (a_inc__tvar (Ξ:=Ξj) α Hincf). exact Hsufj. }
  destruct (Hopt κf Hidf Hincf') as [ζ' [Hζ' [Hie' Hprec']]].
  (* peel the junk rows off ζ' *)
  destruct (@a_inc_suffix_prefix_inv _ _ _ _ Hsufj Hζ')
    as [κa [ζ [-> [Hdomκa Hζmid]]]].
  destruct (a_inc_tvar_inv Hζmid) as [Ξs [Θ2 [HeqT2 [HsufΞs Hζfin]]]].
  destruct Ξs as [ | [y by_] Ξs' ]; simpl in HeqT2;
    [ | exfalso; inversion HeqT2; subst;
        inversion HsufΞs as [ | ? ? ? ? Hsb ]; subst;
        inversion Hsb ].
  inversion HeqT2; subst Θ2.
  exists ζ. split; [ exact Hζfin | ]. split.
  { (* the metasubstitution equivalence, at the stripped composite *)
    destruct (a_inc_equiv_tvar_inv Hie') as [Ξs2 [Θ2' [HeqT3 [Hsuf2 Hie2]]]].
    destruct Ξs2 as [ | [y2 by2] Ξs2' ]; simpl in HeqT3;
      [ | exfalso; inversion HeqT3; subst;
          inversion Hsuf2 as [ | ? ? ? ? Hsb2 ]; subst;
          inversion Hsb2 ].
    inversion HeqT3; subst Θ2'.
    assert (Hcomp : msubst_compose (κa ++ ζ) κf = msubst_compose ζ κf).
    { apply msubst_compose_id_app_agree; [ exact Hidf | ].
      intros x Hx Hc.
      assert (HxΘ0 : x `in` dom Θ0).
      { destruct (a_inc_dom_flex Hincf Hx) as [Hb | [τ Hb]];
          apply binds_In in Hb; exact Hb. }
      eapply HdisjΞ0; [ | exact HxΘ0 ].
      clear - Hdomκa Hc; fsetdec. }
    rewrite Hcomp in Hie2. exact Hie2. }
  { (* the precision: rebind the quantifier from the α-instance *)
    assert (Hαζ : α `notin` dom ζ).
    { intro Hin.
      destruct (a_inc_dom_flex Hζfin Hin) as [Hb | [τ Hb]];
        apply binds_In in Hb; clear - Hb HαΘ1; fsetdec. }
    assert (Hlcζ : msubst_lc ζ) by (eapply a_inc_msubst_lc; exact Hζfin).
    assert (Himgζ : forall α1 τ, In (α1, τ) ζ -> α `notin` ftvar_in_ptyp τ).
    { intros α1 τ Hin.
      pose proof (a_inc_images_ftv_dom Hζfin _ _ Hin) as Hsc.
      clear - Hsc HαΘ. fsetdec. }
    (* move the α-instance's subject from (κa ++ ζ) to ζ *)
    unfold ad_precise in Hprec' |- *.
    rewrite msubst_bskl_pskl_to_bskl_syn in Hprec' |- *.
    rewrite bskl_to_pskl_pskl_to_bskl_syn in Hprec' |- *.
    assert (Hagree : msubst_pskl (κa ++ ζ)
                       (open_pskl_wrt_pskl (ptyp_to_pskl A0) (pskl_var_f α))
                   = msubst_pskl ζ
                       (open_pskl_wrt_pskl (ptyp_to_pskl A0) (pskl_var_f α))).
    { apply msubst_pskl_agree. intros β Hβ.
      apply msubst_lookup_app_notin.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                    (ptyp_to_pskl A0) (pskl_var_f α)) as Hup.
      simpl in Hup.
      destruct (β == α) as [-> | Hne].
      - clear - Hdomκa HαΞj. fsetdec.
      - assert (HβA0 : β `in` ftvar_in_pskl (ptyp_to_pskl A0))
          by (clear - Hβ Hup Hne; fsetdec).
        assert (HβΘ0 : β `in` dom Θ0).
        { destruct (a_wf_pskl_ftv_binds_tvar HwfP0
                      (α := β) ltac:(simpl; clear - HβA0; fsetdec))
            as [Hin | Hbt];
            [ exfalso; clear - Hin; fsetdec | ].
          destruct Hbt as [Hb | [Hb | [τ Hb]]]; eapply binds_In; exact Hb. }
        intro Hc. eapply HdisjΞ0; [ | exact HβΘ0 ].
        clear - Hdomκa Hc; fsetdec. }
    rewrite Hagree in Hprec'.
    rewrite (msubst_pskl_open_lc (ptyp_to_pskl A0) Hlcζ Hαζ) in Hprec'.
    rewrite bskl_to_pskl_open in Hprec'.
    cbn [msubst_pskl bskl_to_pskl pskl_to_bskl_inh].
    apply ad_refine_syn__all with
      (L := singleton α `union` dom Θ `union` dom Θ1
            `union` ftvar_in_pskl (ptyp_to_pskl A0) `union` ftvar_in_bskl B
            `union` dom κa `union` dom ζ).
    intros β Hβ.
    (* the α-instance, hygienically F-marked and ghost-free *)
    pose proof (ad_refine_syn_f_empty_intro Hprec') as Hp0.
    assert (Hgfsrc : bskl_ghost_free
              (pskl_to_bskl_inh
                 (open_pskl_wrt_pskl (msubst_pskl ζ (ptyp_to_pskl A0))
                    (pskl_var_f α)))).
    { apply pskl_to_bskl_inh_ghost_free.
      rewrite (msubst_pskl_ptyp_to_pskl ζ A0).
      rewrite <- ptyp_to_pskl_open.
      apply ptyp_to_pskl_ghost_free. }
    pose proof (@ad_refine_syn_f_ghost_free_strip_rename _ _ _ _ _ Hp0
                  nil α Θ β
                  ltac:(simpl_env; reflexivity)
                  Hgfsrc Hwfth'
                  ltac:(apply a_wf_aenv_uniq; exact Hwfth')
                  ltac:(intros γ Hγ; simpl_env; fsetdec)) as Hp1.
    (* push the rename inside and collapse it *)
    rewrite pskl_to_bskl_inh_subst_var in Hp1.
    rewrite pskl_to_bskl_inh_subst_var in Hp1.
    rewrite <- (msubst_pskl_open_lc (ptyp_to_pskl A0) Hlcζ Hαζ) in Hp1.
    assert (Hβζ : β `notin` dom ζ) by (clear - Hβ; fsetdec).
    rewrite (msubst_pskl_subst_var ζ
               (open_pskl_wrt_pskl (ptyp_to_pskl A0) (pskl_var_f α))
               Hαζ Hβζ Himgζ) in Hp1.
    rewrite <- (subst_pskl_in_pskl_intro α (ptyp_to_pskl A0)
                  (pskl_var_f β) ltac:(clear - Fr; fsetdec)) in Hp1.
    rewrite <- (subst_pskl_in_pskl_intro α (bskl_to_pskl B)
                  (pskl_var_f β)) in Hp1.
    2: { pose proof (ftvar_in_pskl_bskl_to_pskl B) as Hfb.
         clear - Fr Hfb. simpl in Fr. fsetdec. }
    rewrite (msubst_pskl_open_lc (ptyp_to_pskl A0) Hlcζ Hβζ) in Hp1.
    rewrite pskl_to_bskl_inh_open in Hp1.
    rewrite pskl_to_bskl_inh_open in Hp1.
    (* both sides are now in the goal's opened shape *)
    eapply ad_refine_syn_f_forget.
    eapply ad_refine_syn_f_delta_mono; [ exact Hp1 | clear; fsetdec ]. }
Qed.

Print Assumptions a_sub_complete_forall_r.
