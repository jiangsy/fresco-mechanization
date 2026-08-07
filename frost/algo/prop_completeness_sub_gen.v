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
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_extra.
Require Import src.frost.coercions.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.
Require Import src.frost.prop_basic.              (* bskl_to_pskl_pskl_to_bskl_{syn,inh} *)
Require Import src.frost.algo.def_meta.
Require Import src.frost.decorated_algo.def_decl_algo.
Require Import src.frost.decorated_algo.def_decorated.
Require Import src.frost.decorated_algo.def_decl_algo_sub.
Require Import src.frost.decorated_algo.def_decl_algo_sub_hyg.
Require Import src.frost.algo.prop_inc.           (* a_binds_tvar_weaken_mid *)
Require Import src.frost.algo.prop_refine.        (* lc_pskl_to_bskl_inh, a_wf_pskl_delta_mono *)
Require Import src.frost.algo.prop_completeness_consis. (* ad_precise_f *)
Require Import src.frost.algo.prop_consis_precise. (* pskl_no_forall *)
Require Import src.frost.algo.prop_metasubst.     (* opt_axiom_factor *)
Require Import src.frost.algo.prop_precise.       (* ad_precise, ⊢ₚᵣᵃ *)
Require Import src.frost.algo.prop_flex.          (* a_decls *)
Require Import src.frost.algo.prop_soundness_consis.  (* ad_refine_{syn,pskl}_f *)
Require Import src.frost.algo.prop_compose.       (* a_inc_{dom_flex,lookup_wf,lookup_mono}, msubst_pskl_open *)
Require Import src.frost.decorated_algo.prop_decorate_sub.  (* lc_uskl_of_pskl *)
Require Import src.frost.algo.prop_normal.        (* a_inc_equiv_lookup (the a_binds_tvar form) *)
Require Import src.frost.algo.prop_mono_bridge.   (* ptyp_to_bskl_inh_syn_eq *)
Require Import src.frost.algo.prop_precise_recover. (* tyequiv_mono_refine_syn *)
Require Import src.frost.algo.prop_pat_sub.       (* uskl_to_pskl_ptyp_to_uskl_syn *)
Require Import src.frost.algo.prop_sub_msubst_equiv. (* ≡ᵘ + erasure + generation *)
Require Import src.frost.algo.prop_stability.     (* a_wf_pskl_isub *)
Require Import src.frost.algo.prop_inc_strengthen. (* a_assign_unify_consis_flex_preserve *)
Require Import src.frost.decorated_algo.prop_decorate_key.  (* a_sub_sound_thm *)
Require Import src.frost.decorated_algo.prop_decorate.       (* pskl_to_uskl kit *)
Require Import src.frost.algo.prop_soundness_sub.      (* a_wf_pskl_subst_tvar *)
Require Import src.frost.algo.prop_consis_precise.   (* uskl_precise kit *)
Require Import src.frost.algo.prop_completeness_sub_precise.     (* P5 + the _gv transports *)
Require Import src.frost.algo.completeness_look.prop_eq_cstr.
Require Import src.frost.algo.completeness_look.prop_sub_cstr.
Require Import src.frost.algo.completeness_look.prop_extract.
Require Import src.frost.algo.prop_swap.                  (* THE SWAP KIT — P7a's renaming primitive *)

Set Implicit Arguments.

(** ⚙️ P6-L's guess-scope premise, read off the guess's own
    well-formedness.  A named lemma rather than an inline [rewrite … in …]:
    at one of the two call sites the [⌊·⌋ˢ] is already reduced and the
    rewrite has nothing to fire on. *)
Lemma uskl_wf_ftv_dom : forall Θ Δ ψ,
  Θ ⨟ Δ ⊢ₚₛᵃ ⌊ ψ ⌋ˢ -> ftvar_in_uskl ψ [<=] Δ `union` dom Θ.
Proof.
  intros Θ Δ ψ H.
  pose proof (a_wf_pskl_ftv_dom H) as Hd.
  rewrite ftvar_in_pskl_uskl_to_pskl in Hd. exact Hd.
Qed.


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
  (* the solution's counterpart is well formed — the paper's EXTERNAL wf
     side condition (WF-SIDE-CONDITIONS.md), first consumed by
     Sub-ForallL's precision-substitution step (P5's [Hwfq]); refinement
     does not transport wf, so it cannot be derived from the fill *)
  Θ ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q) ->
  (* the JOIN-side subject is ghost-free at the TY sort — an EXTERNAL side
     condition of the same family as the wf ones (WF-SIDE-CONDITIONS.md,
     2026-08-03).  P5's precision-substitution transport
     ([ad_pat_sub_precise_upre_gv]) demands it at the ForallL rows and the
     join cannot supply it ([__arrow]'s domain leaf and [__infer] take an
     arbitrary subject).  Guarded by [NM = TY]: every ghost-heading join
     rule is SK-only, so the SK-side suppliers are all vacuous — which is
     what makes the premise cheap to thread. *)
  (NM = a_sub_mode_ty -> uskl_ghost_free R') ->
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
  (* …and every one of them is a P0-DEPENDENCY.  The consistency walk's
     motive carries the same invariant ([assign_complete_at],
     prop_consis_complete.v:2249) and this one used to lack it.  It is
     supplied at [a_sub__flex_mono] (Ξ = ·) and preserved by every walk row —
     [Flex-Depend] adds exactly a [β ∈ ftv P0], the others leave Ξ alone, and
     [Flex-Assign]'s [P0[τ/β̂]] keeps every OTHER variable of [P0].  It is
     load-bearing at [Flex-SkipRigid] and nowhere else: Ξ sits ABOVE the
     skipped rigid β in the source, so without it a solution may send a
     Ξ-flexible to β — and the rule re-attaches β at the TOP of the output,
     where Θ1's flexibles are scoped BELOW it, so no ζ could reproduce it. *)
  dom Ξ [<=] ftvar_in_pskl P0 ->
  a_wf_aenv (Ξ ++ Θ0) -> a_wf_aenv Θ ->
  (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P0 ->
  (* …and the subject lives in the SHRINKING half, not in the walked suffix.
     That is the walk's own invariant — [a_sub__flex_mono] enters at [Ξ = ·],
     [Flex-Depend] moves only a [β ≠ α] into Ξ and [Flex-Skip] /
     [Flex-SkipRigid] drop only a [β ≠ α] — and it is what the consistency
     walk's motive states too ([assign_complete_at],
     prop_consis_complete.v:2249).  It is load-bearing at [Flex-SkipRigid]:
     it makes [α ∉ dom Ξ], hence [α ∉ dom κa], hence the subject's image
     readable off the TRUNCATED increase [κb ∷ Θ0 ⊑ Θ'].  Read off the
     Ξ-block instead it would be CIRCULAR — Ξ's images are confined only by
     the join's ⇓-confinement, which needs the subject's scope first. *)
  a_flex_tvar Θ0 α ->
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
  Θ ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q) ->    (* external wf, as in the main motive *)
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

(** A subject ≡ᵘ-equivalent to a monotype PAINTING is itself one, hence
    ghost-free — the supplier for the motive's TY ghost-freeness premise at
    every flex-half re-entry into the main judgment (Flex-Assign keeps the
    walk's subject, Flex-Solve deposits a painted arrow). *)
Lemma tyequiv_mono_paint_ghost_free : forall Θ R' τ,
  Θ ⊢ R' ≡ᵘ (ptyp_to_uskl_syn τ) ->
  mono_ptyp τ -> a_wf_ptyp Θ τ ->
  uskl_ghost_free R'.
Proof.
  intros Θ R' τ Hrel Hm Hwf.
  destruct (a_uskl_tyequiv_mono_r_inv Hrel eq_refl Hm Hwf)
    as [τ' [-> [Hm' _]]].
  apply mono_ptyp_to_uskl_syn_ghost_free. exact Hm'.
Qed.

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
  intros Hwf0 Hwfth HwfP0 HwfP HmodSK HmodTY HeqP Hinc Hrel Hsub Hrs HwfQ Hgf.
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
  intros Hwf0 Hwfth HwfP0 HwfP HmodSK HmodTY HeqP Hinc Hrel Hsub Hrs HwfQ Hgf.
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

Lemma a_consis_hole_p0_output : forall Δ1 Δ2 Θ0 P0 P P' Θ1,
  a_consis Δ1 Δ2 Θ0 P0 P P' Θ1 ->
  P0 = pskl_hole ->
  P' = P.
Proof.
  intros Δ1 Δ2 Θ0 P0 P P' Θ1 H; induction H; intros Heq;
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
  destruct (a_consis_complete_thm Hwf0 (a_wf_pskl__hole Θ0 empty)
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
  intros Hwf0 Hwfth HwfP0 HwfP HmodSK HmodTY HeqP Hinc Hrel Hsub Hrs HwfQ Hgf.
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
  intros Hwf0 Hwfth HwfP0 HwfP HmodSK HmodTY HeqP Hinc Hrel Hsub Hrs HwfQ Hgf.
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
  intros Hwf0 Hwfth HwfP0 HwfP HmodSK HmodTY HeqP Hinc Hrel Hsub Hrs HwfQ Hgf.
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
  (* …and it is a TYPE: the motive's TY-sort ghost-freeness of the unresolved
     subject transports across [≡ᵘ] (which relates a ghost only to the SAME
     ghost, and its one non-structural row to a monotype painting), then
     reflects back through the metasubstitution (whose images are monotypes)
     and through the erasure.  This is [a_sub__check]'s SUBJECT premise. *)
  assert (HgfP : pskl_ghost_free P).
  { rewrite <- HeqP.
    eapply msubst_pskl_ghost_free_inv with (κ := κ).
    rewrite <- uskl_to_pskl_msubst_uskl_syn.
    apply uskl_ghost_free_to_pskl.
    eapply a_uskl_tyequiv_ghost_free; [ exact Hrel | exact (Hgf eq_refl) ]. }
  (* the DECORATED premise undecorates, then the slack moves it to κP *)
  assert (Hc : empty ⨟ Θ ⊢ₛᵃ (pskl_to_uskl (msubst_pskl κ P))
                            ∼ (pskl_to_bskl_inh B)).
  { pose proof (ad_pat_consis_strip_tags Hrow) as H0.
    destruct (skl_tyequiv_consis_transport Herase Hwfth
                (fun x b Hb => Hb)) as [Hct _].
    exact (Hct _ _ H0). }
  destruct (a_consis_complete_thm Hwf0 HwfP0 HwfP Hinc Hwfth Hc Hrs Hrp)
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
    [ apply a_sub__check;
        [ exact HgfP
        | apply a_ty_mode_compat_tc_ghost_free; exact (HmodTY eq_refl)
        | exact HgP | exact HgP0 | exists P1; exact Hrun ] | ].
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
  intros Hwf0 Hwfth HwfP0 HwfP HmodSK HmodTY HeqP Hinc Hrel Hsub Hrs HwfQ Hgf.
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
  destruct (a_consis_complete_thm Hwf0 HwfP0a HwfPa Hinc Hwfth Hc1
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
  (* the codomain's external target wf, off the arrow's *)
  assert (HwfQ2 : Θ ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q2))
    by (cbn in HwfQ; inversion HwfQ; assumption).
  (* the codomain's ghost-freeness, off the arrow's *)
  assert (Hgf2 : NM = a_sub_mode_ty -> uskl_ghost_free R2')
    by (intro HNM; pose proof (Hgf HNM) as Hga; inversion Hga; assumption).
  (* ---- the codomain IH ---- *)
  destruct (IH NM M Θ1 P0b (⌊ Rb ⌋ˢ) Rb R2' _ Θ ζ1 Q2
              Hwf1 Hwfth HwfP0b1 HwfPb1 HmodSKb HmodTYb eq_refl Hζ1
              Hslack Hsub2 Hrs2' HwfQ2 Hgf2)
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
  intros Hwf0 Hwfth HwfP0 HwfP HmodSK HmodTY HeqP Hinc Hrel Hsub Hrs HwfQ Hgf.
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
  cbn in HwfQ.
  destruct (a_wf_pskl_all_inv HwfQ) as [Lw HwQbody].
  match type of Hfill with
  | forall α, α `notin` ?Lx -> _ =>
      destruct (atom_fresh
        (L `union` Lx `union` Lw `union` dom Θ0 `union` dom Θ `union` dom κ
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
  assert (HwfQα : ((α ~ abind_tvar) ++ Θ) ⨟ empty ⊢ₚₛᵃ
                    (bskl_to_pskl (open_bskl_wrt_bskl B (bskl_var_f α)))).
  { rewrite bskl_to_pskl_open.
    eapply a_wf_pskl_delta_to_tvar;
      [ apply HwQbody; clear - Fr; fsetdec | clear; fsetdec ]. }
  (* ---- 4. the IH, once ---- *)
  destruct (IH a_sub_mode_ty mode_tc ((α ~ abind_tvar) ++ Θ0)
              (open_pskl_wrt_pskl (ptyp_to_pskl A0) (pskl_var_f α))
              (⌊ R ⌋ˢ) R R' Ψ ((α ~ abind_tvar) ++ Θ) κ
              (open_bskl_wrt_bskl B (bskl_var_f α))
              Hwf0' Hwfth' HwfP0α HwfPα HmodSKα HmodTYα eq_refl Hinc'
              Hrel' Hjoinα Hrsα HwfQα Hgf)
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
      [ exact (ptyp_to_pskl_ghost_free (ptyp_all A0))
      | exact Hsufj | exact HuqJ | | exact Hrun ].
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

(* ===================================================================== *)
(*  Sub-ForallL leaf plumbing (P7b's last row)                            *)
(* ===================================================================== *)

(** The plain-skeleton embedding commutes with the metasubstitution. *)
Lemma msubst_uskl_syn_pskl_to_uskl : forall κ P,
  msubst_uskl_syn κ (pskl_to_uskl P) = pskl_to_uskl (msubst_pskl κ P).
Proof.
  intros κ P; induction P; cbn; try solve [ f_equal; auto ].
  symmetry; apply pskl_to_uskl_ptyp.
Qed.

(** Embeddings of plain skeletons are tag-free. *)
Lemma ftag_in_uskl_pskl_to_uskl : forall P,
  ftag_in_uskl (pskl_to_uskl P) [=] empty.
Proof. induction P; simpl; fsetdec. Qed.

(** Instantiating a wf∅ ∀-body at a wf∅ argument stays wf∅. *)
Lemma a_wf_pskl_all_open : forall Θ P X,
  Θ ⨟ empty ⊢ₚₛᵃ (pskl_all_syn P) ->
  Θ ⨟ empty ⊢ₚₛᵃ X ->
  Θ ⨟ empty ⊢ₚₛᵃ (open_pskl_wrt_pskl P X).
Proof.
  intros Θ P X Hall HX.
  destruct (a_wf_pskl_all_inv Hall) as [Lw Hb].
  destruct (atom_fresh (Lw `union` dom Θ `union` ftvar_in_pskl P))
    as [γ Frγ].
  rewrite (subst_pskl_in_pskl_intro γ P X ltac:(clear - Frγ; fsetdec)).
  eapply a_wf_pskl_subst_tvar with (Δ := add γ empty);
    [ apply Hb; clear - Frγ; fsetdec
    | clear - Frγ; fsetdec
    | clear - Frγ; fsetdec
    | exact HX ].
Qed.

(** Two increases from the SAME source have metasubstitutions of the same
    length (the walk is positional: exactly the source's flexible entries
    are consumed). *)
Lemma a_inc_same_length : forall Θ0 ζ1 Θ1,
  ζ1 ∷ Θ0 ⊑ Θ1 ->
  forall ζ2 Θ2, ζ2 ∷ Θ0 ⊑ Θ2 ->
  length ζ1 = length ζ2.
Proof.
  intros Θ0 ζ1 Θ1 H; induction H; intros ζx Θx Hx; inversion Hx; subst;
    simpl; try reflexivity; try (f_equal; eapply IHa_inc; eassumption);
    eauto.
Qed.

(** App-injectivity from tail lengths. *)
Lemma app_inj_tail_length : forall (A : Type) (l1 l2 m1 m2 : list A),
  l1 ++ l2 = m1 ++ m2 -> length l2 = length m2 -> l1 = m1 /\ l2 = m2.
Proof.
  intros A l1 l2 m1 m2 Heq Hlen.
  assert (Hl1 : length l1 = length m1).
  { pose proof (f_equal (@length _) Heq) as HL.
    rewrite ! app_length in HL. lia. }
  revert m1 Heq Hl1; induction l1; intros [ | b m1 ] Heq Hl1;
    simpl in *; try discriminate Hl1; auto.
  injection Heq as -> Heq.
  destruct (IHl1 _ Heq ltac:(lia)) as [-> ->]. auto.
Qed.

(** Paintings of types are ghost-free (a [ptyp] has no ghosts to paint). *)
Lemma pskl_to_uskl_ptyp_ghost_free : forall A,
  lc_ptyp A ->
  uskl_ghost_free (pskl_to_uskl (ptyp_to_pskl A)).
Proof.
  intros A Hlc; induction Hlc; cbn.
  - apply uskl_ghost_free__unit.
  - apply uskl_ghost_free__var.
  - apply uskl_ghost_free__arrow; assumption.
  - apply uskl_ghost_free__all_syn with (L := empty).
    intros α _.
    change (uskl_var_f α) with (pskl_to_uskl (pskl_var_f α)).
    rewrite <- pskl_to_uskl_open.
    rewrite <- ptyp_to_pskl_open.
    auto.
Qed.

(** The same, from local closure of the PAINTING (what wf hands out). *)
Lemma pskl_to_uskl_paint_ghost_free : forall Pp,
  lc_pskl Pp ->
  forall A, Pp = ptyp_to_pskl A ->
  uskl_ghost_free (pskl_to_uskl Pp).
Proof.
  intros Pp Hlc; induction Hlc; intros A0 HeqA;
    destruct A0; cbn in HeqA; try discriminate HeqA; cbn.
  - apply uskl_ghost_free__unit.
  - apply uskl_ghost_free__var.
  - injection HeqA as HeqA1 HeqA2.
    apply uskl_ghost_free__arrow;
      [ eapply IHHlc1; exact HeqA1 | eapply IHHlc2; exact HeqA2 ].
  - injection HeqA as HeqA0.
    apply uskl_ghost_free__all_syn with (L := empty).
    intros α _.
    change (uskl_var_f α) with (pskl_to_uskl (pskl_var_f α)).
    rewrite <- pskl_to_uskl_open.
    eapply H0 with (A := open_ptyp_wrt_ptyp A0 (ptyp_var_f α)).
    rewrite HeqA0. symmetry. apply ptyp_to_pskl_open.
Qed.

(* ===================================================================== *)
(*  P7b, THE ForallL CASE (paper :3374-3453) — TAGGED-subject variant.    *)
(*                                                                        *)
(*  The row lemma takes the join row's fields as hypotheses (the bundle   *)
(*  dispatches on the join's last rule, as with ForallR), plus TASK 0's   *)
(*  [sub_shield] gate and the paper's WLOG (H3: when [P0] is a ∀ the      *)
(*  bundle dispatches ForallR first).  Assembly per the paper:            *)
(*  slack-erase the join at the exact κ-image subject                     *)
(*  ([ad_pat_sub_g_tyequiv_subject] on the inverted body ≡ᵘ family);      *)
(*  P6-L at ambient [Ψ ∪ Ψa] returns the extract + [κa];                  *)
(*  [uskl_precise_of_precise] + [uskl_precise_open_into] build the ⊑ᵤ     *)
(*  pair and [ad_pat_sub_precise_upre_gv] swaps the ORIGINAL join's       *)
(*  subject to the guess's image, dropping [Ψa]; the IH runs at           *)
(*  [(Ξ ++ Θ0, κa ++ κ)] with the slack regenerated at the new            *)
(*  instantiation; algorithmic [ForallL] closes with the extract family;  *)
(*  the package peels the [Ξ]-flex block off the IH's own ([length]-      *)
(*  identified tails — the walks are positional).                         *)
(* ===================================================================== *)

Lemma a_sub_complete_forall_l_tagged :
  forall n NM M Θ0 P0 P Rb Rj Ψ Θ κ Q ε Ψa ψa,
  (forall NM' M' Θ0' P0' P' R'' T'' Ψ' Θ' κ' Q',
     sub_complete_concl n NM' M' Θ0' P0' P' R'' T'' Ψ' Θ' κ' Q') ->
  M <> mode_ti ->
  Ψa ∩ Ψ [=] empty ->
  Ψa ∩ (ftag_in_uskl (uskl_all_etag ε Rj)) [=] empty ->
  a_tags_sort NM Ψa ψa ->
  Θ ⨟ empty ⊢ₚₛᵃ ⌊ ψa ⌋ˢ ->
  ad_pat_sub_gv n NM M (Ψ `union` Ψa) Θ (open_uskl_wrt_uskl Rj ψa) Q ->
  (* ⭕⭕ TASK 0's GATE IS GONE (2026-08-05).  It used to demand
     [sub_shield Θ0 Ψa ∅ α P0 (open Rb α) ψa] at every marker, and no general
     supply route existed for a [P0] carrying a ∀ below its head — that
     residual is what kept [main_forall] a hypothesis.  Under the authors'
     repaired [SolE-FlexR], [sub_shield] lost its guess-descending conjunct
     and, at Δρ = ∅, is unconditionally TRUE ([sub_shield_empty]).  P6-L
     discharges it internally and no longer takes it. *)
  (guarded_pskl P0 \/ P0 = pskl_hole) ->
  sub_complete_concl (S n) NM M Θ0 P0 P (uskl_all_etag ε Rb)
    (uskl_all_etag ε Rj) Ψ Θ κ Q.
Proof.
  intros n NM M Θ0 P0 P Rb Rj Ψ Θ κ Q ε Ψa ψa
    IH HMti HΨaΨ HΨaftag Htags Hwfψa HD HP0wlog.
  unfold sub_complete_concl.
  intros Hwf0 Hwfth HwfP0 HwfP HmodSK HmodTY HeqP Hinc Hrel Hsub Hrs HwfQ Hgf.
  cbn in HeqP. subst P.
  (* ---- 0. ambient facts ---- *)
  assert (Hlcκ : msubst_lc κ) by (eapply a_inc_msubst_lc; exact Hinc).
  assert (Htskψa : is_tskl ψa) by (inversion Htags; subst; assumption).
  assert (Hdtags : d_tags_skl Ψa ψa) by (inversion Htags; subst; assumption).
  assert (Hlcψa : lc_uskl ψa) by (apply is_tskl_lc; exact Htskψa).
  assert (Hlcall : lc_uskl (uskl_all_etag ε Rb))
    by (apply lc_uskl_of_pskl; eapply a_wf_pskl_lc; exact HwfP).
  assert (Hlcb : forall β, lc_uskl (open_uskl_wrt_uskl Rb (uskl_var_f β)))
    by (inversion Hlcall; subst; assumption).
  assert (Hlcjall : lc_uskl (uskl_all_etag ε Rj))
    by (exact (proj1 (a_uskl_tyequiv_lc Hrel))).
  assert (Hlcj : forall β, lc_uskl (open_uskl_wrt_uskl Rj (uskl_var_f β)))
    by (inversion Hlcjall; subst; assumption).
  (* the subject's variables are Θ0-scoped *)
  assert (Hftvb : ftvar_in_uskl Rb [<=] dom Θ0).
  { intros β Hβ.
    pose proof (a_wf_pskl_ftv_dom HwfP) as Hsc.
    assert (Hβp : β `in` ftvar_in_pskl ⌊ uskl_all_etag ε Rb ⌋ˢ).
    { change (ftvar_in_pskl ⌊ uskl_all_etag ε Rb ⌋ˢ)
        with (ftvar_in_pskl ⌊ Rb ⌋ˢ).
      rewrite ftvar_in_pskl_uskl_to_pskl. exact Hβ. }
    apply Hsc. exact Hβp. }
  (* ---- 1. the body ≡ᵘ family and the ftag transfer ---- *)
  cbn in Hrel.
  destruct (a_uskl_tyequiv_all_etag_inv Hrel) as [Le Hrelb].
  assert (Hftjb : ftag_in_uskl Rj [=] ftag_in_uskl Rb).
  { destruct (atom_fresh Le) as [β Frβ].
    pose proof (a_uskl_tyequiv_ftag (Hrelb β Frβ)) as Hf.
    rewrite (ftag_in_uskl_open_var Rj β) in Hf.
    rewrite (ftag_in_uskl_open_var (msubst_uskl_syn κ Rb) β) in Hf.
    rewrite (ftag_in_uskl_msubst_uskl_syn κ Rb) in Hf.
    exact Hf. }
  (* ---- 2. fresh α, the slack-erased join, and P6-L ---- *)
  destruct (atom_fresh
    (Le `union` dom Θ0 `union` dom Θ `union` dom κ
       `union` ftvar_in_uskl Rb `union` ftvar_in_pskl ⌊ Rb ⌋ˢ
       `union` ftvar_in_aenv Θ0 `union` ftvar_in_pskl P0
       `union` ftvar_in_uskl (msubst_uskl_syn κ Rb))) as [α Fr].
  assert (Hbody_eq : Θ ⊢ (open_uskl_wrt_uskl (msubst_uskl_syn κ Rb) ψa)
                       ≡ᵘ (open_uskl_wrt_uskl Rj ψa)).
  { eapply a_uskl_tyequiv_open with (L := Le);
      [ intros β Hβ; exact (a_uskl_tyequiv_sym (Hrelb β Hβ))
      | exact Hlcψa ]. }
  assert (Hsubty : ad_pat_sub_g n NM M (Ψ `union` Ψa) Θ
                     (subst_bskl_in_uskl ψa α
                        (msubst_uskl_syn κ
                           (open_uskl_wrt_uskl Rb (uskl_var_f α)))) Q).
  { rewrite (msubst_uskl_syn_open Rb Hinc
               (α := α) ltac:(clear - Fr; fsetdec)).
    rewrite <- (subst_bskl_in_uskl_intro α (msubst_uskl_syn κ Rb) ψa
                  ltac:(clear - Fr; fsetdec)).
    eapply ad_pat_sub_g_tyequiv_subject;
      [ apply ad_pat_sub_gv_forget; exact HD | exact Hwfth
      | exact Hbody_eq ]. }
  assert (HwfSubj : Θ ⨟ empty ⊢ₚₛᵃ
            (uskl_to_pskl
               (subst_bskl_in_uskl ψa α
                  (msubst_uskl_syn κ
                     (open_uskl_wrt_uskl Rb (uskl_var_f α)))))).
  { rewrite (msubst_uskl_syn_open Rb Hinc
               (α := α) ltac:(clear - Fr; fsetdec)).
    rewrite <- (subst_bskl_in_uskl_intro α (msubst_uskl_syn κ Rb) ψa
                  ltac:(clear - Fr; fsetdec)).
    rewrite uskl_to_pskl_open_gen.
    apply a_wf_pskl_all_open; [ | exact Hwfψa ].
    assert (HwfPθ : Θ ⨟ empty ⊢ₚₛᵃ (msubst_pskl κ ⌊ uskl_all_etag ε Rb ⌋ˢ)).
    { eapply a_wf_pskl_msubst_inc;
        [ exact Hinc | exact Hwf0 | exact HwfP
        | intros β Hβ; exfalso; clear - Hβ; fsetdec ]. }
    cbn in HwfPθ.
    rewrite (uskl_to_pskl_msubst_uskl_syn κ Rb).
    exact HwfPθ. }
  destruct (@a_extract_complete_gen n NM M Θ0 Θ κ empty Ψa
              (Ψ `union` Ψa) ψa Q
              (open_pskl_wrt_pskl ⌊ Rb ⌋ˢ (pskl_var_f α)) P0
              (open_uskl_wrt_uskl Rb (uskl_var_f α)) α
              Hwfth Hwf0 HwfP0 HmodSK HmodTY Hinc
              ltac:(clear - Fr; fsetdec) ltac:(clear - Fr; fsetdec)
              (uskl_to_pskl_open Rb α)
              ltac:(pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper
                                  Rb (uskl_var_f α)) as Hup;
                    cbn in Hup; clear - Hup Hftvb; fsetdec)
              (Hlcb α) Htags
              ltac:(rewrite (ftag_in_uskl_open_var Rb α);
                    cbn in HΨaftag; clear - HΨaftag Hftjb; fsetdec)
              ltac:(clear; fsetdec)
              (* ⭐ P6-L's new guess-scope premise (the SolE-FlexR repair):
                 read straight off the guess's own well-formedness *)
              ltac:(assert (Hdψ : ftvar_in_uskl ψa [<=] empty `union` dom Θ)
                      by (apply uskl_wf_ftv_dom; exact Hwfψa);
                    clear - Hdψ; fsetdec)
              Hwfψa
              ltac:(intros β α0 τ Hβ; exfalso; clear - Hβ; fsetdec)
              ltac:(pose proof (ad_pat_sub_g_ftag_sub
                                  (ad_pat_sub_gv_forget HD)) as Hfs;
                    pose proof (ftag_in_uskl_open_upper Rj ψa) as Hou;
                    pose proof (d_tags_skl_ftag Hdtags) as Htg;
                    rewrite (ftag_in_uskl_open_var Rb α);
                    clear - Hfs Hou Htg Hftjb; fsetdec)
              ltac:(clear; fsetdec)
              Hsubty HwfSubj
              (ad_refine_syn_f_forget Hrs))
    as (Ξ & Pa & κa & Hlook & HwfPa & HwfΞΘ0 & HdeclsΞ & Hkeys
        & Hinca & Hie0 & Hpre).
  (* ---- 3. the ⊑ᵤ pair and the subject swap on the ORIGINAL join ---- *)
  assert (Hdomκa : dom κa [=] dom Ξ) by (apply keys_eq_dom; exact Hkeys).
  assert (HdomΞ : forall β, β `in` dom Ξ -> β `notin` dom Θ0).
  { intros β Hβ Hc.
    pose proof (a_wf_aenv_uniq HwfΞΘ0) as Hu.
    clear - Hu Hβ Hc. solve_uniq. }
  assert (HwfPaΘ : Θ ⨟ empty ⊢ₚₛᵃ (msubst_pskl (κa ++ κ) Pa)).
  { eapply a_wf_pskl_msubst_inc;
      [ exact Hinca | exact HwfΞΘ0 | exact HwfPa
      | intros β Hβ; exfalso; clear - Hβ; fsetdec ]. }
  assert (HlcψPa : lc_uskl (pskl_to_uskl (msubst_pskl (κa ++ κ) Pa)))
    by (apply pskl_to_uskl_lc; eapply a_wf_pskl_lc; exact HwfPaΘ).
  assert (Hupair : uskl_precise Θ Ψa
                     (pskl_to_uskl (msubst_pskl (κa ++ κ) Pa)) ψa).
  { eapply uskl_precise_of_precise with (Θ := Θ);
      [ exact Hpre | exact Hwfth | reflexivity | reflexivity
      | exact Htskψa | exact Hdtags ]. }
  destruct (uskl_precise_open_into Rj Hlcj Hupair Hlcψa)
    as [Ψrep' [HΨrep' Hopen_pair]].
  (* TY: the swapped subject is ghost-free — the body from the MOTIVE's
     ghost-freeness premise ([Hgf]), the instantiation because a TY-guess
     is a TYPE.  Named, because BOTH the subject swap below and the IH's
     own motive premise consume it. *)
  assert (Hgfswap : NM = a_sub_mode_ty ->
            uskl_ghost_free
              (open_uskl_wrt_uskl Rj
                 (pskl_to_uskl (msubst_pskl (κa ++ κ) Pa)))).
  { intro HeqNM. subst NM.
    assert (HgfPa : uskl_ghost_free
                      (pskl_to_uskl (msubst_pskl (κa ++ κ) Pa))).
    { inversion Hlook; subst.
      match goal with Hg : a_guess _ a_sub_mode_ty _ _ _ |- _ =>
        inversion Hg; subst end.
      rewrite msubst_pskl_ptyp_to_pskl in HwfPaΘ |- *.
      eapply pskl_to_uskl_paint_ghost_free;
        [ eapply a_wf_pskl_lc; exact HwfPaΘ | reflexivity ]. }
    destruct (uskl_ghost_free_all_etag_inv (Hgf eq_refl)) as [Lg Hgb].
    destruct (atom_fresh (Lg `union` ftvar_in_uskl Rj)) as [γ Frγ].
    rewrite (subst_bskl_in_uskl_intro γ Rj
               (pskl_to_uskl (msubst_pskl (κa ++ κ) Pa))
               ltac:(clear - Frγ; fsetdec)).
    apply uskl_ghost_free_subst;
      [ apply Hgb; clear - Frγ; fsetdec | exact HgfPa | exact HlcψPa ]. }
  assert (HDswap : ad_pat_sub_gv n NM M Ψ Θ
            (open_uskl_wrt_uskl Rj
               (pskl_to_uskl (msubst_pskl (κa ++ κ) Pa))) Q).
  { eapply ad_pat_sub_precise_upre_gv with
      (Ψsup := Ψa) (Ψna := Ψa) (Ψr := Ψrep');
      [ exact HD | exact Hopen_pair | exact Hwfth
      | destruct HΨrep' as [He | He]; rewrite He; clear; fsetdec
      | intros x b0 Hb0; exact Hb0
      | exact Hwfth
      | clear; fsetdec
      | clear; fsetdec
      | exact HΨaΨ
      | pose proof (ftag_in_uskl_open_upper Rj
                      (pskl_to_uskl (msubst_pskl (κa ++ κ) Pa))) as Hou;
        pose proof (ftag_in_uskl_pskl_to_uskl
                      (msubst_pskl (κa ++ κ) Pa)) as Hemb;
        cbn in HΨaftag; clear - Hou Hemb HΨaftag Hftjb; fsetdec
      | exact HwfQ
      | exact Hgfswap ]. }
  (* ---- 4. the IH at (Ξ ++ Θ0, κa ++ κ) ---- *)
  assert (Hmon0 : forall x (b : abind), binds x b Θ0 -> binds x b (Ξ ++ Θ0))
    by (intros x b0 Hb0; unfold binds in *; apply in_or_app; right;
        exact Hb0).
  assert (HwfP0' : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P0)
    by (eapply a_wf_pskl_weaken; [ exact Hmon0 | exact HwfP0 ]).
  assert (HeqPnew : ⌊ open_uskl_wrt_uskl Rb (pskl_to_uskl Pa) ⌋ˢ
                    = open_pskl_wrt_pskl ⌊ Rb ⌋ˢ Pa).
  { rewrite uskl_to_pskl_open_gen.
    rewrite uskl_to_pskl_pskl_to_uskl. reflexivity. }
  assert (HwfPnew : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ
                      (open_pskl_wrt_pskl ⌊ Rb ⌋ˢ Pa)).
  { apply a_wf_pskl_all_open; [ | exact HwfPa ].
    change (pskl_all_syn ⌊ Rb ⌋ˢ) with ⌊ uskl_all_etag ε Rb ⌋ˢ.
    eapply a_wf_pskl_weaken; [ exact Hmon0 | exact HwfP ]. }
  assert (Hcollapse : msubst_uskl_syn (κa ++ κ) Rb = msubst_uskl_syn κ Rb).
  { apply msubst_uskl_syn_agree. intros β Hβ.
    apply msubst_lookup_app_notin.
    assert (HβΘ0 : β `in` dom Θ0) by (clear - Hβ Hftvb; fsetdec).
    intro Hc.
    apply (HdomΞ β); [ clear - Hc Hdomκa; fsetdec | exact HβΘ0 ]. }
  assert (Hslack : Θ ⊢ (open_uskl_wrt_uskl Rj
                          (pskl_to_uskl (msubst_pskl (κa ++ κ) Pa)))
                     ≡ᵘ (msubst_uskl_syn (κa ++ κ)
                           (open_uskl_wrt_uskl Rb (pskl_to_uskl Pa)))).
  { assert (Hro : msubst_uskl_syn (κa ++ κ)
                    (open_uskl_wrt_uskl Rb (pskl_to_uskl Pa))
                = open_uskl_wrt_uskl (msubst_uskl_syn (κa ++ κ) Rb)
                    (msubst_uskl_syn (κa ++ κ) (pskl_to_uskl Pa))).
    { unfold open_uskl_wrt_uskl.
      apply (msubst_uskl_syn_open_rec Rb (pskl_to_uskl Pa) 0 Hinca). }
    rewrite Hro. rewrite Hcollapse.
    rewrite msubst_uskl_syn_pskl_to_uskl.
    eapply a_uskl_tyequiv_open with (L := Le);
      [ intros β Hβ; exact (Hrelb β Hβ)
      | exact HlcψPa ]. }
  assert (HrsΞ : ad_refine_syn_f empty Θ empty
                   (pskl_to_bskl_inh (msubst_pskl (κa ++ κ) P0)) Q).
  { assert (HP0c : msubst_pskl (κa ++ κ) P0 = msubst_pskl κ P0).
    { apply msubst_pskl_agree. intros β Hβ.
      apply msubst_lookup_app_notin.
      assert (HβΘ0 : β `in` dom Θ0)
        by (apply (a_wf_pskl_ftv_dom HwfP0); exact Hβ).
      intro Hc.
      apply (HdomΞ β); [ clear - Hc Hdomκa; fsetdec | exact HβΘ0 ]. }
    rewrite HP0c. exact Hrs. }
  destruct (IH NM M (Ξ ++ Θ0) P0 (open_pskl_wrt_pskl ⌊ Rb ⌋ˢ Pa)
              (open_uskl_wrt_uskl Rb (pskl_to_uskl Pa))
              (open_uskl_wrt_uskl Rj
                 (pskl_to_uskl (msubst_pskl (κa ++ κ) Pa)))
              Ψ Θ (κa ++ κ) Q
              HwfΞΘ0 Hwfth HwfP0' HwfPnew HmodSK HmodTY HeqPnew Hinca
              Hslack HDswap HrsΞ HwfQ Hgfswap)
    as [P1 [Θ1 [Hrun Hopt]]].
  (* ---- 5. the run ---- *)
  exists P1, Θ1. split.
  { (* [a_sub__forall_l] is EXISTS-FRESH (campaign cluster 5): P6-L's ONE
       instance IS the premise now, no family to rebuild. *)
    eapply a_sub__forall_l with (α := α) (Ξ := Ξ) (P1 := Pa);
      [ exact HMti | exact HP0wlog
      | clear - Fr; fsetdec
      | exact Hlook
      | apply a_wf_aenv_uniq; exact HwfΞΘ0
      | exact HwfPa
      | exact Hrun ]. }
  (* ---- 6. the package ---- *)
  intros κf Hidf Hincf.
  destruct (a_sub_sound_thm Hrun HwfΞΘ0 HwfP0' HwfPnew HmodSK HmodTY)
    as [[[w [Hidw Hincw]] Hdefs] [HwfΘ1 _]].
  destruct (Hopt w Hidw Hincw) as [ζ' [Hζ' [Hie' Hprec']]].
  exists ζ'. split; [ exact Hζ' | ]. split.
  { (* peel the Ξ-flex block; identify the tails by length *)
    destruct (@a_inc_peel_suffix Ξ Θ0 w Θ1
                (a_decls_suffix HdeclsΞ) Hincw)
      as [wa [wb [-> [Hdomwa Hincwb]]]].
    assert (Hidwb : is_id_msubst wb).
    { unfold is_id_msubst in *. apply Forall_app in Hidw. tauto. }
    assert (Heqwb : wb = κf)
      by (eapply is_id_inc_unique;
          [ exact Hincwb | exact Hidwb | exact Hincf | exact Hidf ]).
    subst wb.
    assert (Hcompw : msubst_compose ζ' (wa ++ κf)
                   = msubst_compose ζ' wa ++ msubst_compose ζ' κf)
      by (unfold msubst_compose; apply List.map_app).
    rewrite Hcompw in Hie'.
    assert (Hinccomp : (msubst_compose ζ' wa ++ msubst_compose ζ' κf)
                         ∷ (Ξ ++ Θ0) ⊑ Θ).
    { rewrite <- Hcompw.
      eapply a_inc_compose;
        [ exact Hincw | exact HwfΞΘ0 | exact HwfΘ1 | exact Hζ' ]. }
    destruct (@a_inc_equiv_inc_peel_suffix Ξ Θ0 (κa ++ κ)
                (msubst_compose ζ' wa ++ msubst_compose ζ' κf) Θ
                (a_decls_suffix HdeclsΞ) Hie' Hinca Hinccomp)
      as [κ1b [κ2b [Hie2 [Hib1 [Hib2 [[p1 [Hp1 Hd1]] [p2 [Hp2 Hd2]]]]]]]].
    assert (Hlen1 : length κ = length κ1b)
      by (symmetry; eapply a_inc_same_length; [ exact Hib1 | exact Hinc ]).
    destruct (app_inj_tail_length κa κ p1 κ1b Hp1 Hlen1) as [_ Heqκ1b].
    subst κ1b.
    assert (Hlen2 : length (msubst_compose ζ' κf) = length κ2b).
    { assert (Hl2a : length κ2b = length κ)
        by (eapply a_inc_same_length; [ exact Hib2 | exact Hinc ]).
      assert (Hl2b : length κf = length κ)
        by (eapply a_inc_same_length; [ exact Hincf | exact Hinc ]).
      unfold msubst_compose. rewrite List.map_length.
      clear - Hl2a Hl2b; lia. }
    destruct (app_inj_tail_length (msubst_compose ζ' wa)
                (msubst_compose ζ' κf) p2 κ2b Hp2 Hlen2) as [_ Heqκ2b].
    subst κ2b.
    exact Hie2. }
  { exact Hprec'. }
Qed.

Print Assumptions a_sub_complete_forall_l_tagged.

(* ===================================================================== *)
(*  P7b, the ForallL case — UNTAGGED-subject variant (∀·): the same       *)
(*  assembly at [uskl_all_syn] subjects.                                  *)
(* ===================================================================== *)

Lemma a_sub_complete_forall_l_untagged :
  forall n NM M Θ0 P0 P Rb Rj Ψ Θ κ Q Ψa ψa,
  (forall NM' M' Θ0' P0' P' R'' T'' Ψ' Θ' κ' Q',
     sub_complete_concl n NM' M' Θ0' P0' P' R'' T'' Ψ' Θ' κ' Q') ->
  M <> mode_ti ->
  Ψa ∩ Ψ [=] empty ->
  Ψa ∩ (ftag_in_uskl (uskl_all_syn Rj)) [=] empty ->
  a_tags_sort NM Ψa ψa ->
  Θ ⨟ empty ⊢ₚₛᵃ ⌊ ψa ⌋ˢ ->
  ad_pat_sub_gv n NM M (Ψ `union` Ψa) Θ (open_uskl_wrt_uskl Rj ψa) Q ->
  (* ⭕⭕ TASK 0's GATE IS GONE (2026-08-05).  It used to demand
     [sub_shield Θ0 Ψa ∅ α P0 (open Rb α) ψa] at every marker, and no general
     supply route existed for a [P0] carrying a ∀ below its head — that
     residual is what kept [main_forall] a hypothesis.  Under the authors'
     repaired [SolE-FlexR], [sub_shield] lost its guess-descending conjunct
     and, at Δρ = ∅, is unconditionally TRUE ([sub_shield_empty]).  P6-L
     discharges it internally and no longer takes it. *)
  (guarded_pskl P0 \/ P0 = pskl_hole) ->
  sub_complete_concl (S n) NM M Θ0 P0 P (uskl_all_syn Rb)
    (uskl_all_syn Rj) Ψ Θ κ Q.
Proof.
  intros n NM M Θ0 P0 P Rb Rj Ψ Θ κ Q Ψa ψa
    IH HMti HΨaΨ HΨaftag Htags Hwfψa HD HP0wlog.
  unfold sub_complete_concl.
  intros Hwf0 Hwfth HwfP0 HwfP HmodSK HmodTY HeqP Hinc Hrel Hsub Hrs HwfQ Hgf.
  cbn in HeqP. subst P.
  (* ---- 0. ambient facts ---- *)
  assert (Hlcκ : msubst_lc κ) by (eapply a_inc_msubst_lc; exact Hinc).
  assert (Htskψa : is_tskl ψa) by (inversion Htags; subst; assumption).
  assert (Hdtags : d_tags_skl Ψa ψa) by (inversion Htags; subst; assumption).
  assert (Hlcψa : lc_uskl ψa) by (apply is_tskl_lc; exact Htskψa).
  assert (Hlcall : lc_uskl (uskl_all_syn Rb))
    by (apply lc_uskl_of_pskl; eapply a_wf_pskl_lc; exact HwfP).
  assert (Hlcb : forall β, lc_uskl (open_uskl_wrt_uskl Rb (uskl_var_f β)))
    by (inversion Hlcall; subst; assumption).
  assert (Hlcjall : lc_uskl (uskl_all_syn Rj))
    by (exact (proj1 (a_uskl_tyequiv_lc Hrel))).
  assert (Hlcj : forall β, lc_uskl (open_uskl_wrt_uskl Rj (uskl_var_f β)))
    by (inversion Hlcjall; subst; assumption).
  (* the subject's variables are Θ0-scoped *)
  assert (Hftvb : ftvar_in_uskl Rb [<=] dom Θ0).
  { intros β Hβ.
    pose proof (a_wf_pskl_ftv_dom HwfP) as Hsc.
    assert (Hβp : β `in` ftvar_in_pskl ⌊ uskl_all_syn Rb ⌋ˢ).
    { change (ftvar_in_pskl ⌊ uskl_all_syn Rb ⌋ˢ)
        with (ftvar_in_pskl ⌊ Rb ⌋ˢ).
      rewrite ftvar_in_pskl_uskl_to_pskl. exact Hβ. }
    apply Hsc. exact Hβp. }
  (* ---- 1. the body ≡ᵘ family and the ftag transfer ---- *)
  cbn in Hrel.
  destruct (a_uskl_tyequiv_all_syn_inv Hrel) as [Le Hrelb].
  assert (Hftjb : ftag_in_uskl Rj [=] ftag_in_uskl Rb).
  { destruct (atom_fresh Le) as [β Frβ].
    pose proof (a_uskl_tyequiv_ftag (Hrelb β Frβ)) as Hf.
    rewrite (ftag_in_uskl_open_var Rj β) in Hf.
    rewrite (ftag_in_uskl_open_var (msubst_uskl_syn κ Rb) β) in Hf.
    rewrite (ftag_in_uskl_msubst_uskl_syn κ Rb) in Hf.
    exact Hf. }
  (* ---- 2. fresh α, the slack-erased join, and P6-L ---- *)
  destruct (atom_fresh
    (Le `union` dom Θ0 `union` dom Θ `union` dom κ
       `union` ftvar_in_uskl Rb `union` ftvar_in_pskl ⌊ Rb ⌋ˢ
       `union` ftvar_in_aenv Θ0 `union` ftvar_in_pskl P0
       `union` ftvar_in_uskl (msubst_uskl_syn κ Rb))) as [α Fr].
  assert (Hbody_eq : Θ ⊢ (open_uskl_wrt_uskl (msubst_uskl_syn κ Rb) ψa)
                       ≡ᵘ (open_uskl_wrt_uskl Rj ψa)).
  { eapply a_uskl_tyequiv_open with (L := Le);
      [ intros β Hβ; exact (a_uskl_tyequiv_sym (Hrelb β Hβ))
      | exact Hlcψa ]. }
  assert (Hsubty : ad_pat_sub_g n NM M (Ψ `union` Ψa) Θ
                     (subst_bskl_in_uskl ψa α
                        (msubst_uskl_syn κ
                           (open_uskl_wrt_uskl Rb (uskl_var_f α)))) Q).
  { rewrite (msubst_uskl_syn_open Rb Hinc
               (α := α) ltac:(clear - Fr; fsetdec)).
    rewrite <- (subst_bskl_in_uskl_intro α (msubst_uskl_syn κ Rb) ψa
                  ltac:(clear - Fr; fsetdec)).
    eapply ad_pat_sub_g_tyequiv_subject;
      [ apply ad_pat_sub_gv_forget; exact HD | exact Hwfth
      | exact Hbody_eq ]. }
  assert (HwfSubj : Θ ⨟ empty ⊢ₚₛᵃ
            (uskl_to_pskl
               (subst_bskl_in_uskl ψa α
                  (msubst_uskl_syn κ
                     (open_uskl_wrt_uskl Rb (uskl_var_f α)))))).
  { rewrite (msubst_uskl_syn_open Rb Hinc
               (α := α) ltac:(clear - Fr; fsetdec)).
    rewrite <- (subst_bskl_in_uskl_intro α (msubst_uskl_syn κ Rb) ψa
                  ltac:(clear - Fr; fsetdec)).
    rewrite uskl_to_pskl_open_gen.
    apply a_wf_pskl_all_open; [ | exact Hwfψa ].
    assert (HwfPθ : Θ ⨟ empty ⊢ₚₛᵃ (msubst_pskl κ ⌊ uskl_all_syn Rb ⌋ˢ)).
    { eapply a_wf_pskl_msubst_inc;
        [ exact Hinc | exact Hwf0 | exact HwfP
        | intros β Hβ; exfalso; clear - Hβ; fsetdec ]. }
    cbn in HwfPθ.
    rewrite (uskl_to_pskl_msubst_uskl_syn κ Rb).
    exact HwfPθ. }
  destruct (@a_extract_complete_gen n NM M Θ0 Θ κ empty Ψa
              (Ψ `union` Ψa) ψa Q
              (open_pskl_wrt_pskl ⌊ Rb ⌋ˢ (pskl_var_f α)) P0
              (open_uskl_wrt_uskl Rb (uskl_var_f α)) α
              Hwfth Hwf0 HwfP0 HmodSK HmodTY Hinc
              ltac:(clear - Fr; fsetdec) ltac:(clear - Fr; fsetdec)
              (uskl_to_pskl_open Rb α)
              ltac:(pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper
                                  Rb (uskl_var_f α)) as Hup;
                    cbn in Hup; clear - Hup Hftvb; fsetdec)
              (Hlcb α) Htags
              ltac:(rewrite (ftag_in_uskl_open_var Rb α);
                    cbn in HΨaftag; clear - HΨaftag Hftjb; fsetdec)
              ltac:(clear; fsetdec)
              (* ⭐ P6-L's new guess-scope premise (the SolE-FlexR repair):
                 read straight off the guess's own well-formedness *)
              ltac:(assert (Hdψ : ftvar_in_uskl ψa [<=] empty `union` dom Θ)
                      by (apply uskl_wf_ftv_dom; exact Hwfψa);
                    clear - Hdψ; fsetdec)
              Hwfψa
              ltac:(intros β α0 τ Hβ; exfalso; clear - Hβ; fsetdec)
              ltac:(pose proof (ad_pat_sub_g_ftag_sub
                                  (ad_pat_sub_gv_forget HD)) as Hfs;
                    pose proof (ftag_in_uskl_open_upper Rj ψa) as Hou;
                    pose proof (d_tags_skl_ftag Hdtags) as Htg;
                    rewrite (ftag_in_uskl_open_var Rb α);
                    clear - Hfs Hou Htg Hftjb; fsetdec)
              ltac:(clear; fsetdec)
              Hsubty HwfSubj
              (ad_refine_syn_f_forget Hrs))
    as (Ξ & Pa & κa & Hlook & HwfPa & HwfΞΘ0 & HdeclsΞ & Hkeys
        & Hinca & Hie0 & Hpre).
  (* ---- 3. the ⊑ᵤ pair and the subject swap on the ORIGINAL join ---- *)
  assert (Hdomκa : dom κa [=] dom Ξ) by (apply keys_eq_dom; exact Hkeys).
  assert (HdomΞ : forall β, β `in` dom Ξ -> β `notin` dom Θ0).
  { intros β Hβ Hc.
    pose proof (a_wf_aenv_uniq HwfΞΘ0) as Hu.
    clear - Hu Hβ Hc. solve_uniq. }
  assert (HwfPaΘ : Θ ⨟ empty ⊢ₚₛᵃ (msubst_pskl (κa ++ κ) Pa)).
  { eapply a_wf_pskl_msubst_inc;
      [ exact Hinca | exact HwfΞΘ0 | exact HwfPa
      | intros β Hβ; exfalso; clear - Hβ; fsetdec ]. }
  assert (HlcψPa : lc_uskl (pskl_to_uskl (msubst_pskl (κa ++ κ) Pa)))
    by (apply pskl_to_uskl_lc; eapply a_wf_pskl_lc; exact HwfPaΘ).
  assert (Hupair : uskl_precise Θ Ψa
                     (pskl_to_uskl (msubst_pskl (κa ++ κ) Pa)) ψa).
  { eapply uskl_precise_of_precise with (Θ := Θ);
      [ exact Hpre | exact Hwfth | reflexivity | reflexivity
      | exact Htskψa | exact Hdtags ]. }
  destruct (uskl_precise_open_into Rj Hlcj Hupair Hlcψa)
    as [Ψrep' [HΨrep' Hopen_pair]].
  (* TY: the swapped subject is ghost-free — the body from the MOTIVE's
     ghost-freeness premise ([Hgf]), the instantiation because a TY-guess
     is a TYPE.  Named, because BOTH the subject swap below and the IH's
     own motive premise consume it. *)
  assert (Hgfswap : NM = a_sub_mode_ty ->
            uskl_ghost_free
              (open_uskl_wrt_uskl Rj
                 (pskl_to_uskl (msubst_pskl (κa ++ κ) Pa)))).
  { intro HeqNM. subst NM.
    assert (HgfPa : uskl_ghost_free
                      (pskl_to_uskl (msubst_pskl (κa ++ κ) Pa))).
    { inversion Hlook; subst.
      match goal with Hg : a_guess _ a_sub_mode_ty _ _ _ |- _ =>
        inversion Hg; subst end.
      rewrite msubst_pskl_ptyp_to_pskl in HwfPaΘ |- *.
      eapply pskl_to_uskl_paint_ghost_free;
        [ eapply a_wf_pskl_lc; exact HwfPaΘ | reflexivity ]. }
    destruct (uskl_ghost_free_all_syn_inv (Hgf eq_refl)) as [Lg Hgb].
    destruct (atom_fresh (Lg `union` ftvar_in_uskl Rj)) as [γ Frγ].
    rewrite (subst_bskl_in_uskl_intro γ Rj
               (pskl_to_uskl (msubst_pskl (κa ++ κ) Pa))
               ltac:(clear - Frγ; fsetdec)).
    apply uskl_ghost_free_subst;
      [ apply Hgb; clear - Frγ; fsetdec | exact HgfPa | exact HlcψPa ]. }
  assert (HDswap : ad_pat_sub_gv n NM M Ψ Θ
            (open_uskl_wrt_uskl Rj
               (pskl_to_uskl (msubst_pskl (κa ++ κ) Pa))) Q).
  { eapply ad_pat_sub_precise_upre_gv with
      (Ψsup := Ψa) (Ψna := Ψa) (Ψr := Ψrep');
      [ exact HD | exact Hopen_pair | exact Hwfth
      | destruct HΨrep' as [He | He]; rewrite He; clear; fsetdec
      | intros x b0 Hb0; exact Hb0
      | exact Hwfth
      | clear; fsetdec
      | clear; fsetdec
      | exact HΨaΨ
      | pose proof (ftag_in_uskl_open_upper Rj
                      (pskl_to_uskl (msubst_pskl (κa ++ κ) Pa))) as Hou;
        pose proof (ftag_in_uskl_pskl_to_uskl
                      (msubst_pskl (κa ++ κ) Pa)) as Hemb;
        cbn in HΨaftag; clear - Hou Hemb HΨaftag Hftjb; fsetdec
      | exact HwfQ
      | exact Hgfswap ]. }
  (* ---- 4. the IH at (Ξ ++ Θ0, κa ++ κ) ---- *)
  assert (Hmon0 : forall x (b : abind), binds x b Θ0 -> binds x b (Ξ ++ Θ0))
    by (intros x b0 Hb0; unfold binds in *; apply in_or_app; right;
        exact Hb0).
  assert (HwfP0' : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P0)
    by (eapply a_wf_pskl_weaken; [ exact Hmon0 | exact HwfP0 ]).
  assert (HeqPnew : ⌊ open_uskl_wrt_uskl Rb (pskl_to_uskl Pa) ⌋ˢ
                    = open_pskl_wrt_pskl ⌊ Rb ⌋ˢ Pa).
  { rewrite uskl_to_pskl_open_gen.
    rewrite uskl_to_pskl_pskl_to_uskl. reflexivity. }
  assert (HwfPnew : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ
                      (open_pskl_wrt_pskl ⌊ Rb ⌋ˢ Pa)).
  { apply a_wf_pskl_all_open; [ | exact HwfPa ].
    change (pskl_all_syn ⌊ Rb ⌋ˢ) with ⌊ uskl_all_syn Rb ⌋ˢ.
    eapply a_wf_pskl_weaken; [ exact Hmon0 | exact HwfP ]. }
  assert (Hcollapse : msubst_uskl_syn (κa ++ κ) Rb = msubst_uskl_syn κ Rb).
  { apply msubst_uskl_syn_agree. intros β Hβ.
    apply msubst_lookup_app_notin.
    assert (HβΘ0 : β `in` dom Θ0) by (clear - Hβ Hftvb; fsetdec).
    intro Hc.
    apply (HdomΞ β); [ clear - Hc Hdomκa; fsetdec | exact HβΘ0 ]. }
  assert (Hslack : Θ ⊢ (open_uskl_wrt_uskl Rj
                          (pskl_to_uskl (msubst_pskl (κa ++ κ) Pa)))
                     ≡ᵘ (msubst_uskl_syn (κa ++ κ)
                           (open_uskl_wrt_uskl Rb (pskl_to_uskl Pa)))).
  { assert (Hro : msubst_uskl_syn (κa ++ κ)
                    (open_uskl_wrt_uskl Rb (pskl_to_uskl Pa))
                = open_uskl_wrt_uskl (msubst_uskl_syn (κa ++ κ) Rb)
                    (msubst_uskl_syn (κa ++ κ) (pskl_to_uskl Pa))).
    { unfold open_uskl_wrt_uskl.
      apply (msubst_uskl_syn_open_rec Rb (pskl_to_uskl Pa) 0 Hinca). }
    rewrite Hro. rewrite Hcollapse.
    rewrite msubst_uskl_syn_pskl_to_uskl.
    eapply a_uskl_tyequiv_open with (L := Le);
      [ intros β Hβ; exact (Hrelb β Hβ)
      | exact HlcψPa ]. }
  assert (HrsΞ : ad_refine_syn_f empty Θ empty
                   (pskl_to_bskl_inh (msubst_pskl (κa ++ κ) P0)) Q).
  { assert (HP0c : msubst_pskl (κa ++ κ) P0 = msubst_pskl κ P0).
    { apply msubst_pskl_agree. intros β Hβ.
      apply msubst_lookup_app_notin.
      assert (HβΘ0 : β `in` dom Θ0)
        by (apply (a_wf_pskl_ftv_dom HwfP0); exact Hβ).
      intro Hc.
      apply (HdomΞ β); [ clear - Hc Hdomκa; fsetdec | exact HβΘ0 ]. }
    rewrite HP0c. exact Hrs. }
  destruct (IH NM M (Ξ ++ Θ0) P0 (open_pskl_wrt_pskl ⌊ Rb ⌋ˢ Pa)
              (open_uskl_wrt_uskl Rb (pskl_to_uskl Pa))
              (open_uskl_wrt_uskl Rj
                 (pskl_to_uskl (msubst_pskl (κa ++ κ) Pa)))
              Ψ Θ (κa ++ κ) Q
              HwfΞΘ0 Hwfth HwfP0' HwfPnew HmodSK HmodTY HeqPnew Hinca
              Hslack HDswap HrsΞ HwfQ Hgfswap)
    as [P1 [Θ1 [Hrun Hopt]]].
  (* ---- 5. the run ---- *)
  exists P1, Θ1. split.
  { (* [a_sub__forall_l] is EXISTS-FRESH (campaign cluster 5): P6-L's ONE
       instance IS the premise now, no family to rebuild. *)
    eapply a_sub__forall_l with (α := α) (Ξ := Ξ) (P1 := Pa);
      [ exact HMti | exact HP0wlog
      | clear - Fr; fsetdec
      | exact Hlook
      | apply a_wf_aenv_uniq; exact HwfΞΘ0
      | exact HwfPa
      | exact Hrun ]. }
  (* ---- 6. the package ---- *)
  intros κf Hidf Hincf.
  destruct (a_sub_sound_thm Hrun HwfΞΘ0 HwfP0' HwfPnew HmodSK HmodTY)
    as [[[w [Hidw Hincw]] Hdefs] [HwfΘ1 _]].
  destruct (Hopt w Hidw Hincw) as [ζ' [Hζ' [Hie' Hprec']]].
  exists ζ'. split; [ exact Hζ' | ]. split.
  { (* peel the Ξ-flex block; identify the tails by length *)
    destruct (@a_inc_peel_suffix Ξ Θ0 w Θ1
                (a_decls_suffix HdeclsΞ) Hincw)
      as [wa [wb [-> [Hdomwa Hincwb]]]].
    assert (Hidwb : is_id_msubst wb).
    { unfold is_id_msubst in *. apply Forall_app in Hidw. tauto. }
    assert (Heqwb : wb = κf)
      by (eapply is_id_inc_unique;
          [ exact Hincwb | exact Hidwb | exact Hincf | exact Hidf ]).
    subst wb.
    assert (Hcompw : msubst_compose ζ' (wa ++ κf)
                   = msubst_compose ζ' wa ++ msubst_compose ζ' κf)
      by (unfold msubst_compose; apply List.map_app).
    rewrite Hcompw in Hie'.
    assert (Hinccomp : (msubst_compose ζ' wa ++ msubst_compose ζ' κf)
                         ∷ (Ξ ++ Θ0) ⊑ Θ).
    { rewrite <- Hcompw.
      eapply a_inc_compose;
        [ exact Hincw | exact HwfΞΘ0 | exact HwfΘ1 | exact Hζ' ]. }
    destruct (@a_inc_equiv_inc_peel_suffix Ξ Θ0 (κa ++ κ)
                (msubst_compose ζ' wa ++ msubst_compose ζ' κf) Θ
                (a_decls_suffix HdeclsΞ) Hie' Hinca Hinccomp)
      as [κ1b [κ2b [Hie2 [Hib1 [Hib2 [[p1 [Hp1 Hd1]] [p2 [Hp2 Hd2]]]]]]]].
    assert (Hlen1 : length κ = length κ1b)
      by (symmetry; eapply a_inc_same_length; [ exact Hib1 | exact Hinc ]).
    destruct (app_inj_tail_length κa κ p1 κ1b Hp1 Hlen1) as [_ Heqκ1b].
    subst κ1b.
    assert (Hlen2 : length (msubst_compose ζ' κf) = length κ2b).
    { assert (Hl2a : length κ2b = length κ)
        by (eapply a_inc_same_length; [ exact Hib2 | exact Hinc ]).
      assert (Hl2b : length κf = length κ)
        by (eapply a_inc_same_length; [ exact Hincf | exact Hinc ]).
      unfold msubst_compose. rewrite List.map_length.
      clear - Hl2a Hl2b; lia. }
    destruct (app_inj_tail_length (msubst_compose ζ' wa)
                (msubst_compose ζ' κf) p2 κ2b Hp2 Hlen2) as [_ Heqκ2b].
    subst κ2b.
    exact Hie2. }
  { exact Hprec'. }
Qed.

Print Assumptions a_sub_complete_forall_l_untagged.


(* ===================================================================== *)
(*  P7a — THE FLEXIBLE WALK.  Infrastructure, and the rows that stay      *)
(*  INSIDE the walk (Flex-Depend, Flex-Skip).                             *)
(*                                                                        *)
(*  The discharge pattern for a RE-ATTACHING row (the walk's Barendregt   *)
(*  output premise [β ∉ dom Θ1], algo/def_extra.v:1100/:1116/:1123) is:   *)
(*                                                                        *)
(*    (i)   PEEL the given [κ ∷ (Ξ ++ (β ~ ·) ++ Θ0) ⊑ Θ] around the mid  *)
(*          β entry ([a_inc_strip_flex_mid]) — for a FLEXIBLE entry the   *)
(*          TARGET is unchanged, which is what makes the row work;        *)
(*    (ii)  feed the IH at the stripped context;                          *)
(*    (iii) pick β1 fresh for everything in hand;                         *)
(*    (iv)  junk-swap the IH's run ([a_sub_flex_swap_junk], prop_swap.v   *)
(*          §13) and re-attach via [swap_junk_dom_out];                   *)
(*    (v)   rebuild the package as [(β, κ's β-image) :: kswap_msubst β β1 *)
(*          ζ], using [a_inc_kswap] for the increase,                     *)
(*          [msubst_compose_kswap_id] + [msubst_compose_head_id] for the  *)
(*          equivalence, and [msubst_bskl_head_notin] +                   *)
(*          [msubst_bskl_kswap_paint] for the precision.                  *)
(*                                                                        *)
(*  ⚠️ [Flex-SkipRigid] is NOT this pattern — see the RESTART NOTE at the  *)
(*  end of this section.                                                  *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  (A)  The flexible walk's SOUNDNESS corollary                          *)
(* ===================================================================== *)

Lemma a_sub_flex_sound_thm : forall NM M P0 Θ0 Ξ α A Θ1,
  a_sub_flex NM M P0 Θ0 Ξ α A Θ1 ->
  a_decls Ξ ->
  a_wf_aenv (Ξ ++ Θ0) ->
  (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P0 ->
  a_binds_tvar α (Ξ ++ Θ0) ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat (mode_fn M) P0) ->
  (NM = a_sub_mode_ty -> a_ty_mode_compat (mode_fn M) P0) ->
  (Ξ ++ Θ0) ⊴ Θ1 /\ a_wf_aenv Θ1.
Proof.
  intros NM M P0 Θ0 Ξ α A Θ1 Hrun Hdecls Hwf HwfP0 Hαb Hmod Hgf.
  assert (Htag : a_subtag_flex NM M P0 Θ0 Ξ α A Θ1).
  { eapply (proj2 a_sub_decorate_bundle);
      [ exact Hrun | exact Hdecls | exact Hwf | exact HwfP0 | exact Hαb
      | intros HSK; apply a_sk_mode_compat_mod_comp_sk; apply Hmod; exact HSK
      | intros _; eapply a_wf_pskl_top_guarded; exact HwfP0 ]. }
  destruct ((proj2 a_subtag_sound_bundle) _ _ _ _ _ _ _ _ Htag
              Hwf Hdecls HwfP0 Hαb
              ltac:(intros HSK; apply a_sk_mode_compat_mod_comp_sk;
                    apply Hmod; exact HSK)
              Hgf)
    as [Hisub [HwfΘ1 _]].
  split; assumption.
Qed.

(* ===================================================================== *)
(*  (B)  PROVENANCE — a target entry is either flexible or comes from     *)
(*       the source by name.                                              *)
(* ===================================================================== *)

Lemma a_suffix_binds : forall Ξ γ bd,
  a_suffix Ξ -> binds γ bd Ξ -> a_suffix_binding bd.
Proof.
  intros Ξ γ bd H; induction H; intros Hb; [ inversion Hb | ].
  analyze_binds Hb; auto.
Qed.

Lemma a_inc_binds_provenance : forall Θs κ Θt γ bd,
  κ ∷ Θs ⊑ Θt ->
  binds γ bd Θt ->
  a_suffix_binding bd \/ γ `in` dom Θs.
Proof.
  intros Θs κ Θt γ bd H; induction H; intros Hb.
  - left; eapply a_suffix_binds; eassumption.
  - destruct (IHa_inc Hb) as [h | h];
      [ left; exact h | right; simpl_env; clear - h; fsetdec ].
  - destruct (IHa_inc Hb) as [h | h];
      [ left; exact h | right; simpl_env; clear - h; fsetdec ].
  - analyze_binds Hb;
      [ left; eapply a_suffix_binds; eassumption
      | right; simpl_env; clear; fsetdec
      | destruct (IHa_inc BindsTac0) as [h | h];
          [ left; exact h | right; simpl_env; clear - h; fsetdec ] ].
  - analyze_binds Hb;
      [ left; eapply a_suffix_binds; eassumption
      | right; simpl_env; clear; fsetdec
      | destruct (IHa_inc BindsTac0) as [h | h];
          [ left; exact h | right; simpl_env; clear - h; fsetdec ] ].
  - analyze_binds Hb;
      [ left; eapply a_suffix_binds; eassumption
      | right; simpl_env; clear; fsetdec
      | destruct (IHa_inc BindsTac0) as [h | h];
          [ left; exact h | right; simpl_env; clear - h; fsetdec ] ].
Qed.

(** The shape [a_inc_kswap] wants, for a name the walk stripped from the
    source: every binding it has in the run's OUTPUT is flexible. *)
Lemma a_sub_flex_out_flex_only : forall NM M P0 Θ0 Ξ α A Θ1 β,
  a_sub_flex NM M P0 Θ0 Ξ α A Θ1 ->
  a_decls Ξ ->
  a_wf_aenv (Ξ ++ Θ0) ->
  (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P0 ->
  a_binds_tvar α (Ξ ++ Θ0) ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat (mode_fn M) P0) ->
  (NM = a_sub_mode_ty -> a_ty_mode_compat (mode_fn M) P0) ->
  β `notin` dom (Ξ ++ Θ0) ->
  forall bd, binds β bd Θ1 ->
    bd = abind_flex_mono \/ exists τ, bd = abind_flex_mono_def τ.
Proof.
  intros * Hrun Hdecls Hwf HwfP0 Hαb Hmod Hgf Hβ bd Hb.
  destruct (a_sub_flex_sound_thm Hrun Hdecls Hwf HwfP0 Hαb Hmod Hgf)
    as [[[w [Hidw Hincw]] _] _].
  assert (Hprov : a_suffix_binding bd \/ β `in` dom (Ξ ++ Θ0))
    by (eapply a_inc_binds_provenance; eassumption).
  destruct Hprov as [h | h];
    [ inversion h; subst; [ left; reflexivity | right; eexists; reflexivity ]
    | exfalso; clear - h Hβ; fsetdec ].
Qed.

(* ===================================================================== *)
(*  (C)  Stripping a MID flexible entry from an [a_inc] source            *)
(* ===================================================================== *)

Lemma msubst_lookup_mid_ne : forall κ1 β τ κ2 γ,
  γ <> β ->
  msubst_lookup (κ1 ++ (β, τ) :: κ2) γ = msubst_lookup (κ1 ++ κ2) γ.
Proof.
  intros κ1; induction κ1 as [| [x τx] κ1']; intros β τ κ2 γ Hne; simpl.
  - destruct (γ == β) as [e | _]; [ exfalso; auto | reflexivity ].
  - destruct (γ == x) as [_ | _]; [ reflexivity | apply IHκ1'; exact Hne ].
Qed.

(** The prefix must be [a_decls] (DECLARATIONS only), not [a_suffix]: a
    DEFINED flexible in the prefix carries a payload that may mention the
    stripped [β], and its [a_inc__flex_def] equivalence premise then does not
    survive the strip.  The motive's Ξ is [a_decls] for exactly this reason. *)
Lemma a_inc_strip_flex_mid : forall Ξ β Θ0 κ Θ,
  a_decls Ξ ->
  κ ∷ (Ξ ++ (β ~ abind_flex_mono) ++ Θ0) ⊑ Θ ->
  exists κ1 τ κ2,
    κ = κ1 ++ (β, τ) :: κ2 /\ length κ1 = length Ξ /\ dom κ1 [=] dom Ξ /\
    (κ1 ++ κ2) ∷ (Ξ ++ Θ0) ⊑ Θ /\ a_wf_ptyp Θ τ /\ mono_ptyp τ /\
    κ2 ∷ Θ0 ⊑ Θ.
Proof.
  intros Ξ; induction Ξ as [| [x b] Ξ' IH]; intros β Θ0 κ Θ Hsuf Hinc.
  - simpl in Hinc.
    inversion Hinc as [ | Θa κa Θb αa τa Hi Hw Hm | | | | ]; subst.
    exists nil, τa, κa. simpl.
    split; [ reflexivity | split; [ reflexivity | ] ].
    split; [ clear; fsetdec | ].
    split; [ exact Hi | ]. split; [ assumption | ]. split; assumption.
  - inversion Hsuf as [ | ? ? Hsuf' ]; subst; simpl in Hinc.
    inversion Hinc as [ | Θa κa Θb αa τa Hi Hw Hm | | | | ]; subst.
    destruct (IH _ _ _ _ Hsuf' Hi)
      as [κ1 [τ [κ2 [-> [Hd [Hdom [Hinc2 [Hwτ [Hmτ Hi2]]]]]]]]].
    exists ((x, τa) :: κ1), τ, κ2. simpl.
    split; [ reflexivity | ].
    split; [ rewrite Hd; reflexivity | ].
    split; [ rewrite Hdom; clear; fsetdec | ].
    split; [ apply a_inc__flex; [ exact Hinc2 | exact Hw | exact Hm ] | ].
    split; [ assumption | ]. split; assumption.
Qed.

Lemma a_inc_strip_flex_def_mid : forall Ξ β τ0 Θ0 κ Θ,
  a_decls Ξ ->
  κ ∷ (Ξ ++ (β ~ abind_flex_mono_def τ0) ++ Θ0) ⊑ Θ ->
  exists κ1 τ κ2,
    κ = κ1 ++ (β, τ) :: κ2 /\ length κ1 = length Ξ /\ dom κ1 [=] dom Ξ /\
    (κ1 ++ κ2) ∷ (Ξ ++ Θ0) ⊑ Θ /\
    Θ ⊢ τ ≡ᵗ (msubst_ptyp κ2 τ0) /\ a_wf_ptyp Θ τ /\ mono_ptyp τ /\
    κ2 ∷ Θ0 ⊑ Θ.
Proof.
  intros Ξ; induction Ξ as [| [x b] Ξ' IH]; intros β τ0 Θ0 κ Θ Hsuf Hinc.
  - simpl in Hinc.
    inversion Hinc as [ | | Θa κa Θb αa τa τb Hi Hw Hm He | | | ]; subst.
    exists nil, τb, κa. simpl.
    split; [ reflexivity | split; [ reflexivity | ] ].
    split; [ clear; fsetdec | ].
    split; [ exact Hi | ]. split; [ exact He | ].
    split; [ assumption | ]. split; assumption.
  - inversion Hsuf as [ | ? ? Hsuf' ]; subst; simpl in Hinc.
    inversion Hinc as [ | Θa κa Θb αa τa Hi Hw Hm | | | | ]; subst.
    destruct (IH _ _ _ _ _ Hsuf' Hi)
      as [κ1 [τ [κ2 [-> [Hd [Hdom [Hinc2 [Heq [Hwτ [Hmτ Hi2]]]]]]]]]].
    exists ((x, τa) :: κ1), τ, κ2. simpl.
    split; [ reflexivity | ].
    split; [ rewrite Hd; reflexivity | ].
    split; [ rewrite Hdom; clear; fsetdec | ].
    split; [ apply a_inc__flex; [ exact Hinc2 | exact Hw | exact Hm ] | ].
    split; [ exact Heq | ]. split; [ assumption | ]. split; assumption.
Qed.

(** The [a_inc_equiv] counterpart of the strip: INSERTING a flexible entry
    in the middle, with the SAME image on both sides. *)
Lemma a_inc_equiv_insert_flex_mid : forall Ξ κ1 κ2 σ1 σ2 β τ Θ0 Θ,
  a_decls Ξ ->
  length κ1 = length Ξ ->
  a_inc_equiv (Ξ ++ Θ0) (κ1 ++ κ2) (σ1 ++ σ2) Θ ->
  length σ1 = length Ξ ->
  Θ ⊢ τ ≡ᵗ τ ->
  a_inc_equiv (Ξ ++ (β ~ abind_flex_mono) ++ Θ0)
              (κ1 ++ (β, τ) :: κ2) (σ1 ++ (β, τ) :: σ2) Θ.
Proof.
  intros Ξ; induction Ξ as [| [x b] Ξ' IH];
    intros κ1 κ2 σ1 σ2 β τ Θ0 Θ Hd Hlk He Hls Hτ.
  - destruct κ1; [ | discriminate ]. destruct σ1; [ | discriminate ].
    simpl in *. apply a_inc_equiv__flex; [ exact He | exact Hτ ].
  - inversion Hd as [ | ? ? Hd' ]; subst.
    destruct κ1 as [| [k1a k1b] κ1']; [ discriminate | ].
    destruct σ1 as [| [s1a s1b] σ1']; [ discriminate | ].
    simpl in He.
    inversion He as [ | Θa κa σa Θb αa τ1 τ2 Hie Heq | | | | ]; subst.
    simpl. apply a_inc_equiv__flex; [ | exact Heq ].
    apply IH; [ exact Hd' | simpl in Hlk; lia | exact Hie
              | simpl in Hls; lia | exact Hτ ].
Qed.

(* ===================================================================== *)
(*  (D)  The JOIN's target is scoped — [ad_pat_consis_target_wf]'s        *)
(*       subtyping-level twin.                                            *)
(* ===================================================================== *)

Lemma ad_pat_sub_target_wf : forall NM M Ψ Θ R Qt,
  Ψ ⨟ Θ ⊢ₛᵃ[ NM | M ] R ⩽ Qt ->
  a_scope_pskl Θ (bskl_to_pskl Qt).
Proof.
  intros NM M Ψ Θ R Qt H; induction H.
  - (* infer *) eapply ad_pat_consis_target_wf; eassumption.
  - (* check *)
    assert (Hc : a_scope_pskl Θ (bskl_to_pskl (pskl_to_bskl_inh B)))
      by (eapply ad_pat_consis_target_wf; eassumption).
    exact Hc.
  - (* forall_r *)
    simpl. apply a_scope_pskl__all with (L := L).
    intros α Hα. rewrite <- bskl_to_pskl_open. apply H0; exact Hα.
  - (* univ_ghost_r *)
    simpl. apply a_scope_pskl__tophole.
    eapply ad_pat_consis_target_wf; eassumption.
  - (* arrow *)
    simpl. apply a_scope_pskl__arrow;
      [ eapply ad_pat_consis_target_wf; eassumption | exact IHad_pat_sub ].
  - (* forall_l_tagged *) exact IHad_pat_sub.
  - (* forall_l_untagged *) exact IHad_pat_sub.
  - (* ghost *)
    rewrite bskl_to_pskl_pskl_to_bskl_inh.
    eapply a_wf_pskl_to_a_scope_pskl;
      [ eassumption | intros x b Hb; exact Hb | intros α Hα; clear - Hα; fsetdec ].
  - (* ghostg *) simpl. apply a_scope_pskl__hole.
  - (* univ_ghost_l *) exact IHad_pat_sub.
  - (* univ_ghost_lg *) exact IHad_pat_sub.
  - (* flex_mono *) exact IHad_pat_sub.
Qed.

(** The flexible walk's OUTPUT skeleton is scoped in the output context. *)
Lemma a_sub_flex_out_scope : forall NM M P0 Θ0 Ξ α A Θ1,
  a_sub_flex NM M P0 Θ0 Ξ α A Θ1 ->
  a_decls Ξ ->
  a_wf_aenv (Ξ ++ Θ0) ->
  (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P0 ->
  a_binds_tvar α (Ξ ++ Θ0) ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat (mode_fn M) P0) ->
  (NM = a_sub_mode_ty -> a_ty_mode_compat (mode_fn M) P0) ->
  a_scope_pskl Θ1 A.
Proof.
  intros NM M P0 Θ0 Ξ α A Θ1 Hrun Hdecls Hwf HwfP0 Hαb Hmod Hgf.
  assert (Htag : a_subtag_flex NM M P0 Θ0 Ξ α A Θ1).
  { eapply (proj2 a_sub_decorate_bundle);
      [ exact Hrun | exact Hdecls | exact Hwf | exact HwfP0 | exact Hαb
      | intros HSK; apply a_sk_mode_compat_mod_comp_sk; apply Hmod; exact HSK
      | intros _; eapply a_wf_pskl_top_guarded; exact HwfP0 ]. }
  destruct ((proj2 a_subtag_sound_bundle) _ _ _ _ _ _ _ _ Htag
              Hwf Hdecls HwfP0 Hαb
              ltac:(intros HSK; apply a_sk_mode_compat_mod_comp_sk;
                    apply Hmod; exact HSK)
              Hgf)
    as [_ [_ [Qt [HeqQt [[njoin Hjoin] _]]]]].
  apply ad_pat_sub_of_gv in Hjoin.
  rewrite <- HeqQt. eapply ad_pat_sub_target_wf; exact Hjoin.
Qed.

(* ===================================================================== *)
(*  (E)  A well-formed context mentions only its own domain               *)
(* ===================================================================== *)

Lemma a_scope_pskl_ftv_dom : forall Θ P,
  a_scope_pskl Θ P -> ftvar_in_pskl P [<=] dom Θ.
Proof.
  intros Θ P H α Hα.
  assert (Hb : a_binds_tvar α Θ) by (eapply a_scope_pskl_ftv_binds; eassumption).
  destruct Hb as [Hb | [Hb | [τ Hb]]]; eapply binds_In; exact Hb.
Qed.

Lemma a_wf_aenv_ftvar_dom : forall Θ,
  a_wf_aenv Θ -> ftvar_in_aenv Θ [<=] dom Θ.
Proof.
  intros Θ H; induction H; simpl.
  - clear; fsetdec.
  - clear - IHa_wf_aenv; fsetdec.
  - pose proof (a_wf_ptyp_ftv_dom H0); clear - IHa_wf_aenv H3; fsetdec.
  - pose proof (a_scope_pskl_ftv_dom H0); clear - IHa_wf_aenv H2; fsetdec.
  - pose proof (a_wf_ptyp_ftv_dom H0); clear - IHa_wf_aenv H2; fsetdec.
  - clear - IHa_wf_aenv; fsetdec.
Qed.

Lemma a_decls_no_ftvar : forall Ξ,
  a_decls Ξ -> ftvar_in_aenv Ξ [<=] dom Ξ.
Proof.
  intros Ξ H; induction H as [| α1 Ξ' Hd IH]; simpl;
    [ clear; fsetdec | clear - IH; fsetdec ].
Qed.

(* ===================================================================== *)
(*  (F)  P7a ROW — Flex-Depend                                            *)
(* ===================================================================== *)

Lemma a_flex_tvar_strip_mid : forall α β b Ξ Θ0,
  a_flex_tvar (Ξ ++ (β ~ b) ++ Θ0) α -> α <> β -> a_flex_tvar (Ξ ++ Θ0) α.
Proof.
  intros * Hf Hne; destruct Hf as [Hb | [τ Hb]];
    [ left | right; exists τ ]; eapply binds_strip_mid;
    solve [ eassumption | intro Hc; inversion Hc; subst; exact (Hne eq_refl) ].
Qed.

(** …and the converse move the motive's [a_flex_tvar Θ0 α] premise needs when
    a row wants the subject flexible in the FULL split context. *)
Lemma a_flex_tvar_app_weaken : forall Ξ Θ0 α,
  a_flex_tvar Θ0 α -> a_flex_tvar (Ξ ++ Θ0) α.
Proof.
  intros Ξ Θ0 α Hf; destruct Hf as [Hb | [τ Hb]];
    [ left | right; exists τ ]; apply binds_app_3; exact Hb.
Qed.

Lemma a_sub_flex_complete_depend : forall n NM M Θ0 Ξ α β P0 R' Ψ Θ κ Q,
  (* ⭐ THE IH IS LENGTH-GUARDED (P7c, 2026-08-03).  The dispatcher proves the
     flex half by a STRUCTURAL induction on [Θ0] with [Ξ] generalized and the
     TOTAL context length bounded (DESIGN §12.1's layer (b)); its IH is
     therefore available only at suffixes the walk can actually reach, and
     [Flex-Depend] reaches exactly one — [Ξ,β̂].  An unguarded [forall Ξ'] is
     not derivable there, and this row needs no more. *)
  (forall Ξ' α' P0' R'' Ψ' Θ'' κ' Q',
     length Ξ' <= S (length Ξ) ->
     sub_flex_complete_concl n NM M Θ0 Ξ' α' P0' R'' Ψ' Θ'' κ' Q') ->
  α <> β ->
  β `in` ftvar_in_pskl P0 ->
  sub_flex_complete_concl n NM M ((β ~ abind_flex_mono) ++ Θ0) Ξ α P0
    R' Ψ Θ κ Q.
Proof.
  intros n NM M Θ0 Ξ α β P0 R' Ψ Θ κ Q IH Hne Hin.
  unfold sub_flex_complete_concl in *.
  intros HdeclsΞ HdomΞ Hwf Hwfth HwfP0 Hfα HmodSK HmodTY Hinc Hslack HD Hrs
         HwfQ.
  assert (Hdecls' : a_decls (Ξ ++ (β ~ abind_flex_mono)))
    by (apply a_decls_app;
        [ exact HdeclsΞ | apply (a_decls__cons β); apply a_decls__nil ]).
  (* the invariant is exactly what this row RE-ESTABLISHES: β joins Ξ, and
     the rule's own premise says β is a P0-dependency *)
  assert (Hdom' : dom (Ξ ++ (β ~ abind_flex_mono)) [<=] ftvar_in_pskl P0)
    by (simpl_env; clear - HdomΞ Hin; fsetdec).
  simpl_env in Hdom'.
  (* the subject survives the head strip: the rule's own [α <> β] *)
  assert (Hfα' : a_flex_tvar Θ0 α).
  { destruct Hfα as [Hb | [τ0 Hb]]; [ left | right; exists τ0 ];
      (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He _] | Hb'];
       [ exfalso; apply Hne; exact He | exact Hb' ]). }
  assert (Hlen : length (Ξ ++ (β ~ abind_flex_mono)) <= S (length Ξ))
    by (rewrite app_length; simpl; lia).
  specialize (IH (Ξ ++ (β ~ abind_flex_mono)) α P0 R' Ψ Θ κ Q Hlen).
  unfold sub_flex_complete_concl in IH.
  simpl_env in IH.
  destruct (IH Hdecls' Hdom' Hwf Hwfth HwfP0 Hfα' HmodSK HmodTY Hinc Hslack HD
              Hrs HwfQ)
    as [P1 [Θ1 [Hrun Hopt]]].
  exists P1, Θ1. split.
  - apply a_sub_flex__depend; [ exact Hne | exact Hin | exact Hrun ].
  - intros κf Hidf Hincf.
    destruct (Hopt κf Hidf Hincf) as [ζ [Hζ [Hie Hprec]]].
    exists ζ. split; [ exact Hζ | split; [ exact Hie | exact Hprec ] ].
Qed.

(* ===================================================================== *)
(*  (G)  P7a ROW — Flex-Skip                                              *)
(* ===================================================================== *)

Lemma msubst_compose_head_id : forall β τ ζ κ1,
  is_id_msubst κ1 ->
  (forall γ, List.In γ (List.map fst κ1) -> γ <> β) ->
  msubst_compose ((β, τ) :: ζ) κ1 = msubst_compose ζ κ1.
Proof.
  intros β τ ζ κ1; induction κ1 as [| [γ τγ] κ1']; intros Hid Hk;
    [ reflexivity | ].
  inversion Hid as [| e κl he hl]; subst.
  unfold is_id_entry in he; simpl in he. subst τγ.
  unfold msubst_compose; simpl.
  assert (hne : γ <> β) by (apply Hk; left; reflexivity).
  destruct (γ == β) as [e | _]; [ exfalso; auto | ].
  f_equal. apply IHκ1'; [ exact hl | intros γ0 h0; apply Hk; right; exact h0 ].
Qed.

Lemma a_sub_flex_complete_skip : forall n NM M Θ0 Ξ α β P0 R' Ψ Θ κ Q,
  (* length-guarded, as in [a_sub_flex_complete_depend] *)
  (forall Ξ' α' P0' R'' Ψ' Θ'' κ' Q',
     length Ξ' <= S (length Ξ) ->
     sub_flex_complete_concl n NM M Θ0 Ξ' α' P0' R'' Ψ' Θ'' κ' Q') ->
  α <> β ->
  β `notin` ftvar_in_pskl P0 ->
  sub_flex_complete_concl n NM M ((β ~ abind_flex_mono) ++ Θ0) Ξ α P0
    R' Ψ Θ κ Q.
Proof.
  intros n NM M Θ0 Ξ α β P0 R' Ψ Θ κ Q IH Hne Hnin.
  unfold sub_flex_complete_concl in *.
  intros HdeclsΞ HdomΞ Hwf Hwfth HwfP0 Hfα HmodSK HmodTY Hinc Hslack HD Hrs
         HwfQ.
  (* ---- 0. the stripped context, and β's absence from it ---- *)
  assert (Huq : uniq (Ξ ++ (β ~ abind_flex_mono) ++ Θ0))
    by (apply a_wf_aenv_uniq; exact Hwf).
  assert (HβΞΘ0 : β `notin` dom (Ξ ++ Θ0)).
  { clear - Huq. simpl_env in Huq. destruct_uniq.
    unfold disjoint in *. simpl_env in *. fsetdec. }
  assert (Hwf' : a_wf_aenv (Ξ ++ Θ0))
    by (eapply a_wf_aenv_strip_mid; [ exact HdeclsΞ | exact Hwf ]).
  assert (HwfP0' : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P0)
    by (eapply a_wf_pskl_strip_mid; [ exact HwfP0 | exact Hnin ]).
  assert (Hfα' : a_flex_tvar Θ0 α).
  { destruct Hfα as [Hb | [τ0 Hb]]; [ left | right; exists τ0 ];
      (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He _] | Hb'];
       [ exfalso; apply Hne; exact He | exact Hb' ]). }
  assert (Hαb' : a_binds_tvar α (Ξ ++ Θ0))
    by (destruct (a_flex_tvar_app_weaken Ξ Hfα') as [h | [τ h]];
        [ right; left; exact h | right; right; exists τ; exact h ]).
  (* ---- 1. strip the mid entry out of κ ---- *)
  destruct (@a_inc_strip_flex_mid Ξ β Θ0 κ Θ HdeclsΞ Hinc)
    as [κ1 [τβ [κ2 [Heqκ [Hlen [Hdomκ1 [Hincih [Hwfτβ [Hmonoτβ _]]]]]]]]].
  assert (Hlk : forall γ, γ <> β ->
            msubst_lookup κ γ = msubst_lookup (κ1 ++ κ2) γ)
    by (intros γ Hγ; rewrite Heqκ; apply msubst_lookup_mid_ne; exact Hγ).
  assert (HeqP0 : msubst_pskl κ P0 = msubst_pskl (κ1 ++ κ2) P0).
  { apply msubst_pskl_agree. intros γ Hγ. apply Hlk.
    intro Hc; subst γ; contradiction. }
  assert (Heqα : msubst_lookup κ α = msubst_lookup (κ1 ++ κ2) α)
    by (apply Hlk; exact Hne).
  rewrite Heqα in Hslack. rewrite HeqP0 in Hrs.
  (* ---- 2. the IH at the stripped context ---- *)
  destruct (IH Ξ α P0 R' Ψ Θ (κ1 ++ κ2) Q ltac:(lia)
              HdeclsΞ HdomΞ Hwf' Hwfth HwfP0'
              Hfα' HmodSK HmodTY Hincih Hslack HD Hrs HwfQ)
    as [P1 [Θ1 [Hrun Hopt]]].
  destruct (a_sub_flex_sound_thm Hrun HdeclsΞ Hwf' HwfP0' Hαb' HmodSK HmodTY)
    as [[[w [Hidw Hincw]] Hdefs] HwfΘ1].
  assert (HscP1 : a_scope_pskl Θ1 P1)
    by (eapply a_sub_flex_out_scope;
        [ exact Hrun | exact HdeclsΞ | exact Hwf' | exact HwfP0'
        | exact Hαb' | exact HmodSK | exact HmodTY ]).
  assert (HβflexΘ1 : forall bd, binds β bd Θ1 ->
            bd = abind_flex_mono \/ exists τ, bd = abind_flex_mono_def τ)
    by (eapply a_sub_flex_out_flex_only;
        [ exact Hrun | exact HdeclsΞ | exact Hwf' | exact HwfP0'
        | exact Hαb' | exact HmodSK | exact HmodTY | exact HβΞΘ0 ]).
  (* ---- 3. the junk rename ---- *)
  assert (HβΞ : β `notin` ftvar_in_aenv Ξ).
  { pose proof (a_decls_no_ftvar HdeclsΞ) as h.
    clear - h HβΞΘ0. simpl_env in HβΞΘ0. fsetdec. }
  assert (HwfΘ0 : a_wf_aenv Θ0) by (eapply a_wf_aenv_app_r; exact Hwf').
  assert (HβΘ0 : β `notin` ftvar_in_aenv Θ0).
  { pose proof (a_wf_aenv_ftvar_dom HwfΘ0) as h.
    clear - h HβΞΘ0. simpl_env in HβΞΘ0. fsetdec. }
  destruct (atom_fresh (dom Θ1 `union` ftvar_in_aenv Θ1
                        `union` ftvar_in_pskl P1 `union` dom Ξ
                        `union` dom Θ0 `union` ftvar_in_aenv Θ0
                        `union` ftvar_in_aenv Ξ `union` ftvar_in_pskl P0
                        `union` singleton α `union` singleton β))
    as [β1 Fr].
  assert (Hrunsw : a_sub_flex NM M P0 Θ0 Ξ α
                     (swap_pskl β β1 P1) (swap_aenv β β1 Θ1)).
  { apply (a_sub_flex_swap_junk β β1 NM M P0 Θ0 Ξ α P1 Θ1 Hrun);
      [ intro Hc; subst; exact (Hne eq_refl)
      | clear - Fr; fsetdec
      | clear - HβΘ0 HβΞ Hnin; fsetdec
      | clear - Fr; fsetdec ]. }
  exists (swap_pskl β β1 P1), ((β ~ abind_flex_mono) ++ swap_aenv β β1 Θ1).
  split.
  { apply a_sub_flex__skip;
      [ exact Hne | exact Hnin
      | apply swap_junk_dom_out; clear - Fr; fsetdec
      | exact Hrunsw ]. }
  (* ---- 4. the package ---- *)
  intros κf Hidf Hincf.
  destruct (@a_inc_strip_flex_mid Ξ β Θ0 κf
              ((β ~ abind_flex_mono) ++ swap_aenv β β1 Θ1) HdeclsΞ Hincf)
    as [κf1 [τf [κf2 [Heqκf [Hlenf [_ [Hincfih [_ [_ _]]]]]]]]].
  assert (Hidfih : is_id_msubst (κf1 ++ κf2)).
  { unfold is_id_msubst in *. rewrite Heqκf in Hidf.
    apply Forall_app in Hidf. destruct Hidf as [h1 h2].
    inversion h2; subst. apply Forall_app; split; assumption. }
  assert (Heqτf : τf = ptyp_var_f β).
  { unfold is_id_msubst in Hidf. rewrite Heqκf in Hidf.
    apply Forall_app in Hidf. destruct Hidf as [_ h2].
    inversion h2 as [| e κl he hl]; subst.
    unfold is_id_entry in he; simpl in he. exact he. }
  assert (Heqw : w = κf1 ++ κf2)
    by (eapply is_id_inc_unique;
        [ exact Hincw | exact Hidw | exact Hincfih | exact Hidfih ]).
  subst w.
  destruct (Hopt (κf1 ++ κf2) Hidfih Hincw) as [ζ [Hζ [Hie Hprec]]].
  (* the keys of ζ and of the identity live in known domains *)
  assert (Hkeysζ : forall γ, List.In γ (List.map fst ζ) -> γ `in` dom Θ1)
    by (intros γ hγ; eapply a_inc_keys_dom; [ exact Hζ | exact hγ ]).
  assert (Hkeysf : forall γ, List.In γ (List.map fst (κf1 ++ κf2)) ->
            γ `in` dom (Ξ ++ Θ0))
    by (intros γ hγ; eapply a_inc_keys_dom; [ exact Hincfih | exact hγ ]).
  exists ((β, τβ) :: kswap_msubst β β1 ζ).
  split.
  { (* the increase *)
    apply a_inc__flex; [ | exact Hwfτβ | exact Hmonoτβ ].
    apply (a_inc_kswap β β1 ζ Θ1 Θ Hζ);
      [ clear - Fr; fsetdec | exact HwfΘ1 | clear - Fr; fsetdec
      | exact HβflexΘ1 ]. }
  split.
  { (* the equivalence *)
    rewrite Heqκ, Heqκf, Heqτf.
    assert (Hsplit : msubst_compose ((β, τβ) :: kswap_msubst β β1 ζ)
                       (κf1 ++ (β, ptyp_var_f β) :: κf2)
                   = msubst_compose ((β, τβ) :: kswap_msubst β β1 ζ) κf1
                     ++ (β, τβ)
                     :: msubst_compose ((β, τβ) :: kswap_msubst β β1 ζ) κf2).
    { unfold msubst_compose. rewrite List.map_app. simpl.
      destruct (β == β) as [_ | n0]; [ reflexivity | exfalso; auto ]. }
    rewrite Hsplit.
    assert (Hid1 : is_id_msubst κf1 /\ is_id_msubst κf2).
    { unfold is_id_msubst in Hidfih. apply Forall_app in Hidfih. exact Hidfih. }
    destruct Hid1 as [Hidf1 Hidf2].
    assert (Hkey1 : forall γ, List.In γ (List.map fst κf1) ->
              γ <> β /\ γ <> β1).
    { intros γ hγ.
      assert (hd : γ `in` dom (Ξ ++ Θ0))
        by (apply Hkeysf; rewrite List.map_app; apply in_or_app; left; exact hγ).
      split; [ intro Hc; subst; clear - hd HβΞΘ0; fsetdec
             | intro Hc; subst; clear - hd Fr; simpl_env in hd; fsetdec ]. }
    assert (Hkey2 : forall γ, List.In γ (List.map fst κf2) ->
              γ <> β /\ γ <> β1).
    { intros γ hγ.
      assert (hd : γ `in` dom (Ξ ++ Θ0))
        by (apply Hkeysf; rewrite List.map_app; apply in_or_app; right; exact hγ).
      split; [ intro Hc; subst; clear - hd HβΞΘ0; fsetdec
             | intro Hc; subst; clear - hd Fr; simpl_env in hd; fsetdec ]. }
    assert (Hk1b : forall γ, List.In γ (List.map fst κf1) -> γ <> β)
      by (intros γ hγ; exact (proj1 (Hkey1 γ hγ))).
    assert (Hk2b : forall γ, List.In γ (List.map fst κf2) -> γ <> β)
      by (intros γ hγ; exact (proj1 (Hkey2 γ hγ))).
    rewrite (@msubst_compose_head_id β τβ (kswap_msubst β β1 ζ) κf1 Hidf1 Hk1b).
    rewrite (@msubst_compose_head_id β τβ (kswap_msubst β β1 ζ) κf2 Hidf2 Hk2b).
    rewrite (msubst_compose_kswap_id β β1 ζ κf1 Hidf1 Hkey1).
    rewrite (msubst_compose_kswap_id β β1 ζ κf2 Hidf2 Hkey2).
    apply a_inc_equiv_insert_flex_mid;
      [ exact HdeclsΞ | exact Hlen
      | unfold msubst_compose in *; rewrite <- List.map_app; exact Hie
      | unfold msubst_compose; rewrite List.map_length; exact Hlenf
      | apply a_tyequiv__refl; apply mono_ptyp_lc; exact Hmonoτβ ]. }
  { (* the precision *)
    assert (Hnbsw : β `notin` ftvar_in_pskl (swap_pskl β β1 P1)).
    { intro Hc.
      assert (h : β1 `in` ftvar_in_pskl P1).
      { pose proof (swap_pskl_ftv_in_rev β β1 P1 β Hc) as h0.
        rewrite swap_atom_l in h0. exact h0. }
      clear - h Fr. fsetdec. }
    assert (Hhead : msubst_bskl ((β, τβ) :: kswap_msubst β β1 ζ)
                      (pskl_to_bskl_syn (swap_pskl β β1 P1))
                  = msubst_bskl (kswap_msubst β β1 ζ)
                      (pskl_to_bskl_syn (swap_pskl β β1 P1))).
    { apply msubst_bskl_head_notin.
      rewrite ftvar_in_bskl_syn. exact Hnbsw. }
    rewrite Hhead.
    rewrite (msubst_bskl_kswap_paint β β1 ζ P1);
      [ exact Hprec
      | clear - Fr; fsetdec
      | intro hc; pose proof (Hkeysζ β1 hc) as h; clear - h Fr; fsetdec
      | clear - Fr; fsetdec
      | destruct (AtomSetProperties.In_dec β (ftvar_in_pskl P1))
          as [hin | hout]; [ right | left; exact hout ];
        assert (hbt : a_binds_tvar β Θ1)
          by (eapply a_scope_pskl_ftv_binds; [ exact HscP1 | exact hin ]);
        destruct hbt as [hbt | [hbt | [τ0 hbt]]];
        [ exfalso; destruct (HβflexΘ1 abind_tvar hbt) as [hc | [τ1 hc]];
            discriminate
        | eapply a_inc_flex_in_keys; [ exact Hζ | left; exact hbt ]
        | eapply a_inc_flex_in_keys; [ exact Hζ | right; eexists; exact hbt ] ] ]. }
Qed.


(* ===================================================================== *)
(*  (H)  Two enablers the CROSS-HALF rows need                            *)
(* ===================================================================== *)

(** Pushing a MONOTYPE substitution through a metasubstitution: the two
    commute by absorbing the substituted variable into the metasubstitution
    (its image being the metasubstituted monotype).  Pure — no side
    condition, because [msubst_pskl] is defined by lookup. *)
Lemma msubst_pskl_subst_mono : forall ζ β τ P,
  msubst_pskl ζ (subst_pskl_in_pskl (ptyp_to_pskl τ) β P)
  = msubst_pskl ((β, msubst_ptyp ζ τ) :: ζ) P.
Proof.
  intros ζ β τ P; induction P; simpl; try solve [ f_equal; auto ].
  (* var_f *)
  destruct (α == β) as [-> | Hne].
  - rewrite msubst_pskl_ptyp_to_pskl.
    match goal with
    | |- _ = ptyp_to_pskl (if ?t then _ else _) => destruct t as [_ | n0]
    end; [ reflexivity | exfalso; apply n0; reflexivity ].
  - simpl.
    match goal with
    | |- _ = ptyp_to_pskl (if ?t then _ else _) => destruct t as [e | _]
    end; [ exfalso; apply Hne; exact e | reflexivity ].
Qed.

(** …and the ≡ˢ congruence for two metasubstitutions that agree POINTWISE up
    to type equivalence.  The dual of [a_pskl_tyequiv_msubst] (which moves one
    ζ across an equivalence); here the SKELETON is fixed and the two
    metasubstitutions vary. *)
Lemma msubst_pskl_tyequiv_pointwise : forall Θs1 ζ Θ Θs2 σ P,
  ζ ∷ Θs1 ⊑ Θ ->
  σ ∷ Θs2 ⊑ Θ ->
  lc_pskl P ->
  (forall γ, Θ ⊢ (msubst_lookup ζ γ) ≡ᵗ (msubst_lookup σ γ)) ->
  Θ ⊢ (msubst_pskl ζ P) ≡ˢ (msubst_pskl σ P).
Proof.
  intros Θs1 ζ Θ Θs2 σ P Hζ Hσ Hlc; induction Hlc; intros Hag; simpl.
  - (* unit *) apply a_pskl_tyequiv__refl; constructor.
  - (* var_f *) apply a_tyequiv_pskl; apply Hag.
  - (* arrow *) apply a_pskl_tyequiv__arrow; auto.
  - (* all_syn *)
    apply a_pskl_tyequiv__all with (L := dom ζ `union` dom σ).
    intros α Hα.
    assert (Hnζ : α `notin` dom ζ) by (clear - Hα; fsetdec).
    assert (Hnσ : α `notin` dom σ) by (clear - Hα; fsetdec).
    rewrite <- (@msubst_pskl_open Θs1 ζ Θ P1 α Hζ Hnζ).
    rewrite <- (@msubst_pskl_open Θs2 σ Θ P1 α Hσ Hnσ).
    exact (H0 α Hag).
  - (* hole *) apply a_pskl_tyequiv__refl; constructor.
  - (* tophole *) apply a_pskl_tyequiv__tophole; auto.
Qed.


(** The [ptyp] twin of [msubst_pskl_tyequiv_pointwise].  (Named
    [_two_msubst], not [_pointwise]: prop_sub_msubst_equiv.v's
    [msubst_ptyp_tyequiv_pointwise] compares a type with its OWN image under
    one κ; this one compares TWO metasubstitutions' images of one type.) *)
Lemma msubst_ptyp_tyequiv_two_msubst : forall Θs1 ζ Θ Θs2 σ A,
  ζ ∷ Θs1 ⊑ Θ ->
  σ ∷ Θs2 ⊑ Θ ->
  lc_ptyp A ->
  (forall γ, γ `in` ftvar_in_ptyp A ->
     Θ ⊢ (msubst_lookup ζ γ) ≡ᵗ (msubst_lookup σ γ)) ->
  Θ ⊢ (msubst_ptyp ζ A) ≡ᵗ (msubst_ptyp σ A).
Proof.
  intros Θs1 ζ Θ Θs2 σ A Hζ Hσ Hlc; induction Hlc; intros Hag; simpl.
  - apply a_tyequiv__refl; constructor.
  - apply Hag; simpl; clear; fsetdec.
  - apply a_tyequiv__arrow;
      [ apply IHHlc1 | apply IHHlc2 ];
      intros γ Hγ; apply Hag; simpl; clear - Hγ; fsetdec.
  - apply a_tyequiv__all with (L := dom ζ `union` dom σ).
    intros γ Hγ.
    assert (Hnζ : γ `notin` dom ζ) by (clear - Hγ; fsetdec).
    assert (Hnσ : γ `notin` dom σ) by (clear - Hγ; fsetdec).
    rewrite <- (@msubst_ptyp_open Θs1 ζ Θ A γ Hζ Hnζ).
    rewrite <- (@msubst_ptyp_open Θs2 σ Θ A γ Hσ Hnσ).
    apply H0.
    { intros δ Hδ.
      destruct (δ == γ) as [-> | Hne].
      - (* the OPENER: outside both domains, so both lookups are itself *)
        rewrite (msubst_lookup_notin _ Hnζ), (msubst_lookup_notin _ Hnσ).
        apply a_tyequiv__refl; constructor.
      - apply Hag.
        pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper A (ptyp_var_f γ))
          as Hup.
        simpl in Hup. clear - Hδ Hup Hne. fsetdec. }
Qed.

(** [a_inc_equiv_insert_flex_mid]'s DEFINED counterpart. *)
Lemma a_inc_equiv_insert_flex_def_mid :
  forall Ξ κ1 κ2 σ1 σ2 β τ τ0 Θ0 Θ,
  a_decls Ξ ->
  length κ1 = length Ξ ->
  a_inc_equiv (Ξ ++ Θ0) (κ1 ++ κ2) (σ1 ++ σ2) Θ ->
  length σ1 = length Ξ ->
  Θ ⊢ τ ≡ᵗ τ ->
  Θ ⊢ τ ≡ᵗ (msubst_ptyp κ2 τ0) ->
  a_inc_equiv (Ξ ++ (β ~ abind_flex_mono_def τ0) ++ Θ0)
              (κ1 ++ (β, τ) :: κ2) (σ1 ++ (β, τ) :: σ2) Θ.
Proof.
  intros Ξ; induction Ξ as [| [x b] Ξ' IH];
    intros κ1 κ2 σ1 σ2 β τ τ0 Θ0 Θ Hd Hlk He Hls Hτ Hτ0.
  - destruct κ1; [ | discriminate ]. destruct σ1; [ | discriminate ].
    simpl in *. apply a_inc_equiv__flex_def; assumption.
  - inversion Hd as [ | ? ? Hd' ]; subst.
    destruct κ1 as [| [k1a k1b] κ1']; [ discriminate | ].
    destruct σ1 as [| [s1a s1b] σ1']; [ discriminate | ].
    simpl in He.
    inversion He as [ | Θa κa σa Θb αa τ1 τ2 Hie Heq | | | | ]; subst.
    simpl. apply a_inc_equiv__flex; [ | exact Heq ].
    apply IH; [ exact Hd' | simpl in Hlk; lia | exact Hie
              | simpl in Hls; lia | exact Hτ | exact Hτ0 ].
Qed.

(* ===================================================================== *)
(*  (I)  P7a ROW — Flex-Assign  (a CROSS-HALF row: its IH is P7b's)       *)
(* ===================================================================== *)

Lemma a_sk_mode_compat_subst_mono : forall M P τ β,
  a_sk_mode_compat M P -> mono_ptyp τ ->
  a_sk_mode_compat M (subst_pskl_in_pskl (ptyp_to_pskl τ) β P).
Proof.
  intros M P τ β H Hm; induction H; simpl;
    [ apply a_sk_mode_compat__ti | apply a_sk_mode_compat__tc
    | apply a_sk_mode_compat__fn; assumption ].
Qed.

Lemma a_sub_flex_complete_assign :
  forall n NM M Θ0 Ξ α β τ P0 R' Ψ Θ κ Q,
  (* ⭐ THE CROSS-HALF IH IS LENGTH-GUARDED (P7c, 2026-08-03).  Flex-Assign
     CONSUMES the definition, so its main call runs at [Ξ,Θ0] — one entry
     shorter than the conclusion's [Ξ,β̂≔τ,Θ0].  That is what lets the
     dispatcher's inner induction on the context length reach it; an
     unguarded main IH at the same fuel is exactly what is NOT available
     (DESIGN §12.1). *)
  (forall NM' M' Θ0' P0' P' R'' T'' Ψ' Θ' κ' Q',
     length Θ0' <= length Ξ + length Θ0 ->
     sub_complete_concl n NM' M' Θ0' P0' P' R'' T'' Ψ' Θ' κ' Q') ->
  sub_flex_complete_concl n NM M
    ((β ~ abind_flex_mono_def τ) ++ Θ0) Ξ α P0 R' Ψ Θ κ Q.
Proof.
  intros n NM M Θ0 Ξ α β τ P0 R' Ψ Θ κ Q IH.
  unfold sub_flex_complete_concl, sub_complete_concl in *.
  intros HdeclsΞ HdomΞ Hwf Hwfth HwfP0 Hfα HmodSK HmodTY Hinc Hslack HD Hrs
         HwfQ.
  (* ---- 0. the stripped context ---- *)
  assert (Huq : uniq (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
    by (apply a_wf_aenv_uniq; exact Hwf).
  assert (HβΞΘ0 : β `notin` dom (Ξ ++ Θ0)).
  { clear - Huq. simpl_env in Huq. destruct_uniq.
    unfold disjoint in *. simpl_env in *. fsetdec. }
  assert (Hwf' : a_wf_aenv (Ξ ++ Θ0))
    by (eapply a_wf_aenv_strip_mid; [ exact HdeclsΞ | exact Hwf ]).
  assert (Hwfcons : a_wf_aenv ((β ~ abind_flex_mono_def τ) ++ Θ0))
    by (eapply a_wf_aenv_strip_prefix; [ exact HdeclsΞ | exact Hwf ]).
  inversion Hwfcons as [ | | βz τz Θz HβΘ0 HwfτΘ0 Hmτ HwfΘ0 | | | ]; subst.
  assert (Hftvτ : ftvar_in_ptyp τ [<=] dom Θ0)
    by (apply a_wf_ptyp_ftv_dom; exact HwfτΘ0).
  assert (Hβτ : β `notin` ftvar_in_ptyp τ) by (clear - Hftvτ HβΘ0; fsetdec).
  (* ---- 1. strip κ around the DEFINED mid entry ---- *)
  destruct (@a_inc_strip_flex_def_mid Ξ β τ Θ0 κ Θ HdeclsΞ Hinc)
    as [κ1 [τβ [κ2 [Heqκ [Hlen [Hdomκ1 [Hincih [Heqβ [Hwfτβ [Hmτβ _]]]]]]]]]].
  assert (Hlk : forall γ, γ <> β ->
            msubst_lookup κ γ = msubst_lookup (κ1 ++ κ2) γ)
    by (intros γ Hγ; rewrite Heqκ; apply msubst_lookup_mid_ne; exact Hγ).
  (* κ1's keys are Ξ's, which miss τ's free variables *)
  assert (Hτ12 : msubst_ptyp (κ1 ++ κ2) τ = msubst_ptyp κ2 τ).
  { apply msubst_ptyp_agree. intros γ Hγ.
    apply msubst_lookup_app_notin.
    assert (HγΘ0 : γ `in` dom Θ0) by (clear - Hγ Hftvτ; fsetdec).
    rewrite Hdomκ1.
    assert (Huq' : uniq (Ξ ++ Θ0)) by (apply a_wf_aenv_uniq; exact Hwf').
    clear - Huq' HγΘ0. destruct_uniq. unfold disjoint in *. fsetdec. }
  assert (Heqβ' : Θ ⊢ τβ ≡ᵗ (msubst_ptyp (κ1 ++ κ2) τ))
    by (rewrite Hτ12; exact Heqβ).
  (* ---- 2. the substituted problem, and its side conditions ---- *)
  assert (Hwfpaint : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ ptyp_to_pskl τ).
  { apply a_scope_pskl_of_ptyp_vis;
      [ apply mono_ptyp_lc; exact Hmτ | ].
    intros γ Hγ. right.
    assert (HγΘ0 : a_binds_tvar γ Θ0)
      by (eapply a_wf_ptyp_ftv_tvarish; [ exact HwfτΘ0 | exact Hγ ]).
    destruct HγΘ0 as [Hb | [Hb | [τ1 Hb]]];
      [ left | right; left | right; right; exists τ1 ];
      unfold binds in *; apply in_or_app; right; exact Hb. }
  assert (HwfP0' : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ
            subst_pskl_in_pskl (ptyp_to_pskl τ) β P0).
  { eapply a_wf_pskl_subst_ctx with (b := abind_flex_mono_def τ);
      [ exact HwfP0 | reflexivity | exact HβΞΘ0 | clear; fsetdec
      | apply mono_ptyp_to_pskl_guarded; exact Hmτ | exact Hwfpaint ]. }
  assert (Hαb : a_binds_tvar α (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
    by (destruct (a_flex_tvar_app_weaken Ξ Hfα) as [h | [τ0 h]];
        [ right; left; exact h | right; right; exists τ0; exact h ]).
  assert (HwfS : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ
            subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)).
  { eapply a_wf_pskl_subst_ctx with (b := abind_flex_mono_def τ);
      [ apply a_wf_pskl__var; right; exact Hαb
      | reflexivity | exact HβΞΘ0 | clear; fsetdec
      | apply mono_ptyp_to_pskl_guarded; exact Hmτ | exact Hwfpaint ]. }
  (* ---- 3. the IH's ≡ᵘ slack and fill ---- *)
  assert (Hincβ : ((β, τβ) :: (κ1 ++ κ2))
                    ∷ ((β ~ abind_flex_mono_def τ) ++ (Ξ ++ Θ0)) ⊑ Θ)
    by (apply a_inc__flex_def;
        [ exact Hincih | exact Hwfτβ | exact Hmτβ | exact Heqβ' ]).
  assert (HwfX : a_wf_ptyp Θ (msubst_ptyp (κ1 ++ κ2) τ)).
  { eapply a_wf_ptyp_msubst;
      [ eapply a_wf_ptyp_weaken;
        [ intros x b0 Hb0; unfold binds in *; apply in_or_app; right; exact Hb0
        | exact HwfτΘ0 ]
      | exact Hwf' | exact Hincih ]. }
  assert (HmX : mono_ptyp (msubst_ptyp (κ1 ++ κ2) τ))
    by (eapply mono_ptyp_msubst; [ exact Hincih | exact Hmτ ]).
  assert (HincX : ((β, msubst_ptyp (κ1 ++ κ2) τ) :: (κ1 ++ κ2))
                    ∷ ((β ~ abind_flex_mono_def τ) ++ (Ξ ++ Θ0)) ⊑ Θ)
    by (apply a_inc__flex_def;
        [ exact Hincih | exact HwfX | exact HmX
        | apply a_tyequiv__refl; apply mono_ptyp_lc; exact HmX ]).
  assert (Hagree : forall γ,
            Θ ⊢ (msubst_lookup ((β, τβ) :: (κ1 ++ κ2)) γ)
              ≡ᵗ (msubst_lookup ((β, msubst_ptyp (κ1 ++ κ2) τ)
                                   :: (κ1 ++ κ2)) γ)).
  { intros γ. simpl. destruct (γ == β) as [-> | Hne];
      [ exact Heqβ'
      | apply a_tyequiv__refl; eapply a_inc_lookup_lc; exact Hincih ]. }

  (* ---- 3. the IH's fill and ≡ᵘ slack ---- *)
  assert (HlcP0 : lc_pskl P0) by (eapply a_wf_pskl_lc; exact HwfP0).
  assert (Hβdomκ1 : β `notin` dom κ1)
    by (rewrite Hdomκ1; clear - HβΞΘ0; simpl_env in HβΞΘ0; fsetdec).
  assert (HeqP0κ : msubst_pskl κ P0
                 = msubst_pskl ((β, τβ) :: (κ1 ++ κ2)) P0).
  { apply msubst_pskl_agree. intros γ _. rewrite Heqκ. simpl.
    destruct (γ == β) as [-> | Hne].
    - rewrite (@msubst_lookup_app_notin κ1 ((β, τβ) :: κ2) β Hβdomκ1).
      simpl.
      match goal with
      | |- (if ?t then _ else _) = _ => destruct t as [_ | n0]
      end; [ reflexivity | exfalso; apply n0; reflexivity ].
    - apply msubst_lookup_mid_ne; exact Hne. }
  assert (Heqs : Θ ⊢ (msubst_pskl κ P0)
                   ≡ˢ (msubst_pskl (κ1 ++ κ2)
                         (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0))).
  { rewrite HeqP0κ, msubst_pskl_subst_mono.
    eapply msubst_pskl_tyequiv_pointwise;
      [ exact Hincβ | exact HincX | exact HlcP0 | exact Hagree ]. }
  assert (Hrs' : ad_refine_syn_f empty Θ empty
            (pskl_to_bskl_inh (msubst_pskl (κ1 ++ κ2)
               (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0))) Q).
  { destruct (skl_tyequiv_refine_syn_f_transport Heqs Hwfth
                (fun x b0 (h : binds x b0 Θ) => h)) as [Hfwd _].
    apply Hfwd. exact Hrs. }
  assert (HeqR : ⌊ pskl_to_uskl
                    (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)) ⌋ˢ
                 = subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α))
    by apply uskl_to_pskl_pskl_to_uskl.
  assert (Hslack' : Θ ⊢ R' ≡ᵘ (msubst_uskl_syn (κ1 ++ κ2)
            (pskl_to_uskl
               (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α))))).
  { rewrite msubst_uskl_syn_pskl_to_uskl, msubst_pskl_subst_mono.
    cbn [msubst_pskl]. rewrite pskl_to_uskl_ptyp.
    eapply a_uskl_tyequiv_trans; [ exact Hslack | ].
    assert (HwfXctx : a_wf_aenv
              ((β ~ abind_flex_mono_def τ) ++ (Ξ ++ Θ0))).
    { simpl_env. apply a_wf_aenv__flex_def;
        [ exact HβΞΘ0
        | eapply a_wf_ptyp_weaken;
          [ intros x b0 Hb0; unfold binds in *; apply in_or_app; right;
            exact Hb0 | exact HwfτΘ0 ]
        | exact Hmτ | exact Hwf' ]. }
    assert (HαbX : a_binds_tvar α ((β ~ abind_flex_mono_def τ) ++ (Ξ ++ Θ0))).
    { assert (Hmove : forall (x : atom) (b0 : abind),
                binds x b0 (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0) ->
                binds x b0 ((β ~ abind_flex_mono_def τ) ++ (Ξ ++ Θ0))).
      { intros x b0 Hb. unfold binds in *. simpl in *.
        apply in_app_or in Hb. destruct Hb as [h | h];
          [ right; apply in_or_app; left; exact h
          | destruct h as [h | h];
            [ left; exact h
            | right; apply in_or_app; right; exact h ] ]. }
      destruct Hαb as [Hb | [Hb | [τ0 Hb]]];
        [ left | right; left | right; right; exists τ0 ];
        apply Hmove; exact Hb. }
    assert (Heqlk : Θ ⊢ (msubst_lookup κ α)
              ≡ᵗ (msubst_lookup ((β, msubst_ptyp (κ1 ++ κ2) τ)
                                   :: (κ1 ++ κ2)) α)).
    { simpl. destruct (α == β) as [-> | Hne].
      - rewrite Heqκ.
        rewrite (@msubst_lookup_app_notin κ1 ((β, τβ) :: κ2) β Hβdomκ1).
        simpl.
        match goal with
        | |- context [if ?t then _ else _] => destruct t as [_ | n0]
        end; [ exact Heqβ' | exfalso; apply n0; reflexivity ].
      - rewrite (Hlk α Hne).
        apply a_tyequiv__refl; eapply a_inc_lookup_lc; exact Hincih. }
    apply a_uskl_tyequiv__mono.
    - eapply a_inc_lookup_mono; exact Hinc.
    - eapply a_inc_lookup_mono; exact HincX.
    - eapply a_inc_lookup_wf; [ exact Hinc | exact Hwf | exact Hαb ].
    - eapply a_inc_lookup_wf; [ exact HincX | exact HwfXctx | exact HαbX ].
    - exact Heqlk. }
  (* ---- 4. the P7b IH at the substituted problem.  Its motive premise:
     the subject R' is ≡ᵘ a monotype PAINTING (the walk's own slack), so it
     is ghost-free outright — no NM analysis needed. ---- *)
  assert (Hgf' : NM = a_sub_mode_ty -> uskl_ghost_free R').
  { intros _. eapply tyequiv_mono_paint_ghost_free;
      [ exact Hslack
      | eapply a_inc_lookup_mono; exact Hinc
      | eapply a_inc_lookup_wf; [ exact Hinc | exact Hwf | exact Hαb ] ]. }
  destruct (IH NM (mode_fn M) (Ξ ++ Θ0)
              (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0)
              (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α))
              (pskl_to_uskl
                 (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)))
              R' Ψ Θ (κ1 ++ κ2) Q
              ltac:(rewrite length_app; lia)
              Hwf' Hwfth HwfP0' HwfS
              ltac:(intros HSK; apply a_sk_mode_compat_subst_mono;
                    [ apply HmodSK; exact HSK | exact Hmτ ])
              ltac:(intros HTY; apply a_ty_mode_compat_subst_mono;
                    [ apply HmodTY; exact HTY | exact Hmτ ])
              HeqR Hincih Hslack' HD Hrs' HwfQ Hgf')
    as [P1 [Θ1 [Hrun Hopt]]].

  (* ---- 5. soundness of the IH's run, and the junk rename ---- *)
  assert (HmodSK' : NM = a_sub_mode_sk ->
            a_sk_mode_compat (mode_fn M)
              (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0))
    by (intros HSK; apply a_sk_mode_compat_subst_mono;
        [ apply HmodSK; exact HSK | exact Hmτ ]).
  assert (HmodTY' : NM = a_sub_mode_ty ->
            a_ty_mode_compat (mode_fn M)
              (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0))
    by (intros HTY; apply a_ty_mode_compat_subst_mono;
        [ apply HmodTY; exact HTY | exact Hmτ ]).
  destruct (a_sub_sound_thm Hrun Hwf' HwfP0' HwfS HmodSK' HmodTY')
    as [[[w [Hidw Hincw]] Hdefs] [HwfΘ1 [Qt [HeqQt [Hjoin1 _]]]]].
  assert (HscP1 : a_scope_pskl Θ1 P1)
    by (rewrite <- HeqQt; eapply ad_pat_sub_target_wf; exact Hjoin1).
  assert (HβflexΘ1 : forall bd, binds β bd Θ1 ->
            bd = abind_flex_mono \/ exists τ0, bd = abind_flex_mono_def τ0).
  { intros bd Hb.
    assert (Hprov : a_suffix_binding bd \/ β `in` dom (Ξ ++ Θ0))
      by (eapply a_inc_binds_provenance; eassumption).
    destruct Hprov as [h | h];
      [ inversion h; subst;
        [ left; reflexivity | right; eexists; reflexivity ]
      | exfalso; clear - h HβΞΘ0; fsetdec ]. }
  (* β misses everything the run's INPUTS mention *)
  assert (HβΞΘ0f : β `notin` ftvar_in_aenv (Ξ ++ Θ0)).
  { pose proof (a_wf_aenv_ftvar_dom Hwf') as h. clear - h HβΞΘ0. fsetdec. }
  assert (HβP0' : β `notin` ftvar_in_pskl
            (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0)).
  { pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P0
                  (ptyp_to_pskl τ) β) as h.
    pose proof (ftvar_in_ptyp_to_pskl τ) as h2.
    clear - h h2 Hβτ. fsetdec. }
  assert (HβS : β `notin` ftvar_in_pskl
            (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α))).
  { pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper (pskl_var_f α)
                  (ptyp_to_pskl τ) β) as h.
    pose proof (ftvar_in_ptyp_to_pskl τ) as h2.
    clear - h h2 Hβτ. fsetdec. }
  destruct (atom_fresh (dom Θ1 `union` ftvar_in_aenv Θ1
                        `union` ftvar_in_pskl P1
                        `union` ftvar_in_aenv (Ξ ++ Θ0) `union` dom (Ξ ++ Θ0)
                        `union` ftvar_in_pskl
                            (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0)
                        `union` ftvar_in_pskl
                            (subst_pskl_in_pskl (ptyp_to_pskl τ) β
                               (pskl_var_f α))
                        `union` ftvar_in_ptyp τ `union` singleton β))
    as [β1 Fr].
  assert (Hrunsw : a_sub NM (mode_fn M)
            (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0) (Ξ ++ Θ0)
            (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α))
            (swap_pskl β β1 P1) (swap_aenv β β1 Θ1)).
  { apply (a_sub_swap_junk β β1 NM (mode_fn M)
             (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0) (Ξ ++ Θ0)
             (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α))
             P1 Θ1 Hrun);
      [ clear - HβΞΘ0f HβP0' HβS; fsetdec | clear - Fr; fsetdec ]. }
  exists (swap_pskl β β1 P1),
         ((β ~ abind_flex_mono_def τ) ++ swap_aenv β β1 Θ1).
  split.
  { apply a_sub_flex__assign;
      [ apply swap_junk_dom_out; clear - Fr; fsetdec | exact Hrunsw ]. }
  (* ---- 6. the package ---- *)
  intros κf Hidf Hincf.
  destruct (@a_inc_strip_flex_def_mid Ξ β τ Θ0 κf
              ((β ~ abind_flex_mono_def τ) ++ swap_aenv β β1 Θ1)
              HdeclsΞ Hincf)
    as [κf1 [τf [κf2 [Heqκf [Hlenf [_ [Hincfih [_ [_ [_ _]]]]]]]]]].
  assert (Hidfih : is_id_msubst (κf1 ++ κf2)).
  { unfold is_id_msubst in *. rewrite Heqκf in Hidf.
    apply Forall_app in Hidf. destruct Hidf as [h1 h2].
    inversion h2; subst. apply Forall_app; split; assumption. }
  assert (Heqτf : τf = ptyp_var_f β).
  { unfold is_id_msubst in Hidf. rewrite Heqκf in Hidf.
    apply Forall_app in Hidf. destruct Hidf as [_ h2].
    inversion h2 as [| e κl he hl]; subst.
    unfold is_id_entry in he; simpl in he. exact he. }
  assert (Heqw : w = κf1 ++ κf2)
    by (eapply is_id_inc_unique;
        [ exact Hincw | exact Hidw | exact Hincfih | exact Hidfih ]).
  subst w.
  destruct (Hopt (κf1 ++ κf2) Hidfih Hincw) as [ζ [Hζ [Hie Hprec]]].
  assert (Hkeysζ : forall γ, List.In γ (List.map fst ζ) -> γ `in` dom Θ1)
    by (intros γ hγ; eapply a_inc_keys_dom; [ exact Hζ | exact hγ ]).
  assert (Hkeysf : forall γ, List.In γ (List.map fst (κf1 ++ κf2)) ->
            γ `in` dom (Ξ ++ Θ0))
    by (intros γ hγ; eapply a_inc_keys_dom; [ exact Hincfih | exact hγ ]).
  (* ζ agrees with κ1 ++ κ2 on τ's free variables *)
  assert (Hζτ : Θ ⊢ (msubst_ptyp (κ1 ++ κ2) τ) ≡ᵗ (msubst_ptyp ζ τ)).
  { eapply msubst_ptyp_tyequiv_two_msubst;
      [ exact Hincih | exact Hζ | apply mono_ptyp_lc; exact Hmτ | ].
    intros γ Hγ.
    assert (HγΘ0 : γ `in` dom Θ0) by (clear - Hγ Hftvτ; fsetdec).
    assert (Hbt : a_binds_tvar γ (Ξ ++ Θ0)).
    { assert (h : a_binds_tvar γ Θ0)
        by (eapply a_wf_ptyp_ftv_tvarish; [ exact HwfτΘ0 | exact Hγ ]).
      destruct h as [hb | [hb | [τ1 hb]]];
        [ left | right; left | right; right; exists τ1 ];
        (unfold binds in *; apply in_or_app; right; exact hb). }
    assert (Heq1 : Θ ⊢ (msubst_lookup (κ1 ++ κ2) γ)
              ≡ᵗ (msubst_lookup (msubst_compose ζ (κf1 ++ κf2)) γ))
      by (eapply src.frost.algo.prop_normal.a_inc_equiv_lookup;
          [ exact Hie | exact Hwf' | exact Hbt ]).
    assert (Heq2 : msubst_lookup (msubst_compose ζ (κf1 ++ κf2)) γ
                 = msubst_lookup ζ γ).
    { destruct (AtomSetProperties.In_dec γ (dom (κf1 ++ κf2)))
        as [hin | hout].
      - rewrite (@msubst_lookup_compose ζ (κf1 ++ κf2) γ (or_introl hin)).
        assert (hid : msubst_lookup (κf1 ++ κf2) γ = ptyp_var_f γ)
          by (eapply msubst_lookup_id; exact Hidfih).
        rewrite hid. reflexivity.
      - (* γ is RIGID in (Ξ ++ Θ0): not a key of the identity, nor of ζ *)
        assert (hnf : ~ a_flex_tvar (Ξ ++ Θ0) γ)
          by (intro hc; apply hout;
              eapply a_inc_flex_dom; [ exact Hincfih | exact Hwf' | exact hc ]).
        assert (hnζ : γ `notin` dom ζ).
        { intro hc.
          assert (hfl : a_flex_tvar Θ1 γ)
            by (eapply a_inc_dom_flex; [ exact Hζ | exact hc ]).
          assert (hrig : binds γ abind_tvar (Ξ ++ Θ0)).
          { destruct Hbt as [hb | [hb | [τ1 hb]]];
              [ exact hb | exfalso; apply hnf; left; exact hb
              | exfalso; apply hnf; right; exists τ1; exact hb ]. }
          assert (hrigΘ1 : binds γ abind_tvar Θ1)
            by (eapply a_inc_binds_tvar; [ exact Hincw | exact hrig ]).
          destruct hfl as [hb | [τ1 hb]];
            (pose proof (binds_unique _ _ _ _ _ hrigΘ1 hb
                           (a_wf_aenv_uniq HwfΘ1)) as hc2; discriminate hc2). }
        rewrite (@msubst_lookup_compose ζ (κf1 ++ κf2) γ (or_intror hnζ)).
        rewrite (msubst_lookup_notin _ hout). simpl. reflexivity. }
    rewrite <- Heq2. exact Heq1. }
  exists ((β, τβ) :: kswap_msubst β β1 ζ).
  split.
  { apply a_inc__flex_def;
      [ apply (a_inc_kswap β β1 ζ Θ1 Θ Hζ);
        [ clear - Fr; fsetdec | exact HwfΘ1 | clear - Fr; fsetdec
        | exact HβflexΘ1 ]
      | exact Hwfτβ | exact Hmτβ | ].
    assert (Hkτ : msubst_ptyp (kswap_msubst β β1 ζ) τ = msubst_ptyp ζ τ).
    { rewrite <- (swap_ptyp_fresh_id β β1 τ) at 1;
        [ | clear - Hβτ; fsetdec | clear - Fr; fsetdec ].
      apply msubst_ptyp_kswap;
        [ clear - Fr; fsetdec
        | intro hc; pose proof (Hkeysζ β1 hc) as h; clear - h Fr; fsetdec
        | clear - Fr; fsetdec
        | left; exact Hβτ ]. }
    rewrite Hkτ.
    eapply a_tyequiv__trans; [ exact Heqβ' | exact Hζτ ]. }
  split.
  { (* the equivalence *)
    rewrite Heqκ, Heqκf, Heqτf.
    assert (Hsplit : msubst_compose ((β, τβ) :: kswap_msubst β β1 ζ)
                       (κf1 ++ (β, ptyp_var_f β) :: κf2)
                   = msubst_compose ((β, τβ) :: kswap_msubst β β1 ζ) κf1
                     ++ (β, τβ)
                     :: msubst_compose ((β, τβ) :: kswap_msubst β β1 ζ) κf2).
    { unfold msubst_compose. rewrite List.map_app. simpl.
      destruct (β == β) as [_ | n0]; [ reflexivity | exfalso; auto ]. }
    rewrite Hsplit.
    assert (Hid1 : is_id_msubst κf1 /\ is_id_msubst κf2)
      by (unfold is_id_msubst in Hidfih; apply Forall_app in Hidfih;
          exact Hidfih).
    destruct Hid1 as [Hidf1 Hidf2].
    assert (Hkey1 : forall γ, List.In γ (List.map fst κf1) ->
              γ <> β /\ γ <> β1).
    { intros γ hγ.
      assert (hd : γ `in` dom (Ξ ++ Θ0))
        by (apply Hkeysf; rewrite List.map_app; apply in_or_app; left; exact hγ).
      split; [ intro Hc; subst; clear - hd HβΞΘ0; fsetdec
             | intro Hc; subst; clear - hd Fr; fsetdec ]. }
    assert (Hkey2 : forall γ, List.In γ (List.map fst κf2) ->
              γ <> β /\ γ <> β1).
    { intros γ hγ.
      assert (hd : γ `in` dom (Ξ ++ Θ0))
        by (apply Hkeysf; rewrite List.map_app; apply in_or_app; right; exact hγ).
      split; [ intro Hc; subst; clear - hd HβΞΘ0; fsetdec
             | intro Hc; subst; clear - hd Fr; fsetdec ]. }
    assert (Hk1b : forall γ, List.In γ (List.map fst κf1) -> γ <> β)
      by (intros γ hγ; exact (proj1 (Hkey1 γ hγ))).
    assert (Hk2b : forall γ, List.In γ (List.map fst κf2) -> γ <> β)
      by (intros γ hγ; exact (proj1 (Hkey2 γ hγ))).
    rewrite (@msubst_compose_head_id β τβ (kswap_msubst β β1 ζ) κf1 Hidf1 Hk1b).
    rewrite (@msubst_compose_head_id β τβ (kswap_msubst β β1 ζ) κf2 Hidf2 Hk2b).
    rewrite (msubst_compose_kswap_id β β1 ζ κf1 Hidf1 Hkey1).
    rewrite (msubst_compose_kswap_id β β1 ζ κf2 Hidf2 Hkey2).
    apply a_inc_equiv_insert_flex_def_mid;
      [ exact HdeclsΞ | exact Hlen
      | unfold msubst_compose in *; rewrite <- List.map_app; exact Hie
      | unfold msubst_compose; rewrite List.map_length; exact Hlenf
      | apply a_tyequiv__refl; apply mono_ptyp_lc; exact Hmτβ
      | exact Heqβ ]. }
  { (* the precision *)
    assert (Hnbsw : β `notin` ftvar_in_pskl (swap_pskl β β1 P1)).
    { intro Hc.
      assert (h : β1 `in` ftvar_in_pskl P1).
      { pose proof (swap_pskl_ftv_in_rev β β1 P1 β Hc) as h0.
        rewrite swap_atom_l in h0. exact h0. }
      clear - h Fr. fsetdec. }
    rewrite (msubst_bskl_head_notin β τβ (kswap_msubst β β1 ζ)
               (pskl_to_bskl_syn (swap_pskl β β1 P1))
               ltac:(rewrite ftvar_in_bskl_syn; exact Hnbsw)).
    rewrite (msubst_bskl_kswap_paint β β1 ζ P1);
      [ exact Hprec
      | clear - Fr; fsetdec
      | intro hc; pose proof (Hkeysζ β1 hc) as h; clear - h Fr; fsetdec
      | clear - Fr; fsetdec
      | destruct (AtomSetProperties.In_dec β (ftvar_in_pskl P1))
          as [hin | hout]; [ right | left; exact hout ];
        assert (hbt : a_binds_tvar β Θ1)
          by (eapply a_scope_pskl_ftv_binds; [ exact HscP1 | exact hin ]);
        destruct hbt as [hbt | [hbt | [τ0 hbt]]];
        [ exfalso; destruct (HβflexΘ1 abind_tvar hbt) as [hc | [τ1 hc]];
            discriminate
        | eapply a_inc_flex_in_keys; [ exact Hζ | left; exact hbt ]
        | eapply a_inc_flex_in_keys; [ exact Hζ | right; eexists; exact hbt ] ] ].
  }
Qed.


(* ===================================================================== *)
(*  (J)  Flex-Solve's CRUX — the join's ARROW GENERATION at a monotype     *)
(*       subject (the paper's step ⓒ→ⓓ, subtyping-proofs.tex:2920)        *)
(*                                                                        *)
(*  The paper says "inversion on ⓒ with Sub-Arrow gives monotypes τ1 and   *)
(*  τ2"; in the mech that inversion must also CHASE definitions, because   *)
(*  a monotype subject may be a defined flexible of Θ and the join then    *)
(*  fires [__flex_mono] instead of [__arrow].  That row preserves the      *)
(*  FUEL, so the chase costs nothing and the regenerated join comes back   *)
(*  at the same [n] — which is what the row lemma's IH needs.  Every other *)
(*  row is excluded by the mode ([__infer] is TI, [__check] /              *)
(*  [__univ_ghost_r] / [__forall_r] are TC) or by the subject's shape (a   *)
(*  mono painting is [unit] / a variable / an arrow — never a ghost, and   *)
(*  never a ∀, which is what kills the two ForallL rows).                  *)
(*                                                                        *)
(*  Reusable by P7c: its [__flex_mono] join case needs exactly this.       *)
(* ===================================================================== *)

(** THE ARROW GENERATION for a MONOTYPE subject at an FN mode: the join can
    only be [__arrow] (already an arrow) or [__flex_mono] (chase the
    definition — same fuel), every other row being excluded by the mode or by
    the subject's shape (a mono painting is [unit] / a variable / an arrow,
    never a ghost and never a ∀). *)
Lemma ad_pat_sub_gv_mono_fn_arrow_inv : forall n NM Mf Ψ Θ R Q,
  ad_pat_sub_gv n NM Mf Ψ Θ R Q ->
  a_wf_aenv Θ ->
  forall M τ, Mf = mode_fn M -> R = ptyp_to_uskl_syn τ ->
  mono_ptyp τ -> a_wf_ptyp Θ τ ->
  exists τ1 τ2,
    Θ ⊢ τ ≡ᵗ (ptyp_arrow τ1 τ2) /\
    mono_ptyp τ1 /\ mono_ptyp τ2 /\
    a_wf_ptyp Θ τ1 /\ a_wf_ptyp Θ τ2 /\
    ad_pat_sub_gv n NM (mode_fn M) Ψ Θ
      (ptyp_to_uskl_syn (ptyp_arrow τ1 τ2)) Q.
Proof.
  intros n NM Mf Ψ Θ R Q H Hwfth; induction H;
    intros M0 τ0 HeqM HeqR Hm Hwf;
    try discriminate HeqM;
    try (destruct τ0; cbn in HeqR; try discriminate HeqR;
         try solve [ inversion Hm ]).
  - (* arrow *)
    inversion HeqM; subst. inversion HeqR; subst.
    assert (Hrefl : Θ ⊢ (ptyp_arrow τ0_1 τ0_2) ≡ᵗ (ptyp_arrow τ0_1 τ0_2))
      by (apply a_tyequiv__refl; apply mono_ptyp_lc; exact Hm).
    inversion Hm; subst. inversion Hwf; subst.
    exists τ0_1, τ0_2.
    split; [ exact Hrefl | ].
    split; [ assumption | ]. split; [ assumption | ].
    split; [ assumption | ]. split; [ assumption | ].
    cbn. eapply ad_pat_sub_gv__arrow; eassumption.
  - (* flex_mono : chase the definition, same fuel *)
    injection HeqR; intros He; subst.
    assert (Hmτ : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwfth | eassumption ]).
    assert (Hwfτ : a_wf_ptyp Θ τ)
      by (eapply a_wf_aenv_binds_def_wf; [ exact Hwfth | eassumption ]).
    destruct (IHad_pat_sub_gv Hwfth M0 τ HeqM eq_refl Hmτ Hwfτ)
      as [τ1 [τ2 [Heq [Hm1 [Hm2 [Hwf1 [Hwf2 Hjoin]]]]]]].
    exists τ1, τ2.
    split.
    { eapply a_tyequiv__trans; [ | exact Heq ].
      apply a_tyequiv__flex_def; eassumption. }
    split; [ exact Hm1 | ]. split; [ exact Hm2 | ].
    split; [ exact Hwf1 | ]. split; [ exact Hwf2 | ]. exact Hjoin.
Qed.


(* ===================================================================== *)
(*  (K)  P7a ROW — Flex-Solve (the paper's FIRST interesting case, :2880)  *)
(*                                                                        *)
(*  The paper's θs is built here: §(J)'s arrow generation supplies the     *)
(*  [τ ≡ᵗ τ1→τ2] that [a_inc__flex_def] demands for the deposited          *)
(*  [α̂0 ≔ α̂→β̂], and the two fresh declarations take τ1 / τ2.  The row      *)
(*  needs NO junk swap — Flex-Solve does not re-attach, so it carries no   *)
(*  Barendregt output premise — and its package is the paper's ⓖ+⑫ ⇒ ⑭:   *)
(*  peel the deposited block out of BOTH identity witnesses, identify them *)
(*  by [is_id_inc_unique] + length, and collapse the equivalence with      *)
(*  [a_inc_equiv_collapse_solve].                                          *)
(*                                                                        *)
(*  ⚙ MEASURED (coqc -time): one [fsetdec] against the three overlapping   *)
(*  freshness unions cost 152s of the file's 153s.  Both fixes are applied *)
(*  below and are the standing rule — keep each [atom_fresh] avoid set     *)
(*  MINIMAL, and shatter it into ATOMIC facts immediately, one             *)
(*  single-hypothesis [fsetdec] each.  152s → 0.09s.                       *)
(* ===================================================================== *)

(** [a_wf_pskl] reads Θ ONLY through [a_binds_tvar] (its context never grows —
    the binder rule extends Δ), so it weakens along any TVAR-ISH monotone map.
    [a_wf_pskl_weaken]'s [binds]-monotone form is too strong here: Flex-Solve
    turns [α̂0]'s DECLARATION into a DEFINITION. *)
Lemma a_wf_pskl_weaken_tvarish : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  forall Θ', (forall α, a_binds_tvar α Θ -> a_binds_tvar α Θ') ->
  Θ' ⨟ Δ ⊢ₚₛᵃ P.
Proof.
  intros Θ Δ P H; induction H; intros Θ' Hmon.
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var. destruct H as [HΔ | Ht];
      [ left; exact HΔ | right; apply Hmon; exact Ht ].
  - apply a_wf_pskl__arrow; auto.
  - apply a_wf_pskl__all with (L := L). intros α Hα. apply H0; auto.
  - apply a_wf_pskl__hole.
  - apply a_wf_pskl__tophole; [ exact H | auto ].
Qed.

(** The companion of the strip lemmas: RE-ATTACHING a declaration-only prefix
    over a DIFFERENT tail.  (The prefix's per-entry obligations are wf/mono of
    its images in the TARGET, which the strip's own increase already carries.) *)
Lemma a_inc_attach_decls_prefix : forall Ξ κ1 Θa κa Θb κb Θ,
  a_decls Ξ ->
  (κ1 ++ κa) ∷ (Ξ ++ Θa) ⊑ Θ ->
  length κ1 = length Ξ ->
  κb ∷ Θb ⊑ Θ ->
  (κ1 ++ κb) ∷ (Ξ ++ Θb) ⊑ Θ.
Proof.
  intros Ξ; induction Ξ as [| [x b] Ξ' IH];
    intros κ1 Θa κa Θb κb Θ Hd Hinc Hlen Hincb.
  - destruct κ1; [ | discriminate ]. simpl. exact Hincb.
  - inversion Hd as [ | ? ? Hd' ]; subst.
    destruct κ1 as [| [k1a k1b] κ1']; [ discriminate | ].
    simpl in Hinc.
    inversion Hinc as [ | Θz κz Θy αz τz Hi Hw Hm | | | | ]; subst.
    simpl. apply a_inc__flex; [ | exact Hw | exact Hm ].
    eapply IH; [ exact Hd' | exact Hi | simpl in Hlen; lia | exact Hincb ].
Qed.

(** …and its [a_wf_aenv] counterpart. *)
Lemma a_wf_aenv_replace_decls_tail : forall Ξ Θa Θb,
  a_decls Ξ ->
  a_wf_aenv (Ξ ++ Θa) ->
  a_wf_aenv Θb ->
  (forall x, x `in` dom Ξ -> x `notin` dom Θb) ->
  a_wf_aenv (Ξ ++ Θb).
Proof.
  intros Ξ; induction Ξ as [| [x b] Ξ' IH]; intros Θa Θb Hd Hwf Hwfb Hdisj.
  - simpl. exact Hwfb.
  - inversion Hd as [ | ? ? Hd' ]; subst.
    simpl in Hwf. inversion Hwf as [ | αz Θz Hn Hwf' | | | | ]; subst.
    simpl. apply a_wf_aenv__flex.
    + rewrite dom_app.
      assert (h1 : x `notin` dom Ξ')
        by (rewrite dom_app in Hn; clear - Hn; fsetdec).
      assert (h2 : x `notin` dom Θb)
        by (apply Hdisj; simpl; clear; fsetdec).
      clear - h1 h2; fsetdec.
    + eapply IH; [ exact Hd' | exact Hwf' | exact Hwfb | ].
      intros y Hy. apply Hdisj. simpl. clear - Hy; fsetdec.
Qed.

(** Two entries inserted just below a mid entry are invisible to a lookup
    that avoids their keys. *)
Lemma msubst_lookup_insert2 : forall κ1 α0 τ β τ2 α τ1 κ2 γ,
  γ <> α -> γ <> β ->
  msubst_lookup (κ1 ++ (α0, τ) :: (β, τ2) :: (α, τ1) :: κ2) γ
  = msubst_lookup (κ1 ++ (α0, τ) :: κ2) γ.
Proof.
  intros κ1; induction κ1 as [| [x tx] κ1'];
    intros α0 τ β τ2 α τ1 κ2 γ Hα Hβ; simpl.
  - destruct (γ == α0) as [_ | _]; [ reflexivity | ].
    destruct (γ == β) as [e | _]; [ exfalso; auto | ].
    destruct (γ == α) as [e | _]; [ exfalso; auto | reflexivity ].
  - destruct (γ == x) as [_ | _]; [ reflexivity | apply IHκ1'; assumption ].
Qed.

(** THE COLLAPSE (the paper's ⓖ+⑫ ⇒ ⑭): Flex-Solve's deposited block
    [α̂0 ≔ α̂→β̂, β̂, α̂] carries the same α̂0-image on both sides, so the
    equivalence descends to the conclusion's source, where α̂0 is a bare
    declaration again. *)
Lemma a_inc_equiv_collapse_solve :
  forall Ξ κ1 κ2 σ1 σ2 α0 τ β τ2 α τ1 X Xb Xa Θ0 Θ,
  a_decls Ξ ->
  length κ1 = length Ξ -> length σ1 = length Ξ ->
  a_inc_equiv
    (Ξ ++ (α0 ~ abind_flex_mono_def
                 (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
        ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0)
    (κ1 ++ (α0, τ) :: (β, τ2) :: (α, τ1) :: κ2)
    (σ1 ++ (α0, X) :: (β, Xb) :: (α, Xa) :: σ2) Θ ->
  a_inc_equiv (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0)
              (κ1 ++ (α0, τ) :: κ2) (σ1 ++ (α0, X) :: σ2) Θ.
Proof.
  intros Ξ; induction Ξ as [| [x b] Ξ' IH];
    intros κ1 κ2 σ1 σ2 α0 τ β τ2 α τ1 X Xb Xa Θ0 Θ Hd Hlk Hls He.
  - destruct κ1; [ | discriminate ]. destruct σ1; [ | discriminate ].
    simpl in *.
    inversion He as [ | | Θz κz σz Θy αz τz τz1 τz2 Hie Heq Heqd | | | ];
      subst.
    inversion Hie as [ | Θa κa σa Θb αa τa1 τa2 Hie2 Heq2 | | | | ]; subst.
    inversion Hie2 as [ | Θc κc σc Θe αc τc1 τc2 Hie3 Heq3 | | | | ]; subst.
    apply a_inc_equiv__flex; [ exact Hie3 | exact Heq ].
  - inversion Hd as [ | ? ? Hd' ]; subst.
    destruct κ1 as [| [k1a k1b] κ1']; [ discriminate | ].
    destruct σ1 as [| [s1a s1b] σ1']; [ discriminate | ].
    simpl in He.
    inversion He as [ | Θa κa σa Θb αa τa1 τa2 Hie Heq | | | | ]; subst.
    simpl. apply a_inc_equiv__flex; [ | exact Heq ].
    eapply IH; [ exact Hd' | simpl in Hlk; lia | simpl in Hls; lia | exact Hie ].
Qed.

(** [app_inj_tail_length] keyed on the HEADS' lengths (the shape every
    peel produces). *)
Lemma app_split_by_head_length : forall (A : Type) (l1 l2 m1 m2 : list A),
  l1 ++ l2 = m1 ++ m2 -> length l1 = length m1 -> l1 = m1 /\ l2 = m2.
Proof.
  intros A l1 l2 m1 m2 Heq Hlen.
  apply app_inj_tail_length; [ exact Heq | ].
  assert (h : length (l1 ++ l2) = length (m1 ++ m2))
    by (rewrite Heq; reflexivity).
  repeat rewrite List.app_length in h. lia.
Qed.

Lemma binds_insert_two_mid : forall (γ : atom) (b : abind) Ξ α0 b0 b1 e1 e2 Θ0,
  binds γ b (Ξ ++ (α0 ~ b0) ++ Θ0) -> γ <> α0 ->
  binds γ b (Ξ ++ (α0 ~ b1) ++ e1 ++ e2 ++ Θ0).
Proof.
  (* ⚙ NOT [analyze_binds]: on a FIVE-part environment it costs minutes.
     The explicit list walk is instant. *)
  intros γ b Ξ α0 b0 b1 e1 e2 Θ0 Hb Hne.
  unfold binds in *. apply in_app_or in Hb. apply in_or_app.
  destruct Hb as [h | h]; [ left; exact h | right ].
  simpl in h. destruct h as [h | h];
    [ exfalso; inversion h; subst; apply Hne; reflexivity | ].
  simpl. right. apply in_or_app. right. apply in_or_app. right. exact h.
Qed.

Lemma a_decls_binds : forall Ξ γ b,
  a_decls Ξ -> binds γ b Ξ -> b = abind_flex_mono.
Proof.
  intros Ξ γ b H; induction H; intros Hb;
    [ inversion Hb | analyze_binds Hb; auto ].
Qed.

(* ===================================================================== *)
(*  P7a ROW — Flex-Solve (the paper's FIRST interesting case, :2880)       *)
(* ===================================================================== *)

Lemma a_sub_flex_complete_solve : forall n NM M Θ0 Ξ α0 P0 R' Ψ Θ κ Q,
  (* ⭐ THE CROSS-HALF IH IS ARROW-RESTRICTED (P7c, 2026-08-03).  Flex-Solve
     re-enters the MAIN judgment at the deposited subject [α̂ → β̂] — an
     ARROW — over a context TWO ENTRIES LARGER, so neither the fuel nor the
     context decreases on this edge.  ⭐ What breaks the cycle is the
     SUBJECT: a main call at an arrow subject can never come back into P7a
     (the escape needs a VARIABLE subject and no join row shrinks an arrow to
     a variable), so the arrow-subject half of the main motive is provable
     from the FUEL IH alone (DESIGN §12.1's layer (a)).  This row needs no
     more. *)
  (forall NM' M' Θ0' P0' P' Ra Rb T'' Ψ' Θ' κ' Q',
     sub_complete_concl n NM' M' Θ0' P0' P' (uskl_arrow Ra Rb) T''
       Ψ' Θ' κ' Q') ->
  sub_flex_complete_concl n NM M ((α0 ~ abind_flex_mono) ++ Θ0) Ξ α0 P0
    R' Ψ Θ κ Q.
Proof.
  intros n NM M Θ0 Ξ α0 P0 R' Ψ Θ κ Q IH.
  unfold sub_flex_complete_concl, sub_complete_concl in *.
  intros HdeclsΞ HdomΞ Hwf Hwfth HwfP0 Hfα HmodSK HmodTY Hinc Hslack HD Hrs
         HwfQ.
  (* ---- 0. the stripped context ---- *)
  assert (Huq : uniq (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0))
    by (apply a_wf_aenv_uniq; exact Hwf).
  assert (Hα0ΞΘ0 : α0 `notin` dom (Ξ ++ Θ0)).
  { clear - Huq. simpl_env in Huq. destruct_uniq.
    unfold disjoint in *. simpl_env in *. fsetdec. }
  assert (Hwf' : a_wf_aenv (Ξ ++ Θ0))
    by (eapply a_wf_aenv_strip_mid; [ exact HdeclsΞ | exact Hwf ]).
  assert (HwfΘ0 : a_wf_aenv Θ0) by (eapply a_wf_aenv_app_r; exact Hwf').
  (* ---- 1. strip κ at the subject's own (undefined) entry ---- *)
  destruct (@a_inc_strip_flex_mid Ξ α0 Θ0 κ Θ HdeclsΞ Hinc)
    as [κ1 [τ [κ2 [Heqκ [Hlen [Hdomκ1 [Hincih [Hwfτ [Hmτ Hincκ2]]]]]]]]].
  assert (Hα0κ1 : α0 `notin` dom κ1)
    by (rewrite Hdomκ1; clear - Hα0ΞΘ0; simpl_env in Hα0ΞΘ0; fsetdec).
  assert (Hlkα0 : msubst_lookup κ α0 = τ).
  { rewrite Heqκ.
    rewrite (@msubst_lookup_app_notin κ1 ((α0, τ) :: κ2) α0 Hα0κ1). simpl.
    match goal with
    | |- (if ?t then _ else _) = _ => destruct t as [_ | n0]
    end; [ reflexivity | exfalso; apply n0; reflexivity ]. }
  rewrite Hlkα0 in Hslack.
  (* ---- 2. the subject is a MONO painting … ---- *)
  destruct (a_uskl_tyequiv_mono_r_inv Hslack (eq_refl (ptyp_to_uskl_syn τ)) Hmτ Hwfτ)
    as [τ' [HeqR' [Hmτ' [Hwfτ' Heqττ']]]].
  subst R'.
  (* ---- 3. … and the join makes it an ARROW ---- *)
  destruct (ad_pat_sub_gv_mono_fn_arrow_inv HD Hwfth
              (eq_refl (mode_fn M)) (eq_refl (ptyp_to_uskl_syn τ'))
              Hmτ' Hwfτ')
    as [τ1 [τ2 [Heqarr [Hm1 [Hm2 [Hwf1 [Hwf2 _]]]]]]].
  assert (Hτarr : Θ ⊢ τ ≡ᵗ (ptyp_arrow τ1 τ2)).
  { eapply a_tyequiv__trans;
      [ apply a_tyequiv__sym; exact Heqττ' | exact Heqarr ]. }

  (* ---- 4. the deposited pair.  ⚙ keep the avoid sets SMALL and shatter
     them into ATOMIC facts immediately: three overlapping unions handed to
     one [fsetdec] below cost 152s (measured with [coqc -time]). ---- *)
  simpl_env in Hα0ΞΘ0.
  destruct (atom_fresh (dom Ξ `union` dom Θ0 `union` singleton α0
                        `union` ftvar_in_pskl P0)) as [α Frα].
  destruct (atom_fresh (dom Ξ `union` dom Θ0 `union` singleton α0
                        `union` singleton α `union` ftvar_in_pskl P0))
    as [β Frβ].
  assert (Hαβ : α <> β) by (clear - Frβ; fsetdec).
  assert (HαΞ : α `notin` dom Ξ) by (clear - Frα; fsetdec).
  assert (HαΘ0 : α `notin` dom Θ0) by (clear - Frα; fsetdec).
  assert (Hαα0 : α <> α0) by (clear - Frα; fsetdec).
  assert (HαP0 : α `notin` ftvar_in_pskl P0) by (clear - Frα; fsetdec).
  assert (HβΞ : β `notin` dom Ξ) by (clear - Frβ; fsetdec).
  assert (HβΘ0 : β `notin` dom Θ0) by (clear - Frβ; fsetdec).
  assert (Hβα0 : β <> α0) by (clear - Frβ; fsetdec).
  assert (HβP0 : β `notin` ftvar_in_pskl P0) by (clear - Frβ; fsetdec).
  assert (Hα0Ξ : α0 `notin` dom Ξ) by (clear - Hα0ΞΘ0; fsetdec).
  assert (Hα0Θ0 : α0 `notin` dom Θ0) by (clear - Hα0ΞΘ0; fsetdec).
  clear Frα Frβ.
  (* ---- 5. the paper's θs ---- *)
  assert (Hincα : ((α, τ1) :: κ2) ∷ ((α ~ abind_flex_mono) ++ Θ0) ⊑ Θ)
    by (apply a_inc__flex; [ exact Hincκ2 | exact Hwf1 | exact Hm1 ]).
  assert (Hincβ : ((β, τ2) :: (α, τ1) :: κ2)
            ∷ ((β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0) ⊑ Θ)
    by (apply a_inc__flex; [ exact Hincα | exact Hwf2 | exact Hm2 ]).
  assert (Hincα0 : ((α0, τ) :: (β, τ2) :: (α, τ1) :: κ2)
            ∷ ((α0 ~ abind_flex_mono_def
                       (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
               ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0) ⊑ Θ).
  { apply a_inc__flex_def; [ exact Hincβ | exact Hwfτ | exact Hmτ | ].
    cbn.
    match goal with
    | |- context [if ?t then _ else _] => destruct t as [e | _]
    end; [ exfalso; apply Hαβ; exact e | ].
    match goal with
    | |- context [if ?t then _ else _] => destruct t as [_ | n0]
    end; [ | exfalso; apply n0; reflexivity ].
    match goal with
    | |- context [if ?t then _ else _] => destruct t as [_ | n0]
    end; [ exact Hτarr | exfalso; apply n0; reflexivity ]. }
  assert (Hincθs : (κ1 ++ (α0, τ) :: (β, τ2) :: (α, τ1) :: κ2)
            ∷ (Ξ ++ (α0 ~ abind_flex_mono_def
                          (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
                 ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0) ⊑ Θ).
  { eapply a_inc_attach_decls_prefix;
      [ exact HdeclsΞ | rewrite <- Heqκ; exact Hinc | exact Hlen
      | exact Hincα0 ]. }
  (* ---- 6. the new source context is well formed ---- *)
  assert (HwfΘb : a_wf_aenv
            ((α0 ~ abind_flex_mono_def
                     (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
             ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0)).
  { assert (Hα0b : α0 `notin` dom ((β ~ abind_flex_mono)
                                   ++ (α ~ abind_flex_mono) ++ Θ0)).
    { simpl_env. clear - Hβα0 Hαα0 Hα0Θ0. fsetdec. }
    apply a_wf_aenv__flex_def; [ exact Hα0b | | | ].
    - apply a_wf_ptyp__arrow; apply a_wf_ptyp__var; right; left;
        unfold binds; simpl; auto.
    - apply mono_ptyp__arrow; apply mono_ptyp__var.
    - apply a_wf_aenv__flex;
        [ simpl_env; clear - Hαβ HβΘ0; fsetdec | ].
      apply a_wf_aenv__flex;
        [ clear - HαΘ0; fsetdec | exact HwfΘ0 ]. }
  assert (HwfΘsrc : a_wf_aenv
            (Ξ ++ (α0 ~ abind_flex_mono_def
                          (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
               ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0)).
  { eapply a_wf_aenv_replace_decls_tail;
      [ exact HdeclsΞ | exact Hwf | exact HwfΘb | ].
    intros x Hx. simpl_env.
    assert (hx0 : x `notin` dom ((α0 ~ abind_flex_mono) ++ Θ0)).
    { clear - Huq Hx. simpl_env in Huq. destruct_uniq.
      unfold disjoint in *. simpl_env in *. fsetdec. }
    simpl_env in hx0.
    assert (hxα : x <> α) by (intro Hc; subst; clear - HαΞ Hx; fsetdec).
    assert (hxβ : x <> β) by (intro Hc; subst; clear - HβΞ Hx; fsetdec).
    clear - hx0 hxα hxβ. fsetdec. }
  (* ---- 7. the remaining premises of the P7b IH ---- *)
  assert (Hmoveb : forall γ,
            a_binds_tvar γ (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0) ->
            a_binds_tvar γ
              (Ξ ++ (α0 ~ abind_flex_mono_def
                            (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
                 ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0)).
  { intros γ Hb. destruct (γ == α0) as [-> | Hne].
    - right; right.
      exists (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)).
      unfold binds; apply in_or_app; right; simpl; left; reflexivity.
    - destruct Hb as [hb | [hb | [τz hb]]];
        [ left | right; left | right; right; exists τz ];
        (eapply binds_insert_two_mid; [ exact hb | exact Hne ]). }
  assert (HwfP0src : (Ξ ++ (α0 ~ abind_flex_mono_def
                                  (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
                        ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono)
                        ++ Θ0) ⨟ empty ⊢ₚₛᵃ P0)
    by (eapply a_wf_pskl_weaken_tvarish; [ exact HwfP0 | exact Hmoveb ]).

  assert (HwfSsrc : (Ξ ++ (α0 ~ abind_flex_mono_def
                                 (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
                       ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono)
                       ++ Θ0) ⨟ empty ⊢ₚₛᵃ
                      (pskl_arrow (pskl_var_f α) (pskl_var_f β))).
  { apply a_wf_pskl__arrow; apply a_wf_pskl__var; right; right; left;
      unfold binds; apply in_or_app; right; simpl;
      [ right; right; left; reflexivity | right; left; reflexivity ]. }
  assert (HeqR : ⌊ uskl_arrow (uskl_var_f α) (uskl_var_f β) ⌋ˢ
                 = pskl_arrow (pskl_var_f α) (pskl_var_f β)) by reflexivity.
  (* the lookups of the deposited pair *)
  assert (Hlkα : msubst_lookup
            (κ1 ++ (α0, τ) :: (β, τ2) :: (α, τ1) :: κ2) α = τ1).
  { assert (hn : α `notin` dom κ1) by (rewrite Hdomκ1; exact HαΞ).
    rewrite (@msubst_lookup_app_notin κ1 _ α hn). simpl.
    destruct (α == α0) as [e | _]; [ exfalso; apply Hαα0; exact e | ].
    destruct (α == β) as [e | _]; [ exfalso; apply Hαβ; exact e | ].
    destruct (α == α) as [_ | n0]; [ reflexivity | exfalso; apply n0; auto ]. }
  assert (Hlkβ : msubst_lookup
            (κ1 ++ (α0, τ) :: (β, τ2) :: (α, τ1) :: κ2) β = τ2).
  { assert (hn : β `notin` dom κ1) by (rewrite Hdomκ1; exact HβΞ).
    rewrite (@msubst_lookup_app_notin κ1 _ β hn). simpl.
    destruct (β == α0) as [e | _]; [ exfalso; apply Hβα0; exact e | ].
    destruct (β == β) as [_ | n0]; [ reflexivity | exfalso; apply n0; auto ]. }
  assert (Hslack' : Θ ⊢ (ptyp_to_uskl_syn τ')
            ≡ᵘ (msubst_uskl_syn (κ1 ++ (α0, τ) :: (β, τ2) :: (α, τ1) :: κ2)
                  (uskl_arrow (uskl_var_f α) (uskl_var_f β)))).
  { cbn [msubst_uskl_syn]. rewrite Hlkα, Hlkβ.
    change (uskl_arrow (ptyp_to_uskl_syn τ1) (ptyp_to_uskl_syn τ2))
      with (ptyp_to_uskl_syn (ptyp_arrow τ1 τ2)).
    apply a_uskl_tyequiv__mono;
      [ exact Hmτ' | apply mono_ptyp__arrow; assumption
      | exact Hwfτ' | apply a_wf_ptyp__arrow; assumption
      | exact Heqarr ]. }
  assert (Hrs' : ad_refine_syn_f empty Θ empty
            (pskl_to_bskl_inh (msubst_pskl
               (κ1 ++ (α0, τ) :: (β, τ2) :: (α, τ1) :: κ2) P0)) Q).
  { assert (Heq : msubst_pskl (κ1 ++ (α0, τ) :: (β, τ2) :: (α, τ1) :: κ2) P0
                = msubst_pskl κ P0).
    { rewrite Heqκ. apply msubst_pskl_agree. intros γ Hγ.
      apply msubst_lookup_insert2;
        [ intro Hc; subst; contradiction | intro Hc; subst; contradiction ]. }
    rewrite Heq. exact Hrs. }
  (* ---- 8. the P7b IH on the deposited problem.  Its motive premise: the
     subject IS a monotype painting, ghost-free outright. ---- *)
  assert (Hgf' : NM = a_sub_mode_ty -> uskl_ghost_free (ptyp_to_uskl_syn τ'))
    by (intros _; apply mono_ptyp_to_uskl_syn_ghost_free; exact Hmτ').
  destruct (IH NM (mode_fn M)
              (Ξ ++ (α0 ~ abind_flex_mono_def
                            (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
                 ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0)
              P0 (pskl_arrow (pskl_var_f α) (pskl_var_f β))
              (uskl_var_f α) (uskl_var_f β)
              (ptyp_to_uskl_syn τ') Ψ Θ
              (κ1 ++ (α0, τ) :: (β, τ2) :: (α, τ1) :: κ2) Q
              HwfΘsrc Hwfth HwfP0src HwfSsrc HmodSK HmodTY HeqR Hincθs
              Hslack' HD Hrs' HwfQ Hgf')
    as [P1 [Θ1 [Hrun Hopt]]].
  (* ---- 9. the run — NO junk swap: Flex-Solve does not re-attach ---- *)
  exists P1, Θ1. split.
  { apply a_sub_flex__solve with (α := α) (β := β);
      [ exact Hαβ
      | simpl_env; clear - HαΞ HαΘ0 Hαα0; fsetdec
      | simpl_env; clear - HβΞ HβΘ0 Hβα0; fsetdec
      | exact Hrun ]. }

  (* ---- 10. the package: the paper's ⓖ+⑫ ⇒ ⑭ collapse ---- *)
  intros κf Hidf Hincf.
  destruct (a_sub_sound_thm Hrun HwfΘsrc HwfP0src HwfSsrc HmodSK HmodTY)
    as [[[w [Hidw Hincw]] _] [HwfΘ1 _]].
  destruct (Hopt w Hidw Hincw) as [ζ [Hζ [Hie Hprec]]].
  exists ζ. split; [ exact Hζ | ]. split; [ | exact Hprec ].
  (* peel the deposited block out of the run's identity witness … *)
  destruct (@a_inc_strip_flex_def_mid Ξ α0
              (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β))
              ((β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0)
              w Θ1 HdeclsΞ Hincw)
    as [w1 [τw [w2 [Heqw [Hlenw [_ [Hw12 [_ [_ [_ _]]]]]]]]]].
  destruct (@a_inc_strip_flex_mid Ξ β ((α ~ abind_flex_mono) ++ Θ0)
              (w1 ++ w2) Θ1 HdeclsΞ Hw12)
    as [wa [τwb [wb [Heqwab [Hlenwa [_ [Hwab [_ [_ _]]]]]]]]].
  assert (Hl1 : length w1 = length wa) by (rewrite Hlenw, Hlenwa; reflexivity).
  destruct (app_split_by_head_length w1 w2 wa ((β, τwb) :: wb) Heqwab Hl1)
    as [Heqw1 Heqw2].
  subst wa. subst w2.
  destruct (@a_inc_strip_flex_mid Ξ α Θ0 (w1 ++ wb) Θ1 HdeclsΞ Hwab)
    as [wc [τwa [wd [Heqwcd [Hlenwc [_ [Hwcd [_ [_ _]]]]]]]]].
  assert (Hl2 : length w1 = length wc) by (rewrite Hlenw, Hlenwc; reflexivity).
  destruct (app_split_by_head_length w1 wb wc ((α, τwa) :: wd) Heqwcd Hl2)
    as [Heqw1' Heqwb].
  subst wc. subst wb.
  (* … and out of the conclusion's, then identify the two by uniqueness *)
  destruct (@a_inc_strip_flex_mid Ξ α0 Θ0 κf Θ1 HdeclsΞ Hincf)
    as [κf1 [τf [κf2 [Heqκf [Hlenf [_ [Hκf12 [_ [_ _]]]]]]]]].
  assert (Hidw' : is_id_msubst (w1 ++ wd)).
  { unfold is_id_msubst in *. rewrite Heqw in Hidw.
    apply Forall_app in Hidw. destruct Hidw as [h1 h2].
    inversion h2 as [| e0 l0 he0 hl0]; subst.
    inversion hl0 as [| e1 l1 he1 hl1]; subst.
    inversion hl1 as [| e2 l2 he2 hl2]; subst.
    apply Forall_app; split; assumption. }
  assert (Hidf' : is_id_msubst (κf1 ++ κf2)).
  { unfold is_id_msubst in *. rewrite Heqκf in Hidf.
    apply Forall_app in Hidf. destruct Hidf as [h1 h2].
    inversion h2; subst. apply Forall_app; split; assumption. }
  assert (Heqid : w1 ++ wd = κf1 ++ κf2)
    by (eapply is_id_inc_unique;
        [ exact Hwcd | exact Hidw' | exact Hκf12 | exact Hidf' ]).
  assert (Hl3 : length w1 = length κf1) by (rewrite Hlenw, Hlenf; reflexivity).
  destruct (app_split_by_head_length w1 wd κf1 κf2 Heqid Hl3)
    as [Heqf1 Heqf2].
  subst κf1. subst κf2.
  (* the identity's images *)
  assert (Heqτw : τw = ptyp_var_f α0 /\ τwb = ptyp_var_f β
                  /\ τwa = ptyp_var_f α).
  { unfold is_id_msubst in Hidw. rewrite Heqw in Hidw.
    apply Forall_app in Hidw. destruct Hidw as [_ h2].
    inversion h2 as [| e0 l0 he0 hl0]; subst.
    inversion hl0 as [| e1 l1 he1 hl1]; subst.
    inversion hl1 as [| e2 l2 he2 hl2]; subst.
    unfold is_id_entry in he0, he1, he2; simpl in he0, he1, he2.
    repeat split; assumption. }
  destruct Heqτw as [-> [-> ->]].
  assert (Heqτf : τf = ptyp_var_f α0).
  { unfold is_id_msubst in Hidf. rewrite Heqκf in Hidf.
    apply Forall_app in Hidf. destruct Hidf as [_ h2].
    inversion h2 as [| e0 l0 he0 hl0]; subst.
    unfold is_id_entry in he0; simpl in he0. exact he0. }
  subst τf.
  (* both composites split along the same prefix *)
  assert (Hsplitw : msubst_compose ζ
            (w1 ++ (α0, ptyp_var_f α0) :: (β, ptyp_var_f β)
                :: (α, ptyp_var_f α) :: wd)
          = msubst_compose ζ w1
            ++ (α0, msubst_ptyp ζ (ptyp_var_f α0))
            :: (β, msubst_ptyp ζ (ptyp_var_f β))
            :: (α, msubst_ptyp ζ (ptyp_var_f α))
            :: msubst_compose ζ wd)
    by (unfold msubst_compose; rewrite List.map_app; reflexivity).
  assert (Hsplitf : msubst_compose ζ (w1 ++ (α0, ptyp_var_f α0) :: wd)
          = msubst_compose ζ w1
            ++ (α0, msubst_ptyp ζ (ptyp_var_f α0)) :: msubst_compose ζ wd)
    by (unfold msubst_compose; rewrite List.map_app; reflexivity).
  rewrite Heqκ, Heqκf, Hsplitf.
  rewrite Heqw, Hsplitw in Hie.
  eapply a_inc_equiv_collapse_solve;
    [ exact HdeclsΞ | exact Hlen
    | unfold msubst_compose; rewrite List.map_length; exact Hlenw
    | exact Hie ].
Qed.


(* ===================================================================== *)
(*  (L0)  THE ⇓-CONFINEMENT — a MONOTYPE subject scopes the counterpart    *)
(*                                                                        *)
(*  [Flex-SkipRigid] must run its IH at the truncation Θ' that             *)
(*  [a_inc_tvar_inv] hands back, so every solution-side premise has to     *)
(*  move to a sub-context — and §(L)'s three strengthenings all take       *)
(*  [ftv Q ⊆ dom Θ'] as a HYPOTHESIS.  That is NOT derivable of [Q]        *)
(*  itself: [ad_pat_consis__flex_r] and [ad_refine_syn_f__flex_r] let the  *)
(*  counterpart be an arbitrary DEFINED flexible of Θ, so [Q] may name one *)
(*  of the junk block sitting ABOVE β.  It IS derivable of [⇓ᵇ[Θ] Q],      *)
(*  which unfolds exactly those — which is why the consistency walk        *)
(*  normalizes before it truncates.                                       *)
(*                                                                        *)
(*  These two lemmas are the MIRROR of [join_pskl_downarrow_mono_scoped]   *)
(*  (prop_consis_complete.v): there the monotype is the COUNTERPART and    *)
(*  the ⇓ of the SUBJECT is scoped; here — the flexible subtyping walk's   *)
(*  subject is [syn{κα̂}] — the monotype is the SUBJECT and the ⇓ of the    *)
(*  COUNTERPART is scoped.  Same induction, same def-closed [D].           *)
(*                                                                        *)
(*  (The [ad_pat_consis] half would sit just as well next to its mirror in *)
(*  prop_consis_complete.v; it lives here because P7a is its only          *)
(*  consumer.)                                                            *)
(* ===================================================================== *)

Notation "⇓ᵇ[ Θ ] Q" := (msubst_bskl (aenv_msubst Θ) Q)
  (at level 5, Θ at level 0) : type_scope.

(** The syn painting commutes with a metasubstitution. *)
Lemma msubst_bskl_ptyp_to_bskl_syn : forall κ A,
  msubst_bskl κ (ptyp_to_bskl_syn A) = ptyp_to_bskl_syn (msubst_ptyp κ A).
Proof.
  intros κ A. unfold ptyp_to_bskl_syn.
  induction A; simpl; try reflexivity.
  - rewrite IHA1, IHA2. reflexivity.
  - rewrite IHA. reflexivity.
Qed.

Lemma ftvar_in_bskl_ptyp_to_bskl_syn : forall A,
  ftvar_in_bskl (ptyp_to_bskl_syn A) [=] ftvar_in_ptyp A.
Proof.
  intros A. unfold ptyp_to_bskl_syn.
  rewrite ftvar_in_bskl_syn. apply ftvar_in_ptyp_to_pskl.
Qed.

(** THE MIRROR.  [join_pskl_downarrow_mono_scoped] scopes the ⇓ of the
    SUBJECT from a monotype COUNTERPART; the flexible SUBTYPING walk needs the
    other side — its join carries the monotype on the SUBJECT (the subject is
    [syn{κα̂}]) and the counterpart [Q] is free.  Same induction, same
    def-closed [D]: every rule either pins [Q] to the subject's variables
    ([__var]), recurses ([__arrow]), chases a definition ([__flex_l] /
    [__flex_r] — which is what ⇓ unfolds), or is excluded because a monotype
    painting is never a ∀, a hole, or a tophole.

    ⚙ The hypothesis is stated on [⇓ᵗ[Θ] A], not on [A].  That is both more
    GENERAL (with a def-closed [D], [ftv A ⊆ D] gives it by
    [downarrow_ftv_closed]) and what the consumer actually has: the walk knows
    its subject only up to [≡ᵗ], and [≡ᵗ] does not preserve ftv-scoping — but
    it does preserve ⇓ ([a_tyequiv_downarrow]).  It also makes the
    def-closedness side condition unnecessary: the two definition-chasing rows
    now discharge it by [aenv_msubst_lookup_def] alone. *)
Lemma consis_bskl_downarrow_mono_scoped : forall Ψ Θ R Q,
  Ψ ⨟ Θ ⊢ₛᵃ R ∼ Q ->
  a_wf_aenv Θ ->
  forall A D,
    R = ptyp_to_uskl_syn A -> mono_ptyp A ->
    ftvar_in_ptyp (⇓ᵗ[ Θ ] A) [<=] D ->
    ftvar_in_bskl (⇓ᵇ[ Θ ] Q) [<=] D.
Proof.
  intros Ψ Θ R Q Hc Hwf; induction Hc; intros A0 D HeqR HmA HAD;
    unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in HeqR.
  - (* unit *)
    destruct A0; cbn in HeqR; try discriminate HeqR.
    simpl. clear; fsetdec.
  - (* var : the counterpart IS the subject's variable *)
    destruct A0; cbn in HeqR; try discriminate HeqR.
    inversion HeqR; subst. simpl.
    rewrite ftvar_in_bskl_syn. rewrite ftvar_in_ptyp_to_pskl.
    simpl in HAD. exact HAD.
  - (* arrow *)
    destruct A0 as [ | nb | γ0 | A1 A2 | A0' ];
      cbn in HeqR; try discriminate HeqR; try solve [ inversion HmA ].
    inversion HeqR; subst. inversion HmA; subst.
    simpl in HAD |- *. intros γ Hγ. apply union_1 in Hγ.
    destruct Hγ as [h | h].
    + refine (IHHc1 Hwf A1 D eq_refl _ _ γ h);
        [ assumption | clear - HAD; fsetdec ].
    + refine (IHHc2 Hwf A2 D eq_refl _ _ γ h);
        [ assumption | clear - HAD; fsetdec ].
  - (* forall_inh_tagged : a mono painting is never a ∀ *)
    destruct A0; cbn in HeqR; try discriminate HeqR; inversion HmA.
  - (* forall_inh_untagged *)
    destruct A0; cbn in HeqR; try discriminate HeqR; inversion HmA.
  - (* forall_syn_tagged *)
    destruct A0; cbn in HeqR; try discriminate HeqR; inversion HmA.
  - (* forall_syn *)
    destruct A0; cbn in HeqR; try discriminate HeqR; inversion HmA.
  - (* ghostg : the subject is a ghost *)
    destruct A0; cbn in HeqR; try discriminate HeqR.
  - (* topholeg *)
    destruct A0; cbn in HeqR; try discriminate HeqR.
  - (* hole *)
    destruct A0; cbn in HeqR; try discriminate HeqR.
  - (* tophole *)
    destruct A0; cbn in HeqR; try discriminate HeqR.
  - (* tophole_inh *)
    destruct A0; cbn in HeqR; try discriminate HeqR.
  - (* tophole_drop *)
    destruct A0; cbn in HeqR; try discriminate HeqR.
  - (* flex_l : the SUBJECT is a defined flexible — ⇓ has already chased it.
       [inversion] renames the rule's own variable, so the lookup fact is
       picked out of the goal rather than named. *)
    destruct A0; cbn in HeqR; try discriminate HeqR.
    inversion HeqR; subst.
    assert (Hmτ : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; eauto).
    simpl in HAD.
    match goal with
    | Hb : binds ?g (abind_flex_mono_def τ) Θ |- _ =>
        assert (Hlk : msubst_lookup (aenv_msubst Θ) g = ⇓ᵗ[ Θ ] τ)
          by (apply aenv_msubst_lookup_def; assumption)
    end.
    rewrite Hlk in HAD.
    exact (IHHc Hwf τ D eq_refl Hmτ HAD).
  - (* flex_r : the COUNTERPART is a defined flexible — ⇓ unfolds it.  The
       subject is untouched, so [A0] must NOT be destructed here. *)
    simpl.
    assert (Hlk : msubst_lookup (aenv_msubst Θ) α = ⇓ᵗ[ Θ ] τ)
      by (apply aenv_msubst_lookup_def; assumption).
    rewrite Hlk.
    pose proof (IHHc Hwf A0 D HeqR HmA HAD) as IH.
    rewrite msubst_bskl_ptyp_to_bskl_syn in IH.
    rewrite ftvar_in_bskl_ptyp_to_bskl_syn in IH.
    rewrite ftvar_in_bskl_syn. rewrite ftvar_in_ptyp_to_pskl.
    exact IH.
Qed.

(* --------------------------------------------------------------------- *)
(*  Plumbing the ∀R case of the mirror needs                              *)
(* --------------------------------------------------------------------- *)

(** A rigid entry contributes no definition, so ⇓ ignores it. *)
Lemma aenv_msubst_tvar_cons : forall (α : atom) Θ,
  aenv_msubst ((α ~ abind_tvar) ++ Θ) = aenv_msubst Θ.
Proof. reflexivity. Qed.

(** Opening only ADDS free variables, even under a metasubstitution. *)
Lemma msubst_bskl_open_rec_ftv_lower : forall κ B B' k,
  ftvar_in_bskl (msubst_bskl κ B)
    [<=] ftvar_in_bskl (msubst_bskl κ (open_bskl_wrt_bskl_rec k B' B)).
Proof.
  intros κ B; induction B; intros B' k; simpl.
  - (* unit *) clear; fsetdec.
  - (* var_b *)
    destruct (lt_eq_lt_dec n k) as [[? | ?] | ?]; simpl; clear; fsetdec.
  - (* var_f *) clear; fsetdec.
  - (* arrow *)
    specialize (IHB1 B' k). specialize (IHB2 B' k).
    clear - IHB1 IHB2; fsetdec.
  - (* all_syn *) apply (IHB B' (S k)).
  - (* all_inh *) apply (IHB B' (S k)).
  - (* hole *) clear; fsetdec.
  - (* tophole *) apply (IHB B' k).
Qed.

Corollary msubst_bskl_open_ftv_lower : forall κ B B',
  ftvar_in_bskl (msubst_bskl κ B)
    [<=] ftvar_in_bskl (msubst_bskl κ (open_bskl_wrt_bskl B B')).
Proof. intros. apply msubst_bskl_open_rec_ftv_lower. Qed.

(** The bskl twin of [msubst_pskl_ftv_fresh]. *)
Lemma msubst_bskl_ftv_fresh : forall (Θ : aenv) κ Q β,
  (forall α, ftvar_in_ptyp (msubst_lookup κ α) [<=] add α (dom Θ)) ->
  β `notin` ftvar_in_bskl Q ->
  β `notin` dom Θ ->
  β `notin` ftvar_in_bskl (msubst_bskl κ Q).
Proof.
  intros Θ κ Q β Hsc; revert Q;
    induction Q; intros HβQ HβΘ; cbn in *; try solve [ clear; fsetdec ].
  - (* var_f *)
    rewrite ftvar_in_bskl_syn. rewrite ftvar_in_ptyp_to_pskl.
    specialize (Hsc α). clear - Hsc HβQ HβΘ; fsetdec.
  - (* arrow *)
    specialize (IHQ1 ltac:(clear - HβQ; fsetdec) HβΘ).
    specialize (IHQ2 ltac:(clear - HβQ; fsetdec) HβΘ).
    clear - IHQ1 IHQ2; fsetdec.
  - apply IHQ; assumption.
  - apply IHQ; assumption.
  - apply IHQ; assumption.
Qed.

(** ⇓'s images stay inside the context (plus the variable itself, when it is
    not in the map at all). *)
Lemma aenv_msubst_image_dom : forall Θ,
  a_wf_aenv Θ ->
  forall α, ftvar_in_ptyp (msubst_lookup (aenv_msubst Θ) α) [<=] add α (dom Θ).
Proof.
  intros Θ Hwf α.
  destruct (AtomSetProperties.In_dec α (dom (aenv_msubst Θ))) as [Hin | Hni].
  - assert (Hbt : a_binds_tvar α Θ)
      by (right; apply aenv_msubst_dom_inv; exact Hin).
    pose proof (aenv_msubst_image_wf Hwf Hbt) as Hw.
    apply a_wf_ptyp_ftv_dom in Hw. clear - Hw; fsetdec.
  - rewrite (msubst_lookup_notin _ Hni). simpl. clear; fsetdec.
Qed.

(** ⇓-NORMALIZING THE JOIN'S CONSISTENCY LEAVES.  The confinement above scopes
    [⇓ᵇ Q]; to USE it, the leaf must actually hold at the normalized pair.  At
    a MONOTYPE-painting subject only five rows of [ad_pat_consis] are
    reachable — unit, var, arrow and the two definition chases — and ⇓ is the
    identity on the first three and exactly the chase on the last two, so the
    normalized leaf is the same derivation with the definitions already
    resolved. *)
Lemma consis_downarrow_mono : forall Ψ Θ R Q,
  Ψ ⨟ Θ ⊢ₛᵃ R ∼ Q ->
  a_wf_aenv Θ ->
  forall A, R = ptyp_to_uskl_syn A -> mono_ptyp A -> a_wf_ptyp Θ A ->
  Ψ ⨟ Θ ⊢ₛᵃ (ptyp_to_uskl_syn (⇓ᵗ[ Θ ] A)) ∼ (⇓ᵇ[ Θ ] Q).
Proof.
  intros Ψ Θ R Q Hc Hwf; induction Hc; intros A0 HeqR HmA HwfA;
    unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in HeqR.
  - (* unit *)
    destruct A0; cbn in HeqR; try discriminate HeqR.
    simpl. apply ad_pat_consis__unit; assumption.
  - (* var : both sides ⇓ to the SAME monotype, so this is reflexivity *)
    destruct A0 as [ | nb | γ0 | A1 A2 | A0' ];
      cbn in HeqR; try discriminate HeqR.
    inversion HeqR as [Heqv]. subst γ0.
    assert (Hmd : mono_ptyp (⇓ᵗ[ Θ ] (ptyp_var_f α)))
      by (apply mono_downarrow; [ exact Hwf | exact HwfA | exact HmA ]).
    assert (Hwfd : a_wf_ptyp Θ (⇓ᵗ[ Θ ] (ptyp_var_f α)))
      by (apply a_wf_ptyp_downarrow_mono;
          [ exact Hwf | exact HwfA | exact HmA ]).
    assert (Hvis : forall γ, γ `in` ftvar_in_ptyp (⇓ᵗ[ Θ ] (ptyp_var_f α)) ->
                     a_binds_tvar γ Θ)
      by (intros γ Hγ; eapply a_wf_ptyp_ftv_tvarish; [ exact Hwfd | exact Hγ ]).
    change (⇓ᵇ[ Θ ] (bskl_var_f α))
      with (ptyp_to_bskl_syn (⇓ᵗ[ Θ ] (ptyp_var_f α))).
    eapply ad_pat_consis_psi_cong;
      [ apply consis_mono_refl; [ exact Hmd | exact Hvis ] | fsetdec ].
  - (* arrow *)
    destruct A0 as [ | nb | γ0 | A1 A2 | A0' ];
      cbn in HeqR; try discriminate HeqR; try solve [ inversion HmA ].
    inversion HeqR; subst. inversion HmA; subst. inversion HwfA; subst.
    simpl. apply ad_pat_consis__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
      [ apply (IHHc1 Hwf A1 eq_refl ltac:(assumption) ltac:(assumption))
      | apply (IHHc2 Hwf A2 eq_refl ltac:(assumption) ltac:(assumption))
      | exact H ].
  - (* forall_inh_tagged *)
    destruct A0; cbn in HeqR; try discriminate HeqR; inversion HmA.
  - (* forall_inh_untagged *)
    destruct A0; cbn in HeqR; try discriminate HeqR; inversion HmA.
  - (* forall_syn_tagged *)
    destruct A0; cbn in HeqR; try discriminate HeqR; inversion HmA.
  - (* forall_syn *)
    destruct A0; cbn in HeqR; try discriminate HeqR; inversion HmA.
  - (* ghostg *) destruct A0; cbn in HeqR; try discriminate HeqR.
  - (* topholeg *) destruct A0; cbn in HeqR; try discriminate HeqR.
  - (* hole *) destruct A0; cbn in HeqR; try discriminate HeqR.
  - (* tophole *) destruct A0; cbn in HeqR; try discriminate HeqR.
  - (* tophole_inh *) destruct A0; cbn in HeqR; try discriminate HeqR.
  - (* tophole_drop *) destruct A0; cbn in HeqR; try discriminate HeqR.
  - (* flex_l : ⇓ has already chased the subject's definition *)
    destruct A0 as [ | nb | γ0 | A1 A2 | A0' ];
      cbn in HeqR; try discriminate HeqR.
    inversion HeqR as [Heqv]. subst γ0.
    assert (Hmτ : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; eauto).
    assert (Hwfτ : a_wf_ptyp Θ τ)
      by (eapply a_wf_aenv_binds_def_wf; eauto).
    assert (Hlk : msubst_lookup (aenv_msubst Θ) α = ⇓ᵗ[ Θ ] τ)
      by (apply aenv_msubst_lookup_def; assumption).
    replace (⇓ᵗ[ Θ ] (ptyp_var_f α)) with (⇓ᵗ[ Θ ] τ)
      by (symmetry; exact Hlk).
    exact (IHHc Hwf τ eq_refl Hmτ Hwfτ).
  - (* flex_r : ⇓ has already chased the counterpart's definition *)
    simpl.
    assert (Hlk : msubst_lookup (aenv_msubst Θ) α = ⇓ᵗ[ Θ ] τ)
      by (apply aenv_msubst_lookup_def; assumption).
    rewrite Hlk.
    pose proof (IHHc Hwf A0 HeqR HmA HwfA) as IH.
    rewrite msubst_bskl_ptyp_to_bskl_syn in IH.
    exact IH.
Qed.

(** Erasure commutes with a metasubstitution (the join's leaves state their
    refinement on [⌊·⌋ˢ] / [bskl_to_pskl], so ⇓ has to pass through both). *)
Lemma bskl_to_pskl_msubst_bskl : forall κ Q,
  bskl_to_pskl (msubst_bskl κ Q) = msubst_pskl κ (bskl_to_pskl Q).
Proof.
  intros κ Q; induction Q; simpl; try reflexivity.
  - rewrite bskl_to_pskl_pskl_to_bskl_syn. reflexivity.
  - rewrite IHQ1, IHQ2. reflexivity.
  - rewrite IHQ. reflexivity.
  - rewrite IHQ. reflexivity.
  - rewrite IHQ. reflexivity.
Qed.

(** ⇓-NORMALIZING THE REFINEMENT LEAF.  Same five reachable rows as
    [consis_downarrow_mono], for the same reason: at a monotype source the
    ∀ / hole / tophole rows cannot fire. *)
Lemma refine_pskl_downarrow_mono : forall Θ Δ P Q,
  Θ ⨟ Δ ⊢ᵣₚᵃ P ⊳ Q ->
  a_wf_aenv Θ ->
  forall A, P = ptyp_to_pskl A -> mono_ptyp A -> a_wf_ptyp Θ A ->
  Θ ⨟ Δ ⊢ᵣₚᵃ (⇓ˢ[ Θ ] P) ⊳ (⇓ˢ[ Θ ] Q).
Proof.
  intros Θ Δ P Q Hr Hwf; induction Hr; intros A0 HeqP HmA HwfA.
  - (* unit *)
    destruct A0; cbn in HeqP; try discriminate HeqP.
    simpl. apply ad_refine_pskl__unit.
  - (* var : ⇓ of a visible variable is a wf monotype, and refinement is
       reflexive there *)
    destruct A0 as [ | nb | γ0 | A1 A2 | A0' ];
      cbn in HeqP; try discriminate HeqP.
    inversion HeqP as [Heqv]. subst γ0.
    assert (Hmd : mono_ptyp (⇓ᵗ[ Θ ] (ptyp_var_f α)))
      by (apply mono_downarrow; [ exact Hwf | exact HwfA | exact HmA ]).
    assert (Hwfd : a_wf_ptyp Θ (⇓ᵗ[ Θ ] (ptyp_var_f α)))
      by (apply a_wf_ptyp_downarrow_mono;
          [ exact Hwf | exact HwfA | exact HmA ]).
    change (⇓ˢ[ Θ ] (pskl_var_f α))
      with (ptyp_to_pskl (⇓ᵗ[ Θ ] (ptyp_var_f α))).
    apply ad_refine_pskl_f_forget with (F := empty).
    eapply ad_refine_pskl_f_mono_refl; [ exact Hmd | exact Hwfd ].
  - (* arrow *)
    destruct A0 as [ | nb | γ0 | A1 A2 | A0' ];
      cbn in HeqP; try discriminate HeqP; try solve [ inversion HmA ].
    inversion HeqP; subst. inversion HmA; subst. inversion HwfA; subst.
    simpl. apply ad_refine_pskl__arrow;
      [ apply (IHHr1 Hwf A1 eq_refl ltac:(assumption) ltac:(assumption))
      | apply (IHHr2 Hwf A2 eq_refl ltac:(assumption) ltac:(assumption)) ].
  - (* all *)
    destruct A0; cbn in HeqP; try discriminate HeqP; inversion HmA.
  - (* hole *)
    destruct A0; cbn in HeqP; try discriminate HeqP.
  - (* tophole_remove *)
    destruct A0; cbn in HeqP; try discriminate HeqP.
  - (* tophole_fill *)
    destruct A0; cbn in HeqP; try discriminate HeqP.
  - (* tophole_keep *)
    destruct A0; cbn in HeqP; try discriminate HeqP.
  - (* flex_l : ⇓ has already chased the source's definition *)
    destruct A0 as [ | nb | γ0 | A1 A2 | A0' ];
      cbn in HeqP; try discriminate HeqP.
    inversion HeqP as [Heqv]. subst γ0.
    assert (Hmτ : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; eauto).
    assert (Hwfτ : a_wf_ptyp Θ τ)
      by (eapply a_wf_aenv_binds_def_wf; eauto).
    assert (Hlk : msubst_lookup (aenv_msubst Θ) α = ⇓ᵗ[ Θ ] τ)
      by (apply aenv_msubst_lookup_def; assumption).
    change (⇓ˢ[ Θ ] (pskl_var_f α))
      with (ptyp_to_pskl (msubst_lookup (aenv_msubst Θ) α)).
    rewrite Hlk. rewrite <- msubst_pskl_ptyp_to_pskl.
    exact (IHHr Hwf τ eq_refl Hmτ Hwfτ).
  - (* flex_r : ⇓ has already chased the target's definition *)
    simpl.
    assert (Hlk : msubst_lookup (aenv_msubst Θ) α = ⇓ᵗ[ Θ ] τ)
      by (apply aenv_msubst_lookup_def; assumption).
    rewrite Hlk. rewrite <- msubst_pskl_ptyp_to_pskl.
    exact (IHHr Hwf A0 HeqP HmA HwfA).
Qed.

(* --------------------------------------------------------------------- *)
(*  Plumbing the JOIN's normalization needs on top of the two leaves       *)
(* --------------------------------------------------------------------- *)

(** ⇓ commutes with opening (the ForallR row opens its target under a fresh
    rigid binder).  Mirrors [msubst_pskl_open_rec_lc]. *)
Lemma msubst_bskl_open_rec_lc : forall κ,
  msubst_lc κ ->
  forall B B' k,
  msubst_bskl κ (open_bskl_wrt_bskl_rec k B' B)
  = open_bskl_wrt_bskl_rec k (msubst_bskl κ B') (msubst_bskl κ B).
Proof.
  intros κ Hlc B; induction B; intros B' k; simpl; f_equal; eauto.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
  - symmetry.
    apply open_bskl_wrt_bskl_rec_degree_bskl_wrt_bskl.
    apply degree_bskl_wrt_bskl_O.
    apply degree_bskl_wrt_bskl_of_lc_bskl.
    apply pskl_to_bskl_syn_lc. apply ptyp_to_pskl_lc. apply Hlc.
Qed.

Lemma msubst_bskl_open_lc : forall κ B (α : atom),
  msubst_lc κ ->
  α `notin` dom κ ->
  msubst_bskl κ (open_bskl_wrt_bskl B (bskl_var_f α))
  = open_bskl_wrt_bskl (msubst_bskl κ B) (bskl_var_f α).
Proof.
  intros κ B α Hlc Hα. unfold open_bskl_wrt_bskl.
  rewrite (msubst_bskl_open_rec_lc Hlc B (bskl_var_f α) 0).
  cbn [msubst_bskl]. rewrite msubst_lookup_notin by exact Hα.
  reflexivity.
Qed.

(** A monotype painting is a synthesised skeleton. *)
Lemma is_sskl_ptyp_to_bskl_syn : forall τ,
  mono_ptyp τ -> is_sskl (ptyp_to_bskl_syn τ).
Proof.
  intros τ Hm; unfold ptyp_to_bskl_syn; induction Hm; simpl;
    [ apply is_sskl__unit | apply is_sskl__var
    | apply is_sskl__arrow; assumption ].
Qed.

(** ⇓ preserves "synthesised": every variable is replaced by a MONOTYPE
    painting, which is synthesised, and no colour changes. *)
Lemma is_sskl_msubst_bskl : forall κ Q,
  msubst_lc κ ->
  (forall α, mono_ptyp (msubst_lookup κ α)) ->
  is_sskl Q -> is_sskl (msubst_bskl κ Q).
Proof.
  intros κ Q Hlc Hmono H; induction H; simpl.
  - apply is_sskl__unit.
  - change (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup κ α)))
      with (ptyp_to_bskl_syn (msubst_lookup κ α)).
    apply is_sskl_ptyp_to_bskl_syn. apply Hmono.
  - apply is_sskl__arrow; assumption.
  - apply is_sskl__all with (L := L `union` dom κ). intros α Hα.
    assert (Heq : msubst_bskl κ (open_bskl_wrt_bskl A (bskl_var_f α))
                  = open_bskl_wrt_bskl (msubst_bskl κ A) (bskl_var_f α))
      by (apply msubst_bskl_open_lc;
          [ exact Hlc | clear - Hα; fsetdec ]).
    rewrite <- Heq. apply H0. clear - Hα; fsetdec.
  - apply is_sskl__hole.
  - apply is_sskl__tophole; assumption.
Qed.

(** At a MONO-image metasubstitution the two paintings agree on the images,
    so ⇓ passes through the inh painting. *)
Lemma msubst_bskl_pskl_to_bskl_inh : forall κ P,
  (forall α, mono_ptyp (msubst_lookup κ α)) ->
  msubst_bskl κ (pskl_to_bskl_inh P) = pskl_to_bskl_inh (msubst_pskl κ P).
Proof.
  intros κ P Hmono; induction P; simpl; try reflexivity.
  - symmetry. apply mono_inh_eq_syn. apply Hmono.
  - rewrite IHP1, IHP2. reflexivity.
  - rewrite IHP. reflexivity.
  - rewrite IHP. reflexivity.
Qed.

(** Local closure survives a locally-closed metasubstitution (the [a_inc]
    form [msubst_pskl_lc] is not available at ⇓, which is not an increase). *)
Lemma msubst_pskl_lc_of_msubst_lc : forall κ P,
  msubst_lc κ -> lc_pskl P -> lc_pskl (msubst_pskl κ P).
Proof.
  intros κ P Hlc H; induction H; simpl; try solve [ constructor; auto ].
  - apply ptyp_to_pskl_lc. apply Hlc.
  - pick fresh α for (dom κ).
    apply lc_pskl_all_syn_exists with (α1 := α).
    match goal with
    | |- lc_pskl (open_pskl_wrt_pskl (msubst_pskl _ ?B) _) =>
        assert (Heq : msubst_pskl κ (open_pskl_wrt_pskl B (pskl_var_f α))
                      = open_pskl_wrt_pskl (msubst_pskl κ B) (pskl_var_f α))
          by (apply msubst_pskl_open_lc; [ exact Hlc | clear - Fr; fsetdec ])
    end.
    rewrite <- Heq. apply H0.
Qed.

(** Guardedness survives ⇓ (a monotype image is guarded). *)
Lemma guarded_pskl_msubst_mono : forall κ P,
  msubst_lc κ ->
  (forall α, mono_ptyp (msubst_lookup κ α)) ->
  guarded_pskl P -> guarded_pskl (msubst_pskl κ P).
Proof.
  intros κ P Hlc Hmono Hg; inversion Hg; subst; simpl.
  - apply guarded_pskl__unit.
  - apply mono_ptyp_to_pskl_guarded. apply Hmono.
  - apply guarded_pskl__arrow;
      apply msubst_pskl_lc_of_msubst_lc; assumption.
Qed.

(** Local closure and guardedness for the bskl side. *)
Lemma msubst_bskl_lc_of_msubst_lc : forall κ Q,
  msubst_lc κ -> lc_bskl Q -> lc_bskl (msubst_bskl κ Q).
Proof.
  intros κ Q Hlc H; induction H; simpl; try solve [ constructor; auto ].
  - apply pskl_to_bskl_syn_lc. apply ptyp_to_pskl_lc. apply Hlc.
  - pick fresh α for (dom κ).
    apply lc_bskl_all_syn_exists with (α1 := α).
    match goal with
    | |- lc_bskl (open_bskl_wrt_bskl (msubst_bskl _ ?B) _) =>
        assert (Heq : msubst_bskl κ (open_bskl_wrt_bskl B (bskl_var_f α))
                      = open_bskl_wrt_bskl (msubst_bskl κ B) (bskl_var_f α))
          by (apply msubst_bskl_open_lc; [ exact Hlc | clear - Fr; fsetdec ])
    end.
    rewrite <- Heq. apply H0.
  - pick fresh α for (dom κ).
    apply lc_bskl_all_inh_exists with (α1 := α).
    match goal with
    | |- lc_bskl (open_bskl_wrt_bskl (msubst_bskl _ ?B) _) =>
        assert (Heq : msubst_bskl κ (open_bskl_wrt_bskl B (bskl_var_f α))
                      = open_bskl_wrt_bskl (msubst_bskl κ B) (bskl_var_f α))
          by (apply msubst_bskl_open_lc; [ exact Hlc | clear - Fr; fsetdec ])
    end.
    rewrite <- Heq. apply H0.
Qed.

Lemma guarded_bskl_msubst_mono : forall κ Q,
  msubst_lc κ ->
  (forall α, mono_ptyp (msubst_lookup κ α)) ->
  guarded_bskl Q -> guarded_bskl (msubst_bskl κ Q).
Proof.
  intros κ Q Hlc Hmono Hg; inversion Hg; subst; simpl.
  - apply guarded_bskl__unit.
  - change (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup κ α)))
      with (ptyp_to_bskl_syn (msubst_lookup κ α)).
    pose proof (Hmono α) as Hm. destruct Hm; simpl;
      [ apply guarded_bskl__unit | apply guarded_bskl__var
      | apply guarded_bskl__arrow;
        apply pskl_to_bskl_syn_lc; apply ptyp_to_pskl_lc;
        apply mono_ptyp_lc; assumption ].
  - apply guarded_bskl__arrow;
      apply msubst_bskl_lc_of_msubst_lc; assumption.
Qed.

(** The syn painting of an arrow, kept FOLDED — [simpl] would unfold it and
    the erasure rewrites below match only the folded form. *)
Lemma ptyp_to_uskl_syn_arrow : forall A1 A2,
  ptyp_to_uskl_syn (ptyp_arrow A1 A2)
  = uskl_arrow (ptyp_to_uskl_syn A1) (ptyp_to_uskl_syn A2).
Proof. reflexivity. Qed.

(** ⇓-NORMALIZING THE WHOLE JOIN.  Assembles the two leaf normalizations: at
    a MONOTYPE-painting subject the reachable rows are Infer / Check /
    ForallR / UnivGhostR / Arrow / FlexMono, and each either delegates to a
    leaf, recurses, or chases a definition ⇓ has already resolved. *)
Lemma sub_gv_downarrow_mono : forall n NM M Ψ Θ R Q,
  ad_pat_sub_gv n NM M Ψ Θ R Q ->
  a_wf_aenv Θ ->
  forall A, R = ptyp_to_uskl_syn A -> mono_ptyp A -> a_wf_ptyp Θ A ->
  ad_pat_sub_gv n NM M Ψ Θ (ptyp_to_uskl_syn (⇓ᵗ[ Θ ] A)) (⇓ᵇ[ Θ ] Q).
Proof.
  intros n NM M Ψ Θ R Q H; induction H; intros Hwf A0 HeqR HmA HwfA.
  - (* infer *)
    assert (Hmd : mono_ptyp (⇓ᵗ[ Θ ] A0))
      by (apply mono_downarrow; [ exact Hwf | exact HwfA | exact HmA ]).
    apply ad_pat_sub_gv__infer;
      [ assumption
      | eapply consis_downarrow_mono;
          [ eassumption | exact Hwf | exact HeqR | exact HmA | exact HwfA ]
      | apply is_sskl_msubst_bskl;
          [ apply aenv_msubst_lc; exact Hwf
          | intros; apply aenv_msubst_image_mono; exact Hwf
          | assumption ]
      | ].
    rewrite uskl_to_pskl_ptyp_to_uskl_syn.
    rewrite bskl_to_pskl_msubst_bskl.
    rewrite <- msubst_pskl_ptyp_to_pskl.
    eapply refine_pskl_downarrow_mono;
      [ | exact Hwf | | exact HmA | exact HwfA ];
      [ rewrite <- uskl_to_pskl_ptyp_to_uskl_syn; rewrite <- HeqR;
        eassumption
      | reflexivity ].
  - (* check *)
    assert (Hmd : mono_ptyp (⇓ᵗ[ Θ ] A0))
      by (apply mono_downarrow; [ exact Hwf | exact HwfA | exact HmA ]).
    rewrite (msubst_bskl_pskl_to_bskl_inh (aenv_msubst Θ) B
               ltac:(intros; apply aenv_msubst_image_mono; exact Hwf)).
    apply ad_pat_sub_gv__check;
      [ apply guarded_ptyp_to_uskl_syn; exact Hmd
      | apply guarded_pskl_msubst_mono;
          [ apply aenv_msubst_lc; exact Hwf
          | intros; apply aenv_msubst_image_mono; exact Hwf
          | assumption ]
      | | ].
    + rewrite <- (msubst_bskl_pskl_to_bskl_inh (aenv_msubst Θ) B
                    ltac:(intros; apply aenv_msubst_image_mono; exact Hwf)).
      eapply consis_downarrow_mono;
        [ eassumption | exact Hwf | exact HeqR | exact HmA | exact HwfA ].
    + rewrite uskl_to_pskl_ptyp_to_uskl_syn.
      rewrite <- msubst_pskl_ptyp_to_pskl.
      eapply refine_pskl_downarrow_mono;
        [ | exact Hwf | | exact HmA | exact HwfA ];
        [ rewrite <- uskl_to_pskl_ptyp_to_uskl_syn; rewrite <- HeqR;
          eassumption
        | reflexivity ].
  - (* forall_r : the target's binder, under a fresh rigid entry *)
    simpl.
    apply ad_pat_sub_gv__forall_r
      with (L := L `union` dom Θ `union` dom (aenv_msubst Θ)).
    intros α Hα.
    assert (Hwf' : a_wf_aenv ((α ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ]).
    assert (HwfA' : a_wf_ptyp ((α ~ abind_tvar) ++ Θ) A0)
      by (eapply a_wf_ptyp_weaken;
          [ intros x b Hb; apply binds_cons_3; exact Hb | exact HwfA ]).
    pose proof (H0 α ltac:(clear - Hα; fsetdec) Hwf' A0 HeqR HmA HwfA') as IH.
    rewrite aenv_msubst_tvar_cons in IH.
    assert (Heq : msubst_bskl (aenv_msubst Θ)
                    (open_bskl_wrt_bskl B (bskl_var_f α))
                  = open_bskl_wrt_bskl (msubst_bskl (aenv_msubst Θ) B)
                      (bskl_var_f α))
      by (apply msubst_bskl_open_lc;
          [ apply aenv_msubst_lc; exact Hwf | clear - Hα; fsetdec ]).
    rewrite Heq in IH. exact IH.
  - (* univ_ghost_r *)
    assert (Hmd : mono_ptyp (⇓ᵗ[ Θ ] A0))
      by (apply mono_downarrow; [ exact Hwf | exact HwfA | exact HmA ]).
    simpl. apply ad_pat_sub_gv__univ_ghost_r;
      [ assumption
      | apply guarded_ptyp_to_uskl_syn; exact Hmd
      | apply guarded_bskl_msubst_mono;
          [ apply aenv_msubst_lc; exact Hwf
          | intros; apply aenv_msubst_image_mono; exact Hwf
          | assumption ]
      | apply is_sskl_msubst_bskl;
          [ apply aenv_msubst_lc; exact Hwf
          | intros; apply aenv_msubst_image_mono; exact Hwf
          | assumption ]
      | eapply consis_downarrow_mono;
          [ eassumption | exact Hwf | exact HeqR | exact HmA | exact HwfA ]
      | ].
    rewrite uskl_to_pskl_ptyp_to_uskl_syn.
    rewrite bskl_to_pskl_msubst_bskl.
    rewrite <- msubst_pskl_ptyp_to_pskl.
    eapply refine_pskl_downarrow_mono;
      [ | exact Hwf | | exact HmA | exact HwfA ];
      [ rewrite <- uskl_to_pskl_ptyp_to_uskl_syn; rewrite <- HeqR;
        eassumption
      | reflexivity ].
  - (* arrow.  The two components' equations are read off the FOLDED painting
       ([ptyp_to_uskl_syn_arrow]); [cbn]/[simpl] would unfold it and the
       erasure rewrites below would stop matching. *)
    destruct A0 as [ | nb | γ0 | A1 A2 | A0' ];
      try solve [ cbn in HeqR; discriminate HeqR ].
    assert (HR : uskl_arrow R1 R2
                 = uskl_arrow (ptyp_to_uskl_syn A1) (ptyp_to_uskl_syn A2))
      by (rewrite HeqR; reflexivity).
    injection HR as HR1 HR2. subst R1. subst R2.
    inversion HmA; subst. inversion HwfA; subst.
    replace (⇓ᵗ[ Θ ] (ptyp_arrow A1 A2))
      with (ptyp_arrow (⇓ᵗ[ Θ ] A1) (⇓ᵗ[ Θ ] A2)) by reflexivity.
    rewrite ptyp_to_uskl_syn_arrow.
    change (⇓ᵇ[ Θ ] (bskl_arrow Q1 Q2))
      with (bskl_arrow (⇓ᵇ[ Θ ] Q1) (⇓ᵇ[ Θ ] Q2)).
    apply ad_pat_sub_gv__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
      [ | | | assumption ].
    + eapply consis_downarrow_mono;
        [ eassumption | exact Hwf | reflexivity | assumption | assumption ].
    + rewrite uskl_to_pskl_ptyp_to_uskl_syn.
      rewrite bskl_to_pskl_msubst_bskl.
      rewrite <- msubst_pskl_ptyp_to_pskl.
      eapply refine_pskl_downarrow_mono;
        [ | exact Hwf | reflexivity | assumption | assumption ].
      rewrite <- uskl_to_pskl_ptyp_to_uskl_syn. eassumption.
    + apply (IHad_pat_sub_gv Hwf A2 eq_refl ltac:(assumption)
               ltac:(assumption)).
  - (* forall_l_tagged : a mono painting is never a ∀ *)
    destruct A0; cbn in HeqR; try discriminate HeqR; inversion HmA.
  - (* forall_l_untagged *)
    destruct A0; cbn in HeqR; try discriminate HeqR; inversion HmA.
  - (* ghost *) destruct A0; cbn in HeqR; try discriminate HeqR.
  - (* ghostg *) destruct A0; cbn in HeqR; try discriminate HeqR.
  - (* univ_ghost_l *) destruct A0; cbn in HeqR; try discriminate HeqR.
  - (* univ_ghost_lg *) destruct A0; cbn in HeqR; try discriminate HeqR.
  - (* flex_mono : ⇓ has already chased the subject's definition *)
    destruct A0 as [ | nb | γ0 | A1 A2 | A0' ];
      cbn in HeqR; try discriminate HeqR.
    inversion HeqR as [Heqv]. subst γ0.
    assert (Hmτ : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; eauto).
    assert (Hwfτ : a_wf_ptyp Θ τ)
      by (eapply a_wf_aenv_binds_def_wf; eauto).
    assert (Hlk : msubst_lookup (aenv_msubst Θ) α = ⇓ᵗ[ Θ ] τ)
      by (apply aenv_msubst_lookup_def; assumption).
    replace (⇓ᵗ[ Θ ] (ptyp_var_f α)) with (⇓ᵗ[ Θ ] τ)
      by (symmetry; exact Hlk).
    exact (IHad_pat_sub_gv Hwf τ eq_refl Hmτ Hwfτ).
Qed.

Print Assumptions sub_gv_downarrow_mono.

(** THE JOIN's version.  Every row of [ad_pat_sub_gv] that a MONOTYPE-painting
    subject admits either ties [Q] to the subject through a consistency leaf
    (Infer / Check / UnivGhostR / Arrow's domain), recurses (Arrow's codomain,
    ForallR, FlexMono), or is excluded by the subject's shape — a mono
    painting is never a ∀, a ghost, or a tophole, which kills the two ForallL
    rows, Ghost / GhostG and UnivGhostL / LG. *)
Lemma sub_gv_bskl_downarrow_mono_scoped : forall n NM M Ψ Θ R Q,
  ad_pat_sub_gv n NM M Ψ Θ R Q ->
  a_wf_aenv Θ ->
  forall A D,
    R = ptyp_to_uskl_syn A -> mono_ptyp A ->
    ftvar_in_ptyp (⇓ᵗ[ Θ ] A) [<=] D ->
    ftvar_in_bskl (⇓ᵇ[ Θ ] Q) [<=] D.
Proof.
  intros n NM M Ψ Θ R Q H; induction H; intros Hwf A0 D HeqR HmA HAD.
  - (* infer : the consistency premise pins Q *)
    eapply consis_bskl_downarrow_mono_scoped;
      [ eassumption | exact Hwf | exact HeqR | exact HmA | exact HAD ].
  - (* check : same, at the inh painting *)
    eapply consis_bskl_downarrow_mono_scoped;
      [ eassumption | exact Hwf | exact HeqR | exact HmA | exact HAD ].
  - (* forall_r : the target gains a binder, the run moves to (α~tvar)++Θ *)
    simpl.
    pick fresh α for (L `union` D `union` dom Θ `union` ftvar_in_bskl B
                      `union` ftvar_in_aenv Θ).
    assert (Hwf' : a_wf_aenv ((α ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - Fr; fsetdec | exact Hwf ]).
    pose proof (H0 α ltac:(clear - Fr; fsetdec) Hwf' A0 (add α D) HeqR HmA
                  ltac:(rewrite aenv_msubst_tvar_cons;
                        clear - HAD; fsetdec)) as IH.
    rewrite aenv_msubst_tvar_cons in IH.
    pose proof (msubst_bskl_open_ftv_lower (aenv_msubst Θ) B (bskl_var_f α))
      as Hlow.
    assert (Hfr : α `notin` ftvar_in_bskl (msubst_bskl (aenv_msubst Θ) B)).
    { eapply msubst_bskl_ftv_fresh with (Θ := Θ);
        [ apply aenv_msubst_image_dom; exact Hwf
        | clear - Fr; fsetdec | clear - Fr; fsetdec ]. }
    clear - IH Hlow Hfr. fsetdec.
  - (* univ_ghost_r : the tophole wrapper is ftv-transparent *)
    simpl.
    eapply consis_bskl_downarrow_mono_scoped;
      [ eassumption | exact Hwf | exact HeqR | exact HmA | exact HAD ].
  - (* arrow : domain by the consistency leaf, codomain by the IH *)
    destruct A0 as [ | nb | γ0 | A1 A2 | A0' ];
      cbn in HeqR; try discriminate HeqR; try solve [ inversion HmA ].
    inversion HeqR; subst. inversion HmA; subst.
    simpl in HAD |- *. intros γ Hγ. apply union_1 in Hγ.
    destruct Hγ as [h | h].
    + assert (h1 : ftvar_in_bskl (⇓ᵇ[ Θ ] Q1) [<=] D).
      { eapply consis_bskl_downarrow_mono_scoped with (A := A1);
          [ exact H | exact Hwf | reflexivity | assumption
          | clear - HAD; fsetdec ]. }
      clear - h1 h; fsetdec.
    + refine (IHad_pat_sub_gv Hwf A2 D eq_refl _ _ γ h);
        [ assumption | clear - HAD; fsetdec ].
  - (* forall_l_tagged : a mono painting is never a ∀ *)
    destruct A0; cbn in HeqR; try discriminate HeqR; inversion HmA.
  - (* forall_l_untagged *)
    destruct A0; cbn in HeqR; try discriminate HeqR; inversion HmA.
  - (* ghost *)
    destruct A0; cbn in HeqR; try discriminate HeqR.
  - (* ghostg *)
    destruct A0; cbn in HeqR; try discriminate HeqR.
  - (* univ_ghost_l *)
    destruct A0; cbn in HeqR; try discriminate HeqR.
  - (* univ_ghost_lg *)
    destruct A0; cbn in HeqR; try discriminate HeqR.
  - (* flex_mono : the SUBJECT is a defined flexible — ⇓ has chased it *)
    destruct A0; cbn in HeqR; try discriminate HeqR.
    inversion HeqR; subst.
    assert (Hmτ : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; eauto).
    simpl in HAD.
    match goal with
    | Hb : binds ?g (abind_flex_mono_def τ) Θ |- _ =>
        assert (Hlk : msubst_lookup (aenv_msubst Θ) g = ⇓ᵗ[ Θ ] τ)
          by (apply aenv_msubst_lookup_def; assumption)
    end.
    rewrite Hlk in HAD.
    exact (IHad_pat_sub_gv Hwf τ D eq_refl Hmτ HAD).
Qed.

Print Assumptions sub_gv_bskl_downarrow_mono_scoped.

(* ===================================================================== *)
(*  (L)  Flex-SkipRigid's FIRST HALF — moving the solution-side data to    *)
(*       the TRUNCATED context                                            *)
(*                                                                        *)
(*  [Flex-SkipRigid] must run its IH at the truncation Θ' that             *)
(*  [a_inc_tvar_inv] hands back (see the RESTART NOTE below), so every     *)
(*  solution-side premise has to move from Θ to a SUB-context.  These two  *)
(*  lemmas are that move for the REFINEMENT and for the JOIN; consistency  *)
(*  already had it ([ad_pat_consis_strengthen]) and so did skeleton wf     *)
(*  ([a_wf_pskl_strengthen]).                                             *)
(*                                                                        *)
(*  ⚠️ The JOIN does NOT strengthen in general: the two ForallL rows       *)
(*  introduce a GUESS whose scope no condition on the conclusion controls. *)
(*  At a MONOTYPE subject they cannot fire, which is exactly the           *)
(*  configuration [Flex-SkipRigid] is in (the subject is [syn{κα̂}]).  Note *)
(*  the mode must stay GENERAL in the statement: [__arrow]'s recursive     *)
(*  premise runs at [M], not at [mode_fn M], so an FN-only version does    *)
(*  not even induct.                                                      *)
(*                                                                        *)
(*  This replaces, for the subtyping walk, the heavier ⇓-NORMALIZATION     *)
(*  route the consistency walk needs ([a_inc_downarrow_prefix] and         *)
(*  friends): there the counterpart is a free [Q], here it is pinned to a  *)
(*  monotype painting, so plain strengthening suffices.                    *)
(* ===================================================================== *)

(** Refinement strengthens along the same ftv discipline as consistency, with
    two extra bits of care: the bound is [Δ ∪ dom Θ'] (the ∀ rows push their
    opener into Δ, where [__var]'s left disjunct catches it), and the
    definition chases need [Δ] apart from [dom Θ] so that a flexible's ftv
    obligation cannot be discharged by the Δ-disjunct. *)
Lemma ad_refine_pskl_strengthen : forall Θ Δ P Q,
  Θ ⨟ Δ ⊢ᵣₚᵃ P ⊳ Q ->
  forall Θ', uniq Θ -> a_wf_aenv Θ' ->
  (forall x b, binds x b Θ' -> binds x b Θ) ->
  (forall x, x `in` Δ -> x `notin` dom Θ) ->
  (forall γ, γ `in` ftvar_in_pskl P -> γ `in` Δ \/ γ `in` dom Θ') ->
  (forall γ, γ `in` ftvar_in_pskl Q -> γ `in` Δ \/ γ `in` dom Θ') ->
  Θ' ⨟ Δ ⊢ᵣₚᵃ P ⊳ Q.
Proof.
  intros Θ Δ P Q H; induction H;
    intros Θ' Hu Hwf' Hsub Hdisj HscP HscQ; simpl in *.
  - apply ad_refine_pskl__unit.
  - (* var *)
    apply ad_refine_pskl__var.
    destruct H as [HΔ | Ht]; [ left; exact HΔ | ].
    destruct (HscP α ltac:(clear; fsetdec)) as [hΔ | hd];
      [ left; exact hΔ | right ].
    eapply a_binds_tvar_strengthen;
      [ exact Ht | exact Hu | exact Hsub | exact hd ].
  - (* arrow *)
    apply ad_refine_pskl__arrow;
      [ apply IHad_refine_pskl1 | apply IHad_refine_pskl2 ];
      auto; intros γ Hγ;
      solve [ apply HscP; clear - Hγ; fsetdec
            | apply HscQ; clear - Hγ; fsetdec ].
  - (* all : the opener joins Δ *)
    apply ad_refine_pskl__all with (L := L `union` dom Θ `union` Δ).
    intros α Hα.
    apply H0; [ clear - Hα; fsetdec | exact Hu | exact Hwf' | exact Hsub
              | intros x Hx; assert (h : x `in` Δ \/ x = α)
                  by (clear - Hx; fsetdec);
                destruct h as [h | ->];
                  [ exact (Hdisj x h) | clear - Hα; fsetdec ]
              | | ].
    + intros γ Hγ.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f α))
        as Hup. simpl in Hup.
      destruct (γ == α) as [-> | Hne]; [ left; clear; fsetdec | ].
      destruct (HscP γ ltac:(clear - Hγ Hup Hne; fsetdec)) as [h | h];
        [ left; clear - h; fsetdec | right; exact h ].
    + intros γ Hγ.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q (pskl_var_f α))
        as Hup. simpl in Hup.
      destruct (γ == α) as [-> | Hne]; [ left; clear; fsetdec | ].
      destruct (HscQ γ ltac:(clear - Hγ Hup Hne; fsetdec)) as [h | h];
        [ left; clear - h; fsetdec | right; exact h ].
  - (* hole : the fill is Δ-free, so its ftv really is in dom Θ' *)
    apply ad_refine_pskl__hole.
    assert (HftQ : forall γ, γ `in` ftvar_in_pskl Q -> γ `in` dom Θ').
    { intros γ Hγ.
      destruct (HscQ γ Hγ) as [h | h]; [ exfalso | exact h ].
      assert (hd : γ `in` dom Θ) by (eapply a_wf_pskl_ftv_dom; eassumption).
      exact (Hdisj γ h hd). }
    eapply a_wf_pskl_strengthen;
      [ exact H | exact Hu | intros x Hx; exfalso; clear - Hx; fsetdec
      | exact Hsub | ].
    intros γ Hγ. right. apply HftQ; exact Hγ.
  - (* tophole_remove *)
    apply ad_refine_pskl__tophole_remove. apply IHad_refine_pskl; auto.
  - (* tophole_fill : the opener joins the CONTEXT *)
    apply ad_refine_pskl__tophole_fill
      with (L := L `union` dom Θ `union` dom Θ' `union` Δ).
    intros α Hα.
    apply H0; [ clear - Hα; fsetdec | | | | | | ].
    + simpl_env. apply uniq_cons_3; [ exact Hu | clear - Hα; fsetdec ].
    + apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf' ].
    + intros x b0 Hb0. analyze_binds Hb0.
    + intros x Hx. simpl_env.
      assert (h : x `notin` dom Θ) by (exact (Hdisj x Hx)).
      assert (h2 : x <> α) by (intro Hc; subst; clear - Hα Hx; fsetdec).
      clear - h h2. fsetdec.
    + intros γ Hγ.
      destruct (HscP γ ltac:(clear - Hγ; fsetdec)) as [h | h];
        [ left; exact h | right; simpl_env; clear - h; fsetdec ].
    + intros γ Hγ.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q (pskl_var_f α))
        as Hup. simpl in Hup.
      destruct (γ == α) as [-> | Hne];
        [ right; simpl_env; clear; fsetdec | ].
      destruct (HscQ γ ltac:(clear - Hγ Hup Hne; fsetdec)) as [h | h];
        [ left; exact h | right; simpl_env; clear - h; fsetdec ].
  - (* tophole_keep *)
    apply ad_refine_pskl__tophole_keep; [ exact H | ].
    apply IHad_refine_pskl; auto.
  - (* flex_l *)
    assert (hd : α `in` dom Θ').
    { destruct (HscP α ltac:(clear; fsetdec)) as [h | h]; [ exfalso | exact h ].
      assert (hdΘ : α `in` dom Θ) by (eapply binds_In; exact H).
      exact (Hdisj α h hdΘ). }
    assert (Hb' : binds α (abind_flex_mono_def τ) Θ')
      by (eapply binds_strengthen; [ exact H | exact Hu | exact Hsub
                                   | exact hd ]).
    eapply ad_refine_pskl__flex_l; [ exact Hb' | ].
    apply IHad_refine_pskl; auto.
    intros γ Hγ. right.
    assert (hw : a_wf_ptyp Θ' τ)
      by (eapply a_wf_aenv_binds_def_wf; [ exact Hwf' | exact Hb' ]).
    apply a_wf_ptyp_ftv_dom in hw.
    rewrite ftvar_in_ptyp_to_pskl in Hγ. clear - hw Hγ. fsetdec.
  - (* flex_r *)
    assert (hd : α `in` dom Θ').
    { destruct (HscQ α ltac:(clear; fsetdec)) as [h | h]; [ exfalso | exact h ].
      assert (hdΘ : α `in` dom Θ) by (eapply binds_In; exact H).
      exact (Hdisj α h hdΘ). }
    assert (Hb' : binds α (abind_flex_mono_def τ) Θ')
      by (eapply binds_strengthen; [ exact H | exact Hu | exact Hsub
                                   | exact hd ]).
    eapply ad_refine_pskl__flex_r; [ exact Hb' | ].
    apply IHad_refine_pskl; auto.
    intros γ Hγ. right.
    assert (hw : a_wf_ptyp Θ' τ)
      by (eapply a_wf_aenv_binds_def_wf; [ exact Hwf' | exact Hb' ]).
    apply a_wf_ptyp_ftv_dom in hw.
    rewrite ftvar_in_ptyp_to_pskl in Hγ. clear - hw Hγ. fsetdec.
Qed.

(** THE JOIN STRENGTHENS AT A MONOTYPE SUBJECT.  In general it does NOT: the
    two ForallL rows introduce a GUESS whose scope no condition on the
    conclusion controls.  At a monotype subject they cannot fire (a mono
    painting is [unit] / a variable / an arrow, never a ∀ and never a ghost),
    and every surviving row keeps its new material inside the subject's or the
    counterpart's free variables — with the definition chase [__flex_mono]
    reading a binding the ftv condition already places in Θ'.  This is what
    [Flex-SkipRigid] needs to move its join to the TRUNCATED solution.

    ⚠️ The mode must stay GENERAL: [__arrow]'s recursive premise runs at [M],
    not at [mode_fn M], so an FN-only statement does not even induct. *)
Lemma ad_pat_sub_gv_mono_strengthen : forall n NM M Ψ Θ R Q,
  ad_pat_sub_gv n NM M Ψ Θ R Q ->
  forall τ, R = ptyp_to_uskl_syn τ -> mono_ptyp τ ->
  forall Θ', uniq Θ -> a_wf_aenv Θ' ->
  (forall x b, binds x b Θ' -> binds x b Θ) ->
  (forall γ, γ `in` ftvar_in_ptyp τ -> γ `in` dom Θ') ->
  (forall γ, γ `in` ftvar_in_bskl Q -> γ `in` dom Θ') ->
  ad_pat_sub_gv n NM M Ψ Θ' R Q.
Proof.
  intros n NM M Ψ Θ R Q H; induction H;
    intros τ0 HeqR Hm Θ' Hu Hwf' Hsub HscR HscQ;
    pose proof (ftvar_in_uskl_ptyp_syn τ0) as HftvR;
    rewrite <- HeqR in HftvR.
  - (* infer *)
    apply ad_pat_sub_gv__infer; try assumption.
    + eapply ad_pat_consis_strengthen; try eassumption;
        intros γ Hγ;
        solve [ apply HscR; clear - Hγ HftvR; fsetdec
              | apply HscQ; clear - Hγ; fsetdec ].
    + eapply ad_refine_pskl_strengthen;
        [ eassumption | exact Hu | exact Hwf' | exact Hsub
        | intros x Hx; exfalso; clear - Hx; fsetdec | | ];
        intros γ Hγ; right;
        solve [ apply HscR; rewrite ftvar_in_pskl_uskl_to_pskl in Hγ;
                clear - Hγ HftvR; fsetdec
              | apply HscQ; rewrite ftvar_in_pskl_bskl_to_pskl in Hγ;
                clear - Hγ; fsetdec ].
  - (* check *)
    apply ad_pat_sub_gv__check; try assumption.
    + eapply ad_pat_consis_strengthen; try eassumption;
        intros γ Hγ;
        solve [ apply HscR; clear - Hγ HftvR; fsetdec
              | apply HscQ; rewrite ftvar_in_bskl_inh; clear - Hγ; fsetdec ].
    + eapply ad_refine_pskl_strengthen;
        [ eassumption | exact Hu | exact Hwf' | exact Hsub
        | intros x Hx; exfalso; clear - Hx; fsetdec | | ];
        intros γ Hγ; right;
        solve [ apply HscR; rewrite ftvar_in_pskl_uskl_to_pskl in Hγ;
                clear - Hγ HftvR; fsetdec
              | apply HscQ; rewrite ftvar_in_bskl_inh; clear - Hγ; fsetdec ].
  - (* forall_r : the opener joins the CONTEXT *)
    apply ad_pat_sub_gv__forall_r with (L := L `union` dom Θ `union` dom Θ').
    intros α Hα.
    eapply H0;
      [ clear - Hα; fsetdec | exact HeqR | exact Hm
      | simpl_env; apply uniq_cons_3; [ exact Hu | clear - Hα; fsetdec ]
      | apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf' ]
      | intros x b0 Hb0; analyze_binds Hb0
      | intros γ Hγ; simpl_env; assert (h := HscR γ Hγ); clear - h; fsetdec
      | ].
    intros γ Hγ. simpl_env.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper B (bskl_var_f α))
      as Hup. simpl in Hup.
    destruct (γ == α) as [-> | Hne]; [ clear; fsetdec | ].
    assert (h : γ `in` dom Θ')
      by (apply HscQ; simpl; clear - Hγ Hup Hne; fsetdec).
    clear - h; fsetdec.
  - (* univ_ghost_r *)
    apply ad_pat_sub_gv__univ_ghost_r; try assumption.
    + eapply ad_pat_consis_strengthen; try eassumption;
        intros γ Hγ;
        solve [ apply HscR; clear - Hγ HftvR; fsetdec
              | apply HscQ; simpl; clear - Hγ; fsetdec ].
    + eapply ad_refine_pskl_strengthen;
        [ eassumption | exact Hu | exact Hwf' | exact Hsub
        | intros x Hx; exfalso; clear - Hx; fsetdec | | ];
        intros γ Hγ; right;
        solve [ apply HscR; rewrite ftvar_in_pskl_uskl_to_pskl in Hγ;
                clear - Hγ HftvR; fsetdec
              | apply HscQ; simpl;
                rewrite ftvar_in_pskl_bskl_to_pskl in Hγ;
                clear - Hγ; fsetdec ].
  - (* arrow *)
    destruct τ0; cbn in HeqR; try discriminate HeqR.
    inversion HeqR; subst. inversion Hm; subst.
    eapply ad_pat_sub_gv__arrow; [ | | | eassumption ].
    + eapply ad_pat_consis_strengthen; try eassumption.
      * intros γ Hγ. apply HscR. simpl. simpl in HftvR.
        clear - Hγ HftvR. fsetdec.
      * intros γ Hγ. apply HscQ. simpl. clear - Hγ. fsetdec.
    + eapply ad_refine_pskl_strengthen;
        [ eassumption | exact Hu | exact Hwf' | exact Hsub
        | intros x Hx; exfalso; clear - Hx; fsetdec | | ].
      * intros γ Hγ. right. apply HscR. simpl.
        rewrite ftvar_in_pskl_uskl_to_pskl in Hγ.
        simpl in HftvR. clear - Hγ HftvR. fsetdec.
      * intros γ Hγ. right. apply HscQ. simpl.
        rewrite ftvar_in_pskl_bskl_to_pskl in Hγ. clear - Hγ. fsetdec.
    + eapply IHad_pat_sub_gv;
        [ reflexivity | assumption | exact Hu | exact Hwf' | exact Hsub | | ].
      * intros γ Hγ. apply HscR. simpl. simpl in HftvR.
        clear - Hγ HftvR. fsetdec.
      * intros γ Hγ. apply HscQ. simpl. clear - Hγ. fsetdec.
  - (* forall_l_tagged : a mono painting is never a ∀ *)
    destruct τ0; cbn in HeqR; discriminate HeqR.
  - (* forall_l_untagged : a mono painting's ∀ shape is [uskl_all_syn], so
       the discriminate only kills the non-∀ shapes; [mono] kills the ∀ *)
    destruct τ0; cbn in HeqR; try discriminate HeqR. inversion Hm.
  - (* ghost *)
    destruct τ0; cbn in HeqR; discriminate HeqR.
  - (* ghostg *)
    destruct τ0; cbn in HeqR; discriminate HeqR.
  - (* univ_ghost_l *)
    destruct τ0; cbn in HeqR; discriminate HeqR.
  - (* univ_ghost_lg *)
    destruct τ0; cbn in HeqR; discriminate HeqR.
  - (* flex_mono : the definition chase *)
    (* keep the RULE's α: do the shape analysis inside an [assert] so the
       destruct's freshening stays local *)
    assert (Hτ0 : τ0 = ptyp_var_f α)
      by (destruct τ0; cbn in HeqR; try discriminate HeqR;
          injection HeqR; intros ->; reflexivity).
    subst τ0.
    assert (HαΘ' : α `in` dom Θ')
      by (apply HscR; simpl; clear; fsetdec).
    assert (Hb' : binds α (abind_flex_mono_def τ) Θ')
      by (eapply binds_strengthen; [ eassumption | exact Hu | exact Hsub
                                   | exact HαΘ' ]).
    eapply ad_pat_sub_gv__flex_mono; [ exact Hb' | ].
    eapply IHad_pat_sub_gv;
      [ reflexivity
      | eapply a_wf_aenv_binds_def_mono; [ exact Hwf' | exact Hb' ]
      | exact Hu | exact Hwf' | exact Hsub | | exact HscQ ].
    intros γ Hγ.
    assert (hw : a_wf_ptyp Θ' τ)
      by (eapply a_wf_aenv_binds_def_wf; [ exact Hwf' | exact Hb' ]).
    apply a_wf_ptyp_ftv_dom in hw. clear - hw Hγ. fsetdec.
Qed.

(** The FILL's counterpart of [ad_refine_pskl_strengthen] — same discipline,
    same two provisos (the ∀ row's opener joins Δ; Δ apart from [dom Θ] so the
    definition chases cannot be discharged by the Δ-disjunct).  [F] is inert. *)
Lemma ad_refine_syn_f_strengthen : forall F Θ Δ Q P,
  ad_refine_syn_f F Θ Δ Q P ->
  forall Θ', uniq Θ -> a_wf_aenv Θ' ->
  (forall x b, binds x b Θ' -> binds x b Θ) ->
  (forall x, x `in` Δ -> x `notin` dom Θ) ->
  (forall γ, γ `in` ftvar_in_bskl Q -> γ `in` Δ \/ γ `in` dom Θ') ->
  (forall γ, γ `in` ftvar_in_bskl P -> γ `in` Δ \/ γ `in` dom Θ') ->
  ad_refine_syn_f F Θ' Δ Q P.
Proof.
  intros F Θ Δ Q P H; induction H;
    intros Θ' Hu Hwf' Hsub Hdisj HscQ HscP; simpl in *.
  - apply ad_refine_syn_f__unit.
  - apply ad_refine_syn_f__var.
    destruct H as [HΔ | Ht]; [ left; exact HΔ | ].
    destruct (HscQ α ltac:(clear; fsetdec)) as [hΔ | hd];
      [ left; exact hΔ | right ].
    eapply a_binds_tvar_strengthen;
      [ exact Ht | exact Hu | exact Hsub | exact hd ].
  - apply ad_refine_syn_f__arrow;
      [ apply IHad_refine_syn_f1 | apply IHad_refine_syn_f2 ];
      auto; intros γ Hγ;
      solve [ apply HscQ; clear - Hγ; fsetdec
            | apply HscP; clear - Hγ; fsetdec ].
  - apply ad_refine_syn_f__all with (L := L `union` dom Θ `union` Δ).
    intros α Hα.
    apply H0;
      [ clear - Hα; fsetdec | exact Hu | exact Hwf' | exact Hsub
      | intros x Hx;
        assert (h : x `in` Δ \/ x = α) by (clear - Hx; fsetdec);
        destruct h as [h | ->];
          [ exact (Hdisj x h) | clear - Hα; fsetdec ]
      | | ];
      intros γ Hγ;
      [ pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f α))
          as Hup
      | pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper P (bskl_var_f α))
          as Hup ];
      simpl in Hup;
      (destruct (γ == α) as [-> | Hne]; [ left; clear; fsetdec | ]);
      [ destruct (HscQ γ ltac:(clear - Hγ Hup Hne; fsetdec)) as [h | h]
      | destruct (HscP γ ltac:(clear - Hγ Hup Hne; fsetdec)) as [h | h] ];
      solve [ left; clear - h; fsetdec | right; exact h ].
  - (* hole : the fill is Δ-free *)
    assert (HftP : forall γ, γ `in` ftvar_in_pskl P -> γ `in` dom Θ').
    { intros γ Hγ.
      assert (hb : γ `in` ftvar_in_bskl (pskl_to_bskl_syn P))
        by (rewrite ftvar_in_bskl_syn; exact Hγ).
      destruct (HscP γ hb) as [h | h]; [ exfalso | exact h ].
      assert (hd : γ `in` dom Θ) by (eapply a_wf_pskl_ftv_dom; eassumption).
      exact (Hdisj γ h hd). }
    apply ad_refine_syn_f__hole; [ exact H | ].
    eapply a_wf_pskl_strengthen;
      [ exact H0 | exact Hu | intros x Hx; exfalso; clear - Hx; fsetdec
      | exact Hsub | ].
    intros γ Hγ. right. apply HftP; exact Hγ.
  - apply ad_refine_syn_f__tophole_remove. apply IHad_refine_syn_f; auto.
  - (* tophole_fill : the opener joins the CONTEXT *)
    apply ad_refine_syn_f__tophole_fill
      with (L := L `union` dom Θ `union` dom Θ' `union` Δ).
    intros α Hα.
    apply H0; [ clear - Hα; fsetdec | | | | | | ].
    + simpl_env. apply uniq_cons_3; [ exact Hu | clear - Hα; fsetdec ].
    + apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf' ].
    + intros x b0 Hb0. analyze_binds Hb0.
    + intros x Hx. simpl_env.
      assert (h : x `notin` dom Θ) by (exact (Hdisj x Hx)).
      assert (h2 : x <> α) by (intro Hc; subst; clear - Hα Hx; fsetdec).
      clear - h h2. fsetdec.
    + intros γ Hγ.
      destruct (HscQ γ ltac:(clear - Hγ; fsetdec)) as [h | h];
        [ left; exact h | right; simpl_env; clear - h; fsetdec ].
    + intros γ Hγ.
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper P (bskl_var_f α))
        as Hup. simpl in Hup.
      destruct (γ == α) as [-> | Hne];
        [ right; simpl_env; clear; fsetdec | ].
      destruct (HscP γ ltac:(clear - Hγ Hup Hne; fsetdec)) as [h | h];
        [ left; exact h | right; simpl_env; clear - h; fsetdec ].
  - apply ad_refine_syn_f__tophole_keep; [ exact H | ].
    apply IHad_refine_syn_f; auto.
  - (* flex_l *)
    assert (hd : α `in` dom Θ').
    { destruct (HscQ α ltac:(clear; fsetdec)) as [h | h]; [ exfalso | exact h ].
      assert (hdΘ : α `in` dom Θ) by (eapply binds_In; exact H).
      exact (Hdisj α h hdΘ). }
    assert (Hb' : binds α (abind_flex_mono_def τ) Θ')
      by (eapply binds_strengthen; [ exact H | exact Hu | exact Hsub
                                   | exact hd ]).
    eapply ad_refine_syn_f__flex_l; [ exact Hb' | ].
    apply IHad_refine_syn_f; auto.
    intros γ Hγ. right.
    assert (hw : a_wf_ptyp Θ' τ)
      by (eapply a_wf_aenv_binds_def_wf; [ exact Hwf' | exact Hb' ]).
    apply a_wf_ptyp_ftv_dom in hw.
    unfold ptyp_to_bskl_syn in Hγ. rewrite ftvar_in_bskl_syn in Hγ.
    rewrite ftvar_in_ptyp_to_pskl in Hγ. clear - hw Hγ. fsetdec.
  - (* flex_r *)
    assert (hd : α `in` dom Θ').
    { destruct (HscP α ltac:(clear; fsetdec)) as [h | h]; [ exfalso | exact h ].
      assert (hdΘ : α `in` dom Θ) by (eapply binds_In; exact H).
      exact (Hdisj α h hdΘ). }
    assert (Hb' : binds α (abind_flex_mono_def τ) Θ')
      by (eapply binds_strengthen; [ exact H | exact Hu | exact Hsub
                                   | exact hd ]).
    eapply ad_refine_syn_f__flex_r; [ exact Hb' | ].
    apply IHad_refine_syn_f; auto.
    intros γ Hγ. right.
    assert (hw : a_wf_ptyp Θ' τ)
      by (eapply a_wf_aenv_binds_def_wf; [ exact Hwf' | exact Hb' ]).
    apply a_wf_ptyp_ftv_dom in hw.
    unfold ptyp_to_bskl_syn in Hγ. rewrite ftvar_in_bskl_syn in Hγ.
    rewrite ftvar_in_ptyp_to_pskl in Hγ. clear - hw Hγ. fsetdec.
Qed.

(* ===================================================================== *)
(*  (L1)  ⇓-NORMALIZING THE FILL, and the two transports the row needs     *)
(*        around it                                                        *)
(*                                                                        *)
(*  §(L0) normalizes the JOIN; the FILL is the other solution-side         *)
(*  premise, and its source [κP0] is NOT a monotype, so that induction     *)
(*  covers every row.  Two further facts come with it: the ⇓-normalized    *)
(*  SOURCE is scoped by the ⇓-normalized TARGET (which is what turns the   *)
(*  join's confinement into §(L)'s hypothesis for BOTH sides of the fill), *)
(*  and ⇓ is itself a PRECISION refinement — the transport the motive's    *)
(*  third conjunct needs to come back from [⇓ᵇQ] to [Q].                   *)
(* ===================================================================== *)

Lemma a_wf_pskl_downarrow : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  a_wf_aenv Θ ->
  (forall α, α `in` Δ -> α `notin` dom Θ) ->
  Θ ⨟ Δ ⊢ₚₛᵃ (⇓ˢ[ Θ ] P).
Proof.
  intros Θ Δ P H; induction H; intros Hwf HΔ; simpl.
  - apply a_wf_pskl__unit.
  - (* var *)
    destruct H as [HαΔ | Hbt].
    + assert (Hn : α `notin` dom (aenv_msubst Θ)).
      { pose proof (dom_aenv_msubst Θ) as h. pose proof (HΔ α HαΔ) as h2.
        clear - h h2. fsetdec. }
      rewrite msubst_lookup_notin by exact Hn. simpl.
      apply a_wf_pskl__var; left; exact HαΔ.
    + apply a_wf_ptyp_to_wf_pskl.
      apply aenv_msubst_image_wf; assumption.
  - apply a_wf_pskl__arrow;
      [ apply IHa_wf_pskl1 | apply IHa_wf_pskl2 ]; solve [ exact Hwf | exact HΔ ].
  - (* all : the opener joins Δ, so it must miss dom Θ *)
    apply a_wf_pskl__all with (L := L `union` dom Θ).
    intros α Hα.
    assert (Heq : msubst_pskl (aenv_msubst Θ)
                    (open_pskl_wrt_pskl P (pskl_var_f α))
                  = open_pskl_wrt_pskl (msubst_pskl (aenv_msubst Θ) P)
                      (pskl_var_f α)).
    { apply msubst_pskl_open_lc_local;
        [ apply aenv_msubst_lc; exact Hwf
        | pose proof (dom_aenv_msubst Θ) as h; clear - Hα h; fsetdec ]. }
    rewrite <- Heq.
    apply H0; [ clear - Hα; fsetdec | exact Hwf | ].
    intros β Hβ.
    destruct (β == α) as [-> | Hne]; [ clear - Hα; fsetdec | ].
    apply HΔ. clear - Hβ Hne; fsetdec.
  - apply a_wf_pskl__hole.
  - apply a_wf_pskl__tophole.
    + apply guarded_pskl_msubst_mono;
        [ apply aenv_msubst_lc; exact Hwf
        | intros; apply aenv_msubst_image_mono; exact Hwf
        | exact H ].
    + apply IHa_wf_pskl; [ exact Hwf | ].
      intros β Hβ. exfalso. clear - Hβ. fsetdec.
Qed.

(** ⇓-NORMALIZING THE FILL.  Unlike the two leaf normalizations of §(L0) the
    source here is NOT a monotype ([κP0] is an arbitrary skeleton), so the
    induction covers every row: the [__hole] fill needs wf under ⇓, the two ∀
    rows need the open-commutation, and the two [__flex_*] rows are exactly
    the chases ⇓ has already performed.  [F] is instantiated at [empty] — the
    hole rule's [F ∩ ftv(fill) = ∅] side condition is about the FILL, which ⇓
    changes. *)
Lemma refine_syn_f_downarrow : forall Θ Δ Q P,
  ad_refine_syn_f empty Θ Δ Q P ->
  a_wf_aenv Θ ->
  (forall x, x `in` Δ -> x `notin` dom Θ) ->
  ad_refine_syn_f empty Θ Δ (⇓ᵇ[ Θ ] Q) (⇓ᵇ[ Θ ] P).
Proof.
  intros Θ Δ Q P H; induction H; intros Hwf HΔ.
  - (* unit *) apply ad_refine_syn_f__unit.
  - (* var *)
    destruct H as [HαΔ | Hbt].
    + assert (Hn : α `notin` dom (aenv_msubst Θ)).
      { pose proof (dom_aenv_msubst Θ) as h. pose proof (HΔ α HαΔ) as h2.
        clear - h h2. fsetdec. }
      simpl. rewrite msubst_lookup_notin by exact Hn. simpl.
      apply ad_refine_syn_f__var. left; exact HαΔ.
    + (* the image is a wf MONOTYPE painting; refinement is reflexive there *)
      simpl.
      change (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup (aenv_msubst Θ) α)))
        with (ptyp_to_bskl_syn (msubst_lookup (aenv_msubst Θ) α)).
      apply ad_refine_syn_f_mono_refl;
        [ apply aenv_msubst_image_mono; exact Hwf
        | apply aenv_msubst_image_wf; assumption ].
  - (* arrow *)
    simpl. apply ad_refine_syn_f__arrow;
      [ apply IHad_refine_syn_f1 | apply IHad_refine_syn_f2 ];
      solve [ exact Hwf | exact HΔ ].
  - (* all *)
    simpl.
    apply ad_refine_syn_f__all
      with (L := L `union` dom Θ `union` Δ `union` dom (aenv_msubst Θ)).
    intros α Hα.
    assert (HeqQ : msubst_bskl (aenv_msubst Θ)
                     (open_bskl_wrt_bskl Q (bskl_var_f α))
                   = open_bskl_wrt_bskl (msubst_bskl (aenv_msubst Θ) Q)
                       (bskl_var_f α))
      by (apply msubst_bskl_open_lc;
          [ apply aenv_msubst_lc; exact Hwf | clear - Hα; fsetdec ]).
    assert (HeqP : msubst_bskl (aenv_msubst Θ)
                     (open_bskl_wrt_bskl P (bskl_var_f α))
                   = open_bskl_wrt_bskl (msubst_bskl (aenv_msubst Θ) P)
                       (bskl_var_f α))
      by (apply msubst_bskl_open_lc;
          [ apply aenv_msubst_lc; exact Hwf | clear - Hα; fsetdec ]).
    rewrite <- HeqQ, <- HeqP.
    apply H0; [ clear - Hα; fsetdec | exact Hwf | ].
    intros x Hx.
    destruct (x == α) as [-> | Hne]; [ clear - Hα; fsetdec | ].
    apply HΔ. clear - Hx Hne; fsetdec.
  - (* hole : ⇓ of the FILL, whose wf is [a_wf_pskl_downarrow] *)
    simpl. rewrite msubst_bskl_pskl_to_bskl_syn.
    apply ad_refine_syn_f__hole;
      [ clear; fsetdec
      | apply a_wf_pskl_downarrow;
          [ exact H0 | exact Hwf | intros x Hx; exfalso; clear - Hx; fsetdec ] ].
  - (* tophole_remove *)
    simpl. apply ad_refine_syn_f__tophole_remove.
    apply IHad_refine_syn_f; [ exact Hwf | exact HΔ ].
  - (* tophole_fill : the opener joins the CONTEXT, which ⇓ ignores *)
    simpl.
    apply ad_refine_syn_f__tophole_fill
      with (L := L `union` dom Θ `union` Δ `union` dom (aenv_msubst Θ)).
    intros α Hα.
    assert (Hwf' : a_wf_aenv ((α ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ]).
    pose proof (H0 α ltac:(clear - Hα; fsetdec) Hwf'
                  ltac:(intros x Hx; simpl_env;
                        assert (h : x `notin` dom Θ) by (exact (HΔ x Hx));
                        assert (h2 : x <> α)
                          by (intro Hc; subst; clear - Hα Hx; fsetdec);
                        clear - h h2; fsetdec)) as IH.
    rewrite aenv_msubst_tvar_cons in IH.
    assert (HeqP : msubst_bskl (aenv_msubst Θ)
                     (open_bskl_wrt_bskl P (bskl_var_f α))
                   = open_bskl_wrt_bskl (msubst_bskl (aenv_msubst Θ) P)
                       (bskl_var_f α))
      by (apply msubst_bskl_open_lc;
          [ apply aenv_msubst_lc; exact Hwf | clear - Hα; fsetdec ]).
    rewrite HeqP in IH. simpl in IH. exact IH.
  - (* tophole_keep *)
    simpl. apply ad_refine_syn_f__tophole_keep;
      [ apply guarded_bskl_msubst_mono;
          [ apply aenv_msubst_lc; exact Hwf
          | intros; apply aenv_msubst_image_mono; exact Hwf
          | exact H ]
      | apply IHad_refine_syn_f; [ exact Hwf | exact HΔ ] ].
  - (* flex_l : ⇓ has already chased the source's definition *)
    assert (Hlk : msubst_lookup (aenv_msubst Θ) α = ⇓ᵗ[ Θ ] τ)
      by (apply aenv_msubst_lookup_def; assumption).
    simpl. rewrite Hlk.
    pose proof (IHad_refine_syn_f Hwf HΔ) as IH.
    rewrite msubst_bskl_ptyp_to_bskl_syn in IH.
    exact IH.
  - (* flex_r : ⇓ has already chased the target's definition *)
    assert (Hlk : msubst_lookup (aenv_msubst Θ) α = ⇓ᵗ[ Θ ] τ)
      by (apply aenv_msubst_lookup_def; assumption).
    simpl. rewrite Hlk.
    pose proof (IHad_refine_syn_f Hwf HΔ) as IH.
    rewrite msubst_bskl_ptyp_to_bskl_syn in IH.
    exact IH.
Qed.

(** SCOPING THE ⇓-NORMALIZED SOURCE FROM THE ⇓-NORMALIZED TARGET.  Refinement's
    source free variables sit below its target's — modulo the definition
    chases, which is exactly what ⇓ has already performed: [__flex_l] /
    [__flex_r] replace a variable by its definition, and under ⇓ the two sides
    of that replacement are literally the same term.  [Δ] collects the ∀ rows'
    openers.  This is what supplies §(L)'s [ftv ⊆ dom Θ'] hypothesis for the
    FILL's source once the confinement has supplied it for its target. *)
Lemma refine_syn_f_downarrow_source_ftv : forall F Θ Δ Q P,
  ad_refine_syn_f F Θ Δ Q P ->
  a_wf_aenv Θ ->
  (forall x, x `in` Δ -> x `notin` dom Θ) ->
  ftvar_in_bskl (⇓ᵇ[ Θ ] Q) [<=] Δ ∪ ftvar_in_bskl (⇓ᵇ[ Θ ] P).
Proof.
  intros F Θ Δ Q P H; induction H; intros Hwf HΔ.
  - (* unit *) simpl. clear; fsetdec.
  - (* var : both sides are the same image *) clear; fsetdec.
  - (* arrow *)
    pose proof (IHad_refine_syn_f1 Hwf HΔ) as h1.
    pose proof (IHad_refine_syn_f2 Hwf HΔ) as h2.
    simpl. clear - h1 h2; fsetdec.
  - (* all : the opener is fresh for the source's ⇓ *)
    simpl.
    pick fresh α for (L `union` Δ `union` dom Θ `union` ftvar_in_bskl Q
                      `union` ftvar_in_bskl P `union` dom (aenv_msubst Θ)).
    assert (HeqQ : msubst_bskl (aenv_msubst Θ)
                     (open_bskl_wrt_bskl Q (bskl_var_f α))
                   = open_bskl_wrt_bskl (msubst_bskl (aenv_msubst Θ) Q)
                       (bskl_var_f α))
      by (apply msubst_bskl_open_lc;
          [ apply aenv_msubst_lc; exact Hwf | clear - Fr; fsetdec ]).
    assert (HeqP : msubst_bskl (aenv_msubst Θ)
                     (open_bskl_wrt_bskl P (bskl_var_f α))
                   = open_bskl_wrt_bskl (msubst_bskl (aenv_msubst Θ) P)
                       (bskl_var_f α))
      by (apply msubst_bskl_open_lc;
          [ apply aenv_msubst_lc; exact Hwf | clear - Fr; fsetdec ]).
    pose proof (H0 α ltac:(clear - Fr; fsetdec) Hwf
                  ltac:(intros x Hx;
                        destruct (x == α) as [-> | Hne];
                          [ clear - Fr; fsetdec
                          | apply HΔ; clear - Hx Hne; fsetdec ])) as IH.
    rewrite HeqQ, HeqP in IH.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_lower
                  (msubst_bskl (aenv_msubst Θ) Q) (bskl_var_f α)) as Hlow.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper
                  (msubst_bskl (aenv_msubst Θ) P) (bskl_var_f α)) as Hup.
    simpl in Hup.
    assert (Hfr : α `notin` ftvar_in_bskl (msubst_bskl (aenv_msubst Θ) Q)).
    { eapply msubst_bskl_ftv_fresh with (Θ := Θ);
        [ apply aenv_msubst_image_dom; exact Hwf
        | clear - Fr; fsetdec | clear - Fr; fsetdec ]. }
    clear - IH Hlow Hup Hfr. fsetdec.
  - (* hole : the source has no free variables *) simpl. clear; fsetdec.
  - (* tophole_remove *)
    pose proof (IHad_refine_syn_f Hwf HΔ) as IH. simpl. clear - IH; fsetdec.
  - (* tophole_fill : same as [all], with the opener joining the CONTEXT *)
    simpl.
    pick fresh α for (L `union` Δ `union` dom Θ `union` ftvar_in_bskl Q
                      `union` ftvar_in_bskl P `union` dom (aenv_msubst Θ)).
    assert (Hwf' : a_wf_aenv ((α ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - Fr; fsetdec | exact Hwf ]).
    assert (HeqP : msubst_bskl (aenv_msubst Θ)
                     (open_bskl_wrt_bskl P (bskl_var_f α))
                   = open_bskl_wrt_bskl (msubst_bskl (aenv_msubst Θ) P)
                       (bskl_var_f α))
      by (apply msubst_bskl_open_lc;
          [ apply aenv_msubst_lc; exact Hwf | clear - Fr; fsetdec ]).
    pose proof (H0 α ltac:(clear - Fr; fsetdec) Hwf'
                  ltac:(intros x Hx; simpl_env;
                        assert (h : x `notin` dom Θ) by (exact (HΔ x Hx));
                        assert (h2 : x <> α)
                          by (intro Hc; subst; clear - Fr Hx; fsetdec);
                        clear - h h2; fsetdec)) as IH.
    rewrite aenv_msubst_tvar_cons in IH.
    rewrite HeqP in IH. simpl in IH.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper
                  (msubst_bskl (aenv_msubst Θ) P) (bskl_var_f α)) as Hup.
    simpl in Hup.
    assert (Hfr : α `notin` ftvar_in_bskl (msubst_bskl (aenv_msubst Θ) Q)).
    { eapply msubst_bskl_ftv_fresh with (Θ := Θ);
        [ apply aenv_msubst_image_dom; exact Hwf
        | clear - Fr; fsetdec | clear - Fr; fsetdec ]. }
    clear - IH Hup Hfr. fsetdec.
  - (* tophole_keep *)
    pose proof (IHad_refine_syn_f Hwf HΔ) as IH. simpl. clear - IH; fsetdec.
  - (* flex_l : under ⇓ the variable and its definition are the SAME term *)
    assert (Hlk : msubst_lookup (aenv_msubst Θ) α = ⇓ᵗ[ Θ ] τ)
      by (apply aenv_msubst_lookup_def; assumption).
    pose proof (IHad_refine_syn_f Hwf HΔ) as IH.
    rewrite msubst_bskl_ptyp_to_bskl_syn in IH.
    simpl. rewrite Hlk. exact IH.
  - (* flex_r : likewise on the target *)
    assert (Hlk : msubst_lookup (aenv_msubst Θ) α = ⇓ᵗ[ Θ ] τ)
      by (apply aenv_msubst_lookup_def; assumption).
    pose proof (IHad_refine_syn_f Hwf HΔ) as IH.
    rewrite msubst_bskl_ptyp_to_bskl_syn in IH.
    simpl. rewrite Hlk. exact IH.
Qed.

(** ⇓ IS A PRECISION REFINEMENT: [⇓ˢP ⊑ P].  Every definition ⇓ unfolded is
    re-folded by [ad_refine_syn__flex_r], and the recursion INTO a definition's
    own definitions — which is not structural — is exactly what
    [a_tyequiv_to_downarrow_mono] already performs at the TYPE level, so the
    variable row delegates to [tyequiv_mono_refine_syn] and the induction here
    stays structural.  This is the transport [Flex-SkipRigid]'s package needs:
    its IH runs at the normalized counterpart [⇓ᵇQ], and the motive's PRECISION
    conjunct has to come back to [Q]. *)
Lemma ad_precise_downarrow : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  a_wf_aenv Θ ->
  (forall α, α `in` Δ -> α `notin` dom Θ) ->
  Θ ⨟ Δ ⊢ₚᵣᵃ (⇓ˢ[ Θ ] P) ⊑ P.
Proof.
  unfold ad_precise.
  intros Θ Δ P H; induction H; intros Hwf HΔ; simpl.
  - apply ad_refine_syn__unit.
  - (* var *)
    destruct H as [HαΔ | Hbt].
    + assert (Hn : α `notin` dom (aenv_msubst Θ)).
      { pose proof (dom_aenv_msubst Θ) as h. pose proof (HΔ α HαΔ) as h2.
        clear - h h2. fsetdec. }
      rewrite msubst_lookup_notin by exact Hn. simpl.
      apply ad_refine_syn__var. left; exact HαΔ.
    + assert (Hwfv : a_wf_ptyp Θ (ptyp_var_f α))
        by (apply a_wf_ptyp__var; exact Hbt).
      assert (Hmv : mono_ptyp (ptyp_var_f α)) by (apply mono_ptyp__var).
      assert (Hmd : mono_ptyp (⇓ᵗ[ Θ ] (ptyp_var_f α)))
        by (apply mono_downarrow; [ exact Hwf | exact Hwfv | exact Hmv ]).
      assert (Hwfd : a_wf_ptyp Θ (⇓ᵗ[ Θ ] (ptyp_var_f α)))
        by (apply a_wf_ptyp_downarrow_mono;
            [ exact Hwf | exact Hwfv | exact Hmv ]).
      assert (Heq : Θ ⊢ (ptyp_var_f α) ≡ᵗ (⇓ᵗ[ Θ ] (ptyp_var_f α)))
        by (apply a_tyequiv_to_downarrow_mono;
            [ exact Hwf | exact Hwfv | exact Hmv ]).
      change (pskl_to_bskl_inh (ptyp_to_pskl (msubst_lookup (aenv_msubst Θ) α)))
        with (pskl_to_bskl_inh (ptyp_to_pskl (⇓ᵗ[ Θ ] (ptyp_var_f α)))).
      rewrite (mono_inh_eq_syn Hmd).
      change (bskl_var_f α) with (ptyp_to_bskl_syn (ptyp_var_f α)).
      eapply tyequiv_mono_refine_syn;
        [ exact Hwf | exact Hmd | exact Hmv
        | apply a_tyequiv__sym; exact Heq
        | intros γ Hγ; eapply a_wf_ptyp_ftv_tvarish; [ exact Hwfd | exact Hγ ] ].
  - (* arrow *)
    apply ad_refine_syn__arrow;
      [ apply IHa_wf_pskl1 | apply IHa_wf_pskl2 ]; solve [ exact Hwf | exact HΔ ].
  - (* all *)
    apply ad_refine_syn__all
      with (L := L `union` dom Θ `union` Δ `union` dom (aenv_msubst Θ)).
    intros α Hα.
    assert (Heq : msubst_pskl (aenv_msubst Θ)
                    (open_pskl_wrt_pskl P (pskl_var_f α))
                  = open_pskl_wrt_pskl (msubst_pskl (aenv_msubst Θ) P)
                      (pskl_var_f α))
      by (apply msubst_pskl_open_lc_local;
          [ apply aenv_msubst_lc; exact Hwf | clear - Hα; fsetdec ]).
    repeat rewrite <- pskl_to_bskl_inh_open.
    rewrite <- Heq.
    apply H0; [ clear - Hα; fsetdec | exact Hwf | ].
    intros β Hβ.
    destruct (β == α) as [-> | Hne]; [ clear - Hα; fsetdec | ].
    apply HΔ. clear - Hβ Hne; fsetdec.
  - (* hole *)
    replace (pskl_to_bskl_inh pskl_hole)
      with (pskl_to_bskl_syn pskl_hole) at 2 by reflexivity.
    apply ad_refine_syn__hole. apply a_wf_pskl__hole.
  - (* tophole *)
    apply ad_refine_syn__tophole_keep;
      [ apply guarded_pskl_to_bskl_inh; exact H | ].
    eapply ad_refine_syn_delta_mono;
      [ apply IHa_wf_pskl;
          [ exact Hwf | intros β Hβ; exfalso; clear - Hβ; fsetdec ]
      | clear; fsetdec ].
Qed.

(* ===================================================================== *)
(*  (M)  P7a ROW — Flex-SkipRigid — the LAST row of P7a                    *)
(*                                                                        *)
(*  This is the row [a_inc]'s POSITIONALITY makes different from the other *)
(*  four.  [a_inc__flex] / [a_inc__flex_def] keep the TARGET fixed, so     *)
(*  [Flex-Skip] / [Flex-Depend] transport their solution-side premises     *)
(*  verbatim; [a_inc__tvar] does not — [κ ∷ (Ξ ++ (β ~ tvar) ++ Θ0) ⊑ Θ]   *)
(*  forces [Θ = Ξv ++ (β ~ tvar) ++ Θ'] with [κb ∷ Θ0 ⊑ Θ']               *)
(*  ([a_inc_tvar_inv]), so the IH runs at the TRUNCATION Θ' and every      *)
(*  solution-side premise has to move there.  [κb ∷ Θ0 ⊑ Θ] is not merely  *)
(*  unproved but FALSE once Θ0 carries a rigid or term entry.             *)
(*                                                                        *)
(*  The move is §(L0) + §(L1) + §(L), in that order: ⇓-NORMALIZE (the      *)
(*  junk block above β is exactly what ⇓ unfolds), then STRENGTHEN.  The   *)
(*  ftv hypotheses §(L) needs come out of the join's confinement           *)
(*  ([sub_gv_bskl_downarrow_mono_scoped]) for the counterpart and out of   *)
(*  [refine_syn_f_downarrow_source_ftv] for the fill's source.  The rest   *)
(*  is the consistency walk's [Assign-SkipRigid] transcribed              *)
(*  (prop_consis_complete.v:5091-5355): [a_inc_downarrow_prefix] over the  *)
(*  Ξ-images (confined by the motive's [dom Ξ ⊆ ftv P0]), the junk swap    *)
(*  for the rule's Barendregt premise, and [a_inc__tvar] /                 *)
(*  [a_inc_equiv_mid_insert_tvar] / [a_inc_equiv_self_downarrow] for the   *)
(*  package.                                                              *)
(*                                                                        *)
(*  ⚙ The ONE obligation the consistency walk does not have is the         *)
(*  motive's PRECISION conjunct: the IH proves it against [⇓ᵇQ] and the    *)
(*  conclusion wants it against [Q].  [ad_precise_downarrow] (§(L1)) is    *)
(*  that transport, composed by [ad_refine_syn_trans].                     *)
(* ===================================================================== *)

Lemma a_sub_flex_complete_skip_rigid : forall n NM M Θ0 Ξ α β P0 R' Ψ Θ κ Q,
  (* length-guarded, as in [a_sub_flex_complete_depend] *)
  (forall Ξ' α' P0' R'' Ψ' Θ'' κ' Q',
     length Ξ' <= S (length Ξ) ->
     sub_flex_complete_concl n NM M Θ0 Ξ' α' P0' R'' Ψ' Θ'' κ' Q') ->
  α <> β ->
  β `notin` ftvar_in_pskl P0 ->
  sub_flex_complete_concl n NM M ((β ~ abind_tvar) ++ Θ0) Ξ α P0
    R' Ψ Θ κ Q.
Proof.
  intros n NM M Θ0 Ξ α β P0 R' Ψ Θ κ Q IH Hne Hnin.
  unfold sub_flex_complete_concl in *.
  intros HdeclsΞ HdomΞ Hwf Hwfth HwfP0 Hfα HmodSK HmodTY Hinc Hslack HD Hrs
         HwfQ.
  (* ---- 0. the stripped context ---- *)
  assert (Huq : uniq (Ξ ++ (β ~ abind_tvar) ++ Θ0))
    by (apply a_wf_aenv_uniq; exact Hwf).
  assert (HβΞΘ0 : β `notin` dom (Ξ ++ Θ0)).
  { clear - Huq. simpl_env in Huq. destruct_uniq.
    unfold disjoint in *. simpl_env in *. fsetdec. }
  assert (Hwf' : a_wf_aenv (Ξ ++ Θ0))
    by (eapply a_wf_aenv_strip_mid; [ exact HdeclsΞ | exact Hwf ]).
  assert (Huq' : uniq (Ξ ++ Θ0)) by (apply a_wf_aenv_uniq; exact Hwf').
  assert (HwfΘ0 : a_wf_aenv Θ0) by (eapply a_wf_aenv_app_r; exact Hwf').
  assert (HwfP0' : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P0)
    by (eapply a_wf_pskl_strip_mid; [ exact HwfP0 | exact Hnin ]).
  (* the subject survives the head strip: the rule's own [α <> β] *)
  assert (Hfα0 : a_flex_tvar Θ0 α).
  { destruct Hfα as [Hb | [τ0 Hb]]; [ left | right; exists τ0 ];
      (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He _] | Hb'];
       [ exfalso; apply Hne; exact He | exact Hb' ]). }
  assert (Hαb0 : a_binds_tvar α Θ0)
    by (destruct Hfα0 as [h | [τ0 h]];
        [ right; left; exact h | right; right; exists τ0; exact h ]).
  assert (Hαb' : a_binds_tvar α (Ξ ++ Θ0))
    by (destruct (a_flex_tvar_app_weaken Ξ Hfα0) as [h | [τ0 h]];
        [ right; left; exact h | right; right; exists τ0; exact h ]).
  assert (Hαbfull : a_binds_tvar α (Ξ ++ (β ~ abind_tvar) ++ Θ0)).
  { destruct (a_flex_tvar_app_weaken (Ξ ++ (β ~ abind_tvar)) Hfα0)
      as [h | [τ0 h]];
      [ right; left | right; right; exists τ0 ]; simpl_env in h; exact h. }
  assert (HuqΘ : uniq Θ) by (apply a_wf_aenv_uniq; exact Hwfth).
  (* ---- 1. peel Ξ off κ, then invert the RIGID middle ---- *)
  destruct (@a_inc_strip_decls_prefix Ξ ((β ~ abind_tvar) ++ Θ0) κ Θ HdeclsΞ
              Hinc)
    as [κa [κb [Heqκ [Hdκa Hincxb]]]].
  destruct (a_inc_tvar_inv Hincxb) as [Ξv [Θ' [HeqΘ [HsufΞv Hincb]]]].
  assert (HwfΘ' : a_wf_aenv Θ').
  { rewrite HeqΘ in Hwfth.
    eapply a_wf_aenv_app_r with (Θp := Ξv ++ (β ~ abind_tvar)).
    simpl_env. simpl_env in Hwfth. exact Hwfth. }
  assert (HeqW : (Ξv ++ (β ~ abind_tvar)) ++ Θ' = Θ)
    by (rewrite HeqΘ; simpl_env; reflexivity).
  assert (Hsub' : forall y c, binds y c Θ' -> binds y c Θ).
  { intros y c Hb. rewrite HeqΘ. apply binds_app_3. apply binds_app_3.
    exact Hb. }
  assert (Hincb_n : msubst_compose (aenv_msubst Θ) κb ∷ Θ0 ⊑ Θ').
  { pose proof (a_inc_self_downarrow Hincb (Ξv ++ (β ~ abind_tvar))) as Hs.
    rewrite HeqW in Hs.
    apply Hs; [ exact Hwfth | exact HuqΘ | exact HwfΘ0 ]. }
  (* ---- 2. the subject is a MONO painting, and ⇓ pins it to [κα̂] ---- *)
  assert (Hmκα : mono_ptyp (msubst_lookup κ α))
    by (eapply a_inc_lookup_mono; exact Hinc).
  assert (Hwfκα : a_wf_ptyp Θ (msubst_lookup κ α))
    by (eapply a_inc_lookup_wf; [ exact Hinc | exact Hwf | exact Hαbfull ]).
  destruct (a_uskl_tyequiv_mono_r_inv Hslack
              (eq_refl (ptyp_to_uskl_syn (msubst_lookup κ α))) Hmκα Hwfκα)
    as [τ' [HeqR' [Hmτ' [Hwfτ' Heqττ']]]].
  subst R'.
  assert (Hddτ' : ⇓ᵗ[ Θ ] τ' = ⇓ᵗ[ Θ ] (msubst_lookup κ α))
    by (apply a_tyequiv_downarrow; [ exact Hwfth | exact Heqττ' ]).
  (* ---- 3. the subject's image is scoped in the TRUNCATION ---- *)
  assert (Hακa : α `notin` dom κa).
  { rewrite Hdκa.
    assert (hd : α `in` dom Θ0)
      by (destruct Hfα0 as [Hb | [? Hb]]; apply binds_In in Hb; exact Hb).
    clear - Huq hd. simpl_env in Huq. solve_uniq. }
  assert (Hwfα' : a_wf_ptyp Θ' (msubst_lookup κ α)).
  { rewrite Heqκ. rewrite (msubst_lookup_app_notin κa κb Hακa).
    eapply a_inc_lookup_wf; [ exact Hincb | exact HwfΘ0 | exact Hαb0 ]. }
  assert (Hftvα : ftvar_in_ptyp (msubst_lookup κ α) [<=] dom Θ')
    by (apply a_wf_ptyp_ftv_dom; exact Hwfα').
  assert (Hddα : ⇓ᵗ[ Θ ] (msubst_lookup κ α) = ⇓ᵗ[ Θ' ] (msubst_lookup κ α)).
  { rewrite <- HeqW.
    apply downarrow_app_agree_ptyp; [ rewrite HeqW; exact HuqΘ | exact Hftvα ]. }
  assert (HO1 : ftvar_in_ptyp (⇓ᵗ[ Θ ] τ') [<=] dom Θ').
  { rewrite Hddτ'. rewrite Hddα. apply a_wf_ptyp_ftv_dom.
    apply a_wf_ptyp_downarrow_mono;
      [ exact HwfΘ' | exact Hwfα' | exact Hmκα ]. }

  (* ---- 4. the JOIN's ⇓-confinement, and the FILL's source below it ---- *)
  assert (Hmono_img : forall γ, mono_ptyp (msubst_lookup (aenv_msubst Θ) γ))
    by (intros; apply aenv_msubst_image_mono; exact Hwfth).
  assert (HO2 : ftvar_in_bskl (⇓ᵇ[ Θ ] Q) [<=] dom Θ').
  { eapply sub_gv_bskl_downarrow_mono_scoped;
      [ exact HD | exact Hwfth | reflexivity | exact Hmτ' | exact HO1 ]. }
  assert (Heqinh : ⇓ᵇ[ Θ ] (pskl_to_bskl_inh (msubst_pskl κ P0))
                   = pskl_to_bskl_inh (⇓ˢ[ Θ ] (msubst_pskl κ P0)))
    by (apply msubst_bskl_pskl_to_bskl_inh; exact Hmono_img).
  assert (HO3 : ftvar_in_pskl (⇓ˢ[ Θ ] (msubst_pskl κ P0)) [<=] dom Θ').
  { pose proof (refine_syn_f_downarrow_source_ftv Hrs Hwfth
                  ltac:(intros x Hx; exfalso; clear - Hx; fsetdec)) as h.
    rewrite Heqinh in h. rewrite ftvar_in_bskl_inh in h.
    clear - h HO2. fsetdec. }
  (* ---- 5. the ⇓-composed increase at the TRUNCATION ---- *)
  assert (Hside : forall γ, γ `in` ftvar_in_pskl P0 ->
            γ `in` dom κ \/ γ `notin` dom (aenv_msubst Θ)).
  { intros γ Hγ.
    destruct (AtomSetProperties.In_dec γ (dom κ)) as [Hin | Hni];
      [ left; exact Hin | right ].
    intro Hin2. apply aenv_msubst_dom_inv in Hin2.
    destruct (a_wf_pskl_ftv_tvarish HwfP0 Hγ) as [Hemp | Hbt];
      [ clear - Hemp; fsetdec | ].
    destruct Hbt as [Htv | [Hfm | [τ0 Hfd]]].
    - assert (HtvΘ : binds γ abind_tvar Θ)
        by (eapply a_inc_binds_tvar; [ exact Hinc | exact Htv ]).
      destruct Hin2 as [Hb | [τ1 Hb]];
        (pose proof (binds_unique _ _ _ _ _ HtvΘ Hb HuqΘ) as Heqb;
         discriminate Heqb).
    - assert (Hyd : γ `in` dom κ)
        by (eapply a_inc_flex_dom; [ exact Hinc | exact Hwf | left; exact Hfm ]).
      contradiction.
    - assert (Hyd : γ `in` dom κ)
        by (eapply a_inc_flex_dom;
            [ exact Hinc | exact Hwf | right; exists τ0; exact Hfd ]).
      contradiction. }
  assert (Hgr : forall γ, γ `in` dom κa ->
            ftvar_in_ptyp (⇓ᵗ[ Θ ] (msubst_lookup κa γ)) [<=] dom Θ').
  { intros γ Hγ.
    assert (HXP : γ `in` ftvar_in_pskl P0)
      by (apply HdomΞ; rewrite <- Hdκa; exact Hγ).
    assert (Hγκ : γ `in` dom κ)
      by (rewrite Heqκ; rewrite dom_app; clear - Hγ; fsetdec).
    assert (Heqlk : ⇓ᵗ[ Θ ] (msubst_lookup κa γ)
                   = msubst_lookup (msubst_compose (aenv_msubst Θ) κ) γ).
    { rewrite (msubst_lookup_compose (aenv_msubst Θ) κ (or_introl Hγκ)).
      f_equal. rewrite Heqκ. symmetry. apply msubst_lookup_app_in; exact Hγ. }
    rewrite Heqlk.
    eapply AtomSetProperties.subset_trans;
      [ apply (msubst_pskl_ftv_lower
                 (msubst_compose (aenv_msubst Θ) κ) P0 HXP) | ].
    rewrite msubst_pskl_compose; [ exact HO3 | exact Hside ]. }
  assert (Hinc_sub : msubst_compose (aenv_msubst Θ) κ ∷ (Ξ ++ Θ0) ⊑ Θ').
  { assert (HincR : κa ++ κb ∷ (Ξ ++ (β ~ abind_tvar) ++ Θ0) ⊑ Θ)
      by (rewrite <- Heqκ; exact Hinc).
    rewrite Heqκ. rewrite msubst_compose_app.
    eapply a_inc_downarrow_prefix;
      [ exact HdeclsΞ | exact HincR | exact Huq | exact Hdκa | exact Hincb_n
      | exact Hwfth | exact HuqΘ | exact Hsub' | exact Hgr ]. }
  (* ---- 6. the JOIN, ⇓-normalized and strengthened ---- *)
  assert (Hmd : mono_ptyp (⇓ᵗ[ Θ ] τ'))
    by (apply mono_downarrow; [ exact Hwfth | exact Hwfτ' | exact Hmτ' ]).
  assert (Hwfd' : a_wf_ptyp Θ' (⇓ᵗ[ Θ ] τ')).
  { rewrite Hddτ'. rewrite Hddα.
    apply a_wf_ptyp_downarrow_mono;
      [ exact HwfΘ' | exact Hwfα' | exact Hmκα ]. }
  assert (Hjoin' : ad_pat_sub_gv n NM (mode_fn M) Ψ Θ'
                     (ptyp_to_uskl_syn (⇓ᵗ[ Θ ] τ')) (⇓ᵇ[ Θ ] Q)).
  { eapply ad_pat_sub_gv_mono_strengthen;
      [ eapply sub_gv_downarrow_mono;
          [ exact HD | exact Hwfth | reflexivity | exact Hmτ' | exact Hwfτ' ]
      | reflexivity | exact Hmd | exact HuqΘ | exact HwfΘ' | exact Hsub'
      | intros γ Hγ; clear - HO1 Hγ; fsetdec
      | intros γ Hγ; clear - HO2 Hγ; fsetdec ]. }
  (* ---- 7. the FILL, ⇓-normalized and strengthened ---- *)
  assert (Hrs' : ad_refine_syn_f empty Θ' empty
                   (pskl_to_bskl_inh
                      (msubst_pskl (msubst_compose (aenv_msubst Θ) κ) P0))
                   (⇓ᵇ[ Θ ] Q)).
  { rewrite (msubst_pskl_compose (aenv_msubst Θ) κ P0 Hside).
    pose proof (refine_syn_f_downarrow Hrs Hwfth
                  ltac:(intros x Hx; exfalso; clear - Hx; fsetdec)) as h.
    rewrite Heqinh in h.
    eapply ad_refine_syn_f_strengthen;
      [ exact h | exact HuqΘ | exact HwfΘ' | exact Hsub'
      | intros x Hx; exfalso; clear - Hx; fsetdec
      | intros γ Hγ; right; rewrite ftvar_in_bskl_inh in Hγ;
        clear - HO3 Hγ; fsetdec
      | intros γ Hγ; right; clear - HO2 Hγ; fsetdec ]. }
  (* ---- 8. the counterpart's wf at the truncation ---- *)
  assert (HwfQ' : Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl (⇓ᵇ[ Θ ] Q))).
  { rewrite bskl_to_pskl_msubst_bskl.
    eapply a_wf_pskl_strengthen;
      [ apply a_wf_pskl_downarrow;
          [ exact HwfQ | exact Hwfth
          | intros x Hx; exfalso; clear - Hx; fsetdec ]
      | exact HuqΘ | intros x Hx; exfalso; clear - Hx; fsetdec | exact Hsub'
      | intros γ Hγ; right;
        rewrite <- bskl_to_pskl_msubst_bskl in Hγ;
        rewrite ftvar_in_pskl_bskl_to_pskl in Hγ;
        clear - HO2 Hγ; fsetdec ]. }
  (* ---- 9. the slack, at the ⇓-composed metasubstitution ---- *)
  assert (Hακdom : α `in` dom κ).
  { rewrite Heqκ. rewrite dom_app.
    assert (Hαd : α `in` dom κb)
      by (eapply a_inc_flex_dom;
          [ exact Hincb | exact HwfΘ0 | exact Hfα0 ]).
    clear - Hαd. fsetdec. }
  assert (Hslack' : Θ' ⊢ (ptyp_to_uskl_syn (⇓ᵗ[ Θ ] τ'))
              ≡ᵘ (ptyp_to_uskl_syn
                    (msubst_lookup (msubst_compose (aenv_msubst Θ) κ) α))).
  { rewrite (msubst_lookup_compose (aenv_msubst Θ) κ (or_introl Hακdom)).
    rewrite <- Hddτ'.
    apply a_uskl_tyequiv__mono;
      [ exact Hmd | exact Hmd | exact Hwfd' | exact Hwfd'
      | apply a_tyequiv__refl; apply mono_ptyp_lc; exact Hmd ]. }

  (* ---- 10. the IH at the TRUNCATED problem ---- *)
  destruct (IH Ξ α P0 (ptyp_to_uskl_syn (⇓ᵗ[ Θ ] τ')) Ψ Θ'
              (msubst_compose (aenv_msubst Θ) κ) (⇓ᵇ[ Θ ] Q) ltac:(lia)
              HdeclsΞ HdomΞ Hwf' HwfΘ' HwfP0' Hfα0 HmodSK HmodTY
              Hinc_sub Hslack' Hjoin' Hrs' HwfQ')
    as [P1 [Θ1 [Hrun Hopt]]].
  (* ---- 11. the junk rename, and the re-attachment ---- *)
  destruct (a_sub_flex_sound_thm Hrun HdeclsΞ Hwf' HwfP0' Hαb' HmodSK HmodTY)
    as [[[w [Hidw Hincw]] Hdefs] HwfΘ1].
  assert (HscP1 : a_scope_pskl Θ1 P1)
    by (eapply a_sub_flex_out_scope;
        [ exact Hrun | exact HdeclsΞ | exact Hwf' | exact HwfP0'
        | exact Hαb' | exact HmodSK | exact HmodTY ]).
  assert (HβflexΘ1 : forall bd, binds β bd Θ1 ->
            bd = abind_flex_mono \/ exists τ, bd = abind_flex_mono_def τ)
    by (eapply a_sub_flex_out_flex_only;
        [ exact Hrun | exact HdeclsΞ | exact Hwf' | exact HwfP0'
        | exact Hαb' | exact HmodSK | exact HmodTY | exact HβΞΘ0 ]).
  assert (HβΞ : β `notin` ftvar_in_aenv Ξ).
  { pose proof (a_decls_no_ftvar HdeclsΞ) as h.
    clear - h HβΞΘ0. simpl_env in HβΞΘ0. fsetdec. }
  assert (HβΘ0 : β `notin` ftvar_in_aenv Θ0).
  { pose proof (a_wf_aenv_ftvar_dom HwfΘ0) as h.
    clear - h HβΞΘ0. simpl_env in HβΞΘ0. fsetdec. }
  destruct (atom_fresh (dom Θ1 `union` ftvar_in_aenv Θ1
                        `union` ftvar_in_pskl P1 `union` dom Ξ
                        `union` dom Θ0 `union` ftvar_in_aenv Θ0
                        `union` ftvar_in_aenv Ξ `union` ftvar_in_pskl P0
                        `union` singleton α `union` singleton β))
    as [β1 Fr].
  assert (Hrunsw : a_sub_flex NM M P0 Θ0 Ξ α
                     (swap_pskl β β1 P1) (swap_aenv β β1 Θ1)).
  { apply (a_sub_flex_swap_junk β β1 NM M P0 Θ0 Ξ α P1 Θ1 Hrun);
      [ intro Hc; subst; exact (Hne eq_refl)
      | clear - Fr; fsetdec
      | clear - HβΘ0 HβΞ Hnin; fsetdec
      | clear - Fr; fsetdec ]. }
  exists (swap_pskl β β1 P1), ((β ~ abind_tvar) ++ swap_aenv β β1 Θ1).
  split.
  { apply a_sub_flex__skip_rigid;
      [ exact Hne | exact Hnin
      | apply swap_junk_dom_out; clear - Fr; fsetdec
      | exact Hrunsw ]. }
  (* ---- 12. the package ---- *)
  intros κf Hidf Hincf.
  assert (Hincf' : κf ∷ (Ξ ++ Θ0) ⊑ swap_aenv β β1 Θ1)
    by (eapply a_inc_tvar_mid_strip_id;
        [ exact HdeclsΞ | exact Huq | exact Hidf | exact Hincf ]).
  assert (Heqw : w = κf)
    by (eapply is_id_inc_unique;
        [ exact Hincw | exact Hidw | exact Hincf' | exact Hidf ]).
  subst w.
  destruct (Hopt κf Hidf Hincw) as [ζ [Hζ [Hie Hprec]]].
  assert (Hkeysζ : forall γ, List.In γ (List.map fst ζ) -> γ `in` dom Θ1)
    by (intros γ hγ; eapply a_inc_keys_dom; [ exact Hζ | exact hγ ]).
  assert (Hkeysf : forall γ, List.In γ (List.map fst κf) ->
            γ `in` dom (Ξ ++ Θ0))
    by (intros γ hγ; eapply a_inc_keys_dom; [ exact Hincf' | exact hγ ]).
  assert (Hkey : forall γ, List.In γ (List.map fst κf) -> γ <> β /\ γ <> β1).
  { intros γ hγ. pose proof (Hkeysf γ hγ) as hd.
    split; [ intro Hc; subst; clear - hd HβΞΘ0; fsetdec
           | intro Hc; subst; clear - hd Fr; simpl_env in hd; fsetdec ]. }
  exists (kswap_msubst β β1 ζ).
  split.
  { (* the increase : [a_inc__tvar] over the swapped sub-output *)
    rewrite HeqΘ. apply a_inc__tvar; [ | exact HsufΞv ].
    apply (a_inc_kswap β β1 ζ Θ1 Θ' Hζ);
      [ clear - Fr; fsetdec | exact HwfΘ1 | clear - Fr; fsetdec
      | exact HβflexΘ1 ]. }
  split.
  { (* the equivalence *)
    rewrite (msubst_compose_kswap_id β β1 ζ κf Hidf Hkey).
    destruct (@a_inc_strip_decls_prefix Ξ Θ0 κf (swap_aenv β β1 Θ1)
                HdeclsΞ Hincf')
      as [κf1 [κf2 [Heqκf [Hdκf1 _]]]].
    assert (Hmi : a_inc_equiv (Ξ ++ (β ~ abind_tvar) ++ Θ0)
                    (msubst_compose (aenv_msubst Θ) κ)
                    (msubst_compose ζ κf)
                    (Ξv ++ (β ~ abind_tvar) ++ Θ')).
    { rewrite Heqκ. rewrite (msubst_compose_app (aenv_msubst Θ) κa κb).
      rewrite Heqκf. rewrite (msubst_compose_app ζ κf1 κf2).
      apply a_inc_equiv_mid_insert_tvar;
        [ exact HdeclsΞ | exact Huq'
        | rewrite dom_msubst_compose; exact Hdκa
        | rewrite dom_msubst_compose; exact Hdκf1
        | exact HsufΞv | ].
      rewrite Heqκ in Hie.
      rewrite (msubst_compose_app (aenv_msubst Θ) κa κb) in Hie.
      rewrite Heqκf in Hie.
      rewrite (msubst_compose_app ζ κf1 κf2) in Hie.
      exact Hie. }
    rewrite <- HeqΘ in Hmi.
    eapply a_inc_equiv_trans; [ | exact Hwfth | exact Hmi ].
    pose proof (a_inc_equiv_self_downarrow Hinc (@nil (atom * abind)))
      as Hself.
    simpl in Hself. apply Hself; [ exact Hwfth | exact HuqΘ | exact Hwf ]. }
  { (* the precision : the swap erases, then the package comes back from
       [(Θ', ⇓ᵇQ)] to [(Θ, Q)] — weaken the context, then compose with
       [⇓ˢ(⌊Q⌋) ⊑ ⌊Q⌋] *)
    rewrite (msubst_bskl_kswap_paint β β1 ζ P1);
      [ | clear - Fr; fsetdec
        | intro hc; pose proof (Hkeysζ β1 hc) as h; clear - h Fr; fsetdec
        | clear - Fr; fsetdec
        | destruct (AtomSetProperties.In_dec β (ftvar_in_pskl P1))
            as [hin | hout]; [ right | left; exact hout ];
          assert (hbt : a_binds_tvar β Θ1)
            by (eapply a_scope_pskl_ftv_binds; [ exact HscP1 | exact hin ]);
          destruct hbt as [hbt | [hbt | [τ0 hbt]]];
          [ exfalso; destruct (HβflexΘ1 abind_tvar hbt) as [hc | [τ1 hc]];
              discriminate
          | eapply a_inc_flex_in_keys; [ exact Hζ | left; exact hbt ]
          | eapply a_inc_flex_in_keys; [ exact Hζ | right; eexists; exact hbt ] ] ].
    assert (HprecΘ : Θ ⨟ empty ⊢ₚᵣᵃ (msubst_bskl ζ (pskl_to_bskl_syn P1))
                       ⊑ (bskl_to_pskl (⇓ᵇ[ Θ ] Q))).
    { unfold ad_precise in *.
      apply ad_refine_syn_f_forget with (F := empty).
      eapply ad_refine_syn_f_weaken_ctx;
        [ apply ad_refine_syn_f_empty_intro; exact Hprec | exact Hsub' ]. }
    unfold ad_precise in *.
    rewrite (bskl_to_pskl_msubst_bskl (aenv_msubst Θ) Q) in HprecΘ.
    eapply ad_refine_syn_trans;
      [ apply ad_precise_downarrow;
          [ exact HwfQ | exact Hwfth
          | intros x Hx; exfalso; clear - Hx; fsetdec ]
      | exact Hwfth
      | intros x Hx; exfalso; clear - Hx; fsetdec
      | rewrite bskl_to_pskl_pskl_to_bskl_inh; exact HwfQ
      | exact HprecΘ ]. }
Qed.

Print Assumptions a_sub_flex_complete_skip_rigid.

(* ===================================================================== *)
(*  §(N) Flex-SkipTmVar — the TERM-VARIABLE head, type binding            *)
(*                                                                        *)
(*  The twin of §(M) [a_sub_flex_complete_skip_rigid]: [a_inc__var]        *)
(*  shrinks the [a_inc] TARGET exactly as [a_inc__tvar] does, so the walk  *)
(*  runs at the truncation [Θ'] and every step of §(M) transcribes.  TWO   *)
(*  differences, both real:                                               *)
(*                                                                        *)
(*  ⭐ The rule carries NO [α ≠ β] and NO [β ∉ ftv P0] premise (nor does    *)
(*  the twin walk's [Assign-SkipTmVar]) — both are DERIVED, because a term *)
(*  entry is never [a_binds_tvar]: under [uniq] neither the flexible       *)
(*  subject nor a free variable of the well-formed [P0] can be β.          *)
(*                                                                        *)
(*  ⭐ A term entry has a PAYLOAD, so [a_inc__var] /                        *)
(*  [a_inc_equiv_mid_insert_var] demand a SEMANTIC MIDDLE                  *)
(*  [Θ' ⊢ A' ≡ᵗ κQv] that the rigid row has no counterpart for.  The       *)
(*  consistency walk's [Assign-SkipTmVar] proves exactly it                *)
(*  (prop_consis_complete.v:5595-5690).  ONE step beyond that twin:        *)
(*  subtyping re-attaches through the JUNK SWAP, so the witness is         *)
(*  [kswap_msubst β β1 ζ] and the middle is read back through              *)
(*  [msubst_ptyp_kswap] — free, since β and β1 are both fresh for a        *)
(*  payload scoped in [Θ0].                                               *)
(* ===================================================================== *)

Lemma a_sub_flex_complete_skip_tm_var :
  forall n NM M Θ0 Ξ α β Qv P0 R' Ψ Θ κ Q,
  (* length-guarded, as in [a_sub_flex_complete_skip_rigid] *)
  (forall Ξ' α' P0' R'' Ψ' Θ'' κ' Q',
     length Ξ' <= S (length Ξ) ->
     sub_flex_complete_concl n NM M Θ0 Ξ' α' P0' R'' Ψ' Θ'' κ' Q') ->
  sub_flex_complete_concl n NM M ((β ~ abind_var_typ Qv) ++ Θ0) Ξ α P0
    R' Ψ Θ κ Q.
Proof.
  intros n NM M Θ0 Ξ α β Qv P0 R' Ψ Θ κ Q IH.
  unfold sub_flex_complete_concl in *.
  intros HdeclsΞ HdomΞ Hwf Hwfth HwfP0 Hfα HmodSK HmodTY Hinc Hslack HD Hrs
         HwfQ.
  (* ---- 0. the stripped context, and the two DERIVED premises ---- *)
  assert (Huq : uniq (Ξ ++ (β ~ abind_var_typ Qv) ++ Θ0))
    by (apply a_wf_aenv_uniq; exact Hwf).
  assert (HβΞΘ0 : β `notin` dom (Ξ ++ Θ0)).
  { clear - Huq. simpl_env in Huq. destruct_uniq.
    unfold disjoint in *. simpl_env in *. fsetdec. }
  (* the subject survives the head strip: a term entry is not flexible *)
  assert (Hfα0 : a_flex_tvar Θ0 α).
  { destruct Hfα as [Hb | [τ0 Hb]];
      [ destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He1 He2] | Hb'];
        [ discriminate | left; exact Hb' ]
      | destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He1 He2] | Hb'];
        [ discriminate | right; exists τ0; exact Hb' ] ]. }
  assert (HαΘ0 : α `in` dom Θ0)
    by (destruct Hfα0 as [Hb | [? Hb]]; apply binds_In in Hb; exact Hb).
  assert (Hne : α <> β).
  { intro Hc; subst. clear - HαΘ0 HβΞΘ0. simpl_env in HβΞΘ0. fsetdec. }
  (* and no free variable of the well-formed [P0] is a term variable *)
  assert (Hnin : β `notin` ftvar_in_pskl P0).
  { intro Hx. destruct (a_wf_pskl_ftv_tvarish HwfP0 Hx) as [Hemp | Hbt];
      [ clear - Hemp; fsetdec | ].
    assert (Hbx : binds β (abind_var_typ Qv)
                    (Ξ ++ (β ~ abind_var_typ Qv) ++ Θ0))
      by (apply binds_app_3; left; reflexivity).
    destruct Hbt as [Hb | [Hb | [τ0 Hb]]];
      (pose proof (binds_unique _ _ _ _ _ Hb Hbx Huq) as Heqb;
       discriminate Heqb). }
  assert (Hwf' : a_wf_aenv (Ξ ++ Θ0))
    by (eapply a_wf_aenv_strip_mid; [ exact HdeclsΞ | exact Hwf ]).
  assert (Huq' : uniq (Ξ ++ Θ0)) by (apply a_wf_aenv_uniq; exact Hwf').
  assert (HwfΘ0 : a_wf_aenv Θ0) by (eapply a_wf_aenv_app_r; exact Hwf').
  assert (HwfP0' : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P0)
    by (eapply a_wf_pskl_strip_mid; [ exact HwfP0 | exact Hnin ]).
  (* the payload is scoped BELOW the entry *)
  assert (HwfaΘ0x : a_wf_aenv ((β ~ abind_var_typ Qv) ++ Θ0))
    by (eapply a_wf_aenv_app_r; exact Hwf).
  destruct (a_wf_aenv_var_typ_inv HwfaΘ0x) as [_ [HwfQv0 _]].
  assert (HwfQv : a_wf_ptyp (Ξ ++ Θ0) Qv)
    by (eapply a_wf_ptyp_weaken;
        [ intros ? ? Hb; apply binds_app_3; exact Hb | exact HwfQv0 ]).
  assert (HlcQv : lc_ptyp Qv) by (eapply a_wf_ptyp_lc; exact HwfQv0).
  assert (HftvQv : ftvar_in_ptyp Qv [<=] dom Θ0)
    by (apply a_wf_ptyp_ftv_dom; exact HwfQv0).
  assert (HβQv : β `notin` ftvar_in_ptyp Qv).
  { clear - HftvQv HβΞΘ0. simpl_env in HβΞΘ0. fsetdec. }
  assert (Hαb0 : a_binds_tvar α Θ0)
    by (destruct Hfα0 as [h | [τ0 h]];
        [ right; left; exact h | right; right; exists τ0; exact h ]).
  assert (Hαb' : a_binds_tvar α (Ξ ++ Θ0))
    by (destruct (a_flex_tvar_app_weaken Ξ Hfα0) as [h | [τ0 h]];
        [ right; left; exact h | right; right; exists τ0; exact h ]).
  assert (Hαbfull : a_binds_tvar α (Ξ ++ (β ~ abind_var_typ Qv) ++ Θ0)).
  { destruct (a_flex_tvar_app_weaken (Ξ ++ (β ~ abind_var_typ Qv)) Hfα0)
      as [h | [τ0 h]];
      [ right; left | right; right; exists τ0 ]; simpl_env in h; exact h. }
  assert (HuqΘ : uniq Θ) by (apply a_wf_aenv_uniq; exact Hwfth).
  (* ---- 1. peel Ξ off κ, then invert the TERM middle ---- *)
  destruct (@a_inc_strip_decls_prefix Ξ ((β ~ abind_var_typ Qv) ++ Θ0) κ Θ
              HdeclsΞ Hinc)
    as [κa [κb [Heqκ [Hdκa Hincxb]]]].
  destruct (a_inc_var_inv Hincxb)
    as [Ξv [A' [Θ' [HeqΘ [HeqA' [HsufΞv Hincb]]]]]].
  assert (HwfΘ' : a_wf_aenv Θ').
  { rewrite HeqΘ in Hwfth.
    eapply a_wf_aenv_app_r with (Θp := Ξv ++ (β ~ abind_var_typ A')).
    simpl_env. simpl_env in Hwfth. exact Hwfth. }
  assert (HeqW : (Ξv ++ (β ~ abind_var_typ A')) ++ Θ' = Θ)
    by (rewrite HeqΘ; simpl_env; reflexivity).
  assert (Hsub' : forall y c, binds y c Θ' -> binds y c Θ).
  { intros y c Hb. rewrite HeqΘ. apply binds_app_3. apply binds_app_3.
    exact Hb. }
  assert (Hincb_n : msubst_compose (aenv_msubst Θ) κb ∷ Θ0 ⊑ Θ').
  { pose proof (a_inc_self_downarrow Hincb (Ξv ++ (β ~ abind_var_typ A')))
      as Hs.
    rewrite HeqW in Hs.
    apply Hs; [ exact Hwfth | exact HuqΘ | exact HwfΘ0 ]. }
  (* ---- 2. the subject is a MONO painting, and ⇓ pins it to [κα̂] ---- *)
  assert (Hmκα : mono_ptyp (msubst_lookup κ α))
    by (eapply a_inc_lookup_mono; exact Hinc).
  assert (Hwfκα : a_wf_ptyp Θ (msubst_lookup κ α))
    by (eapply a_inc_lookup_wf; [ exact Hinc | exact Hwf | exact Hαbfull ]).
  destruct (a_uskl_tyequiv_mono_r_inv Hslack
              (eq_refl (ptyp_to_uskl_syn (msubst_lookup κ α))) Hmκα Hwfκα)
    as [τ' [HeqR' [Hmτ' [Hwfτ' Heqττ']]]].
  subst R'.
  assert (Hddτ' : ⇓ᵗ[ Θ ] τ' = ⇓ᵗ[ Θ ] (msubst_lookup κ α))
    by (apply a_tyequiv_downarrow; [ exact Hwfth | exact Heqττ' ]).
  (* ---- 3. the subject's image is scoped in the TRUNCATION ---- *)
  assert (Hακa : α `notin` dom κa).
  { rewrite Hdκa. clear - Huq HαΘ0. simpl_env in Huq. solve_uniq. }
  assert (Hwfα' : a_wf_ptyp Θ' (msubst_lookup κ α)).
  { rewrite Heqκ. rewrite (msubst_lookup_app_notin κa κb Hακa).
    eapply a_inc_lookup_wf; [ exact Hincb | exact HwfΘ0 | exact Hαb0 ]. }
  assert (Hftvα : ftvar_in_ptyp (msubst_lookup κ α) [<=] dom Θ')
    by (apply a_wf_ptyp_ftv_dom; exact Hwfα').
  assert (Hddα : ⇓ᵗ[ Θ ] (msubst_lookup κ α) = ⇓ᵗ[ Θ' ] (msubst_lookup κ α)).
  { rewrite <- HeqW.
    apply downarrow_app_agree_ptyp; [ rewrite HeqW; exact HuqΘ | exact Hftvα ]. }
  assert (HO1 : ftvar_in_ptyp (⇓ᵗ[ Θ ] τ') [<=] dom Θ').
  { rewrite Hddτ'. rewrite Hddα. apply a_wf_ptyp_ftv_dom.
    apply a_wf_ptyp_downarrow_mono;
      [ exact HwfΘ' | exact Hwfα' | exact Hmκα ]. }
  (* ---- 4. the JOIN's ⇓-confinement, and the FILL's source below it ---- *)
  assert (Hmono_img : forall γ, mono_ptyp (msubst_lookup (aenv_msubst Θ) γ))
    by (intros; apply aenv_msubst_image_mono; exact Hwfth).
  assert (HO2 : ftvar_in_bskl (⇓ᵇ[ Θ ] Q) [<=] dom Θ').
  { eapply sub_gv_bskl_downarrow_mono_scoped;
      [ exact HD | exact Hwfth | reflexivity | exact Hmτ' | exact HO1 ]. }
  assert (Heqinh : ⇓ᵇ[ Θ ] (pskl_to_bskl_inh (msubst_pskl κ P0))
                   = pskl_to_bskl_inh (⇓ˢ[ Θ ] (msubst_pskl κ P0)))
    by (apply msubst_bskl_pskl_to_bskl_inh; exact Hmono_img).
  assert (HO3 : ftvar_in_pskl (⇓ˢ[ Θ ] (msubst_pskl κ P0)) [<=] dom Θ').
  { pose proof (refine_syn_f_downarrow_source_ftv Hrs Hwfth
                  ltac:(intros x Hx; exfalso; clear - Hx; fsetdec)) as h.
    rewrite Heqinh in h. rewrite ftvar_in_bskl_inh in h.
    clear - h HO2. fsetdec. }
  (* ---- 5. the ⇓-composed increase at the TRUNCATION ---- *)
  assert (Hside : forall γ, γ `in` ftvar_in_pskl P0 ->
            γ `in` dom κ \/ γ `notin` dom (aenv_msubst Θ)).
  { intros γ Hγ.
    destruct (AtomSetProperties.In_dec γ (dom κ)) as [Hin | Hni];
      [ left; exact Hin | right ].
    intro Hin2. apply aenv_msubst_dom_inv in Hin2.
    destruct (a_wf_pskl_ftv_tvarish HwfP0 Hγ) as [Hemp | Hbt];
      [ clear - Hemp; fsetdec | ].
    destruct Hbt as [Htv | [Hfm | [τ0 Hfd]]].
    - assert (HtvΘ : binds γ abind_tvar Θ)
        by (eapply a_inc_binds_tvar; [ exact Hinc | exact Htv ]).
      destruct Hin2 as [Hb | [τ1 Hb]];
        (pose proof (binds_unique _ _ _ _ _ HtvΘ Hb HuqΘ) as Heqb;
         discriminate Heqb).
    - assert (Hyd : γ `in` dom κ)
        by (eapply a_inc_flex_dom; [ exact Hinc | exact Hwf | left; exact Hfm ]).
      contradiction.
    - assert (Hyd : γ `in` dom κ)
        by (eapply a_inc_flex_dom;
            [ exact Hinc | exact Hwf | right; exists τ0; exact Hfd ]).
      contradiction. }
  assert (Hgr : forall γ, γ `in` dom κa ->
            ftvar_in_ptyp (⇓ᵗ[ Θ ] (msubst_lookup κa γ)) [<=] dom Θ').
  { intros γ Hγ.
    assert (HXP : γ `in` ftvar_in_pskl P0)
      by (apply HdomΞ; rewrite <- Hdκa; exact Hγ).
    assert (Hγκ : γ `in` dom κ)
      by (rewrite Heqκ; rewrite dom_app; clear - Hγ; fsetdec).
    assert (Heqlk : ⇓ᵗ[ Θ ] (msubst_lookup κa γ)
                   = msubst_lookup (msubst_compose (aenv_msubst Θ) κ) γ).
    { rewrite (msubst_lookup_compose (aenv_msubst Θ) κ (or_introl Hγκ)).
      f_equal. rewrite Heqκ. symmetry. apply msubst_lookup_app_in; exact Hγ. }
    rewrite Heqlk.
    eapply AtomSetProperties.subset_trans;
      [ apply (msubst_pskl_ftv_lower
                 (msubst_compose (aenv_msubst Θ) κ) P0 HXP) | ].
    rewrite msubst_pskl_compose; [ exact HO3 | exact Hside ]. }
  assert (Hinc_sub : msubst_compose (aenv_msubst Θ) κ ∷ (Ξ ++ Θ0) ⊑ Θ').
  { assert (HincR : κa ++ κb ∷ (Ξ ++ (β ~ abind_var_typ Qv) ++ Θ0) ⊑ Θ)
      by (rewrite <- Heqκ; exact Hinc).
    rewrite Heqκ. rewrite msubst_compose_app.
    eapply a_inc_downarrow_prefix;
      [ exact HdeclsΞ | exact HincR | exact Huq | exact Hdκa | exact Hincb_n
      | exact Hwfth | exact HuqΘ | exact Hsub' | exact Hgr ]. }
  (* ---- 6. the JOIN, ⇓-normalized and strengthened ---- *)
  assert (Hmd : mono_ptyp (⇓ᵗ[ Θ ] τ'))
    by (apply mono_downarrow; [ exact Hwfth | exact Hwfτ' | exact Hmτ' ]).
  assert (Hwfd' : a_wf_ptyp Θ' (⇓ᵗ[ Θ ] τ')).
  { rewrite Hddτ'. rewrite Hddα.
    apply a_wf_ptyp_downarrow_mono;
      [ exact HwfΘ' | exact Hwfα' | exact Hmκα ]. }
  assert (Hjoin' : ad_pat_sub_gv n NM (mode_fn M) Ψ Θ'
                     (ptyp_to_uskl_syn (⇓ᵗ[ Θ ] τ')) (⇓ᵇ[ Θ ] Q)).
  { eapply ad_pat_sub_gv_mono_strengthen;
      [ eapply sub_gv_downarrow_mono;
          [ exact HD | exact Hwfth | reflexivity | exact Hmτ' | exact Hwfτ' ]
      | reflexivity | exact Hmd | exact HuqΘ | exact HwfΘ' | exact Hsub'
      | intros γ Hγ; clear - HO1 Hγ; fsetdec
      | intros γ Hγ; clear - HO2 Hγ; fsetdec ]. }
  (* ---- 7. the FILL, ⇓-normalized and strengthened ---- *)
  assert (Hrs' : ad_refine_syn_f empty Θ' empty
                   (pskl_to_bskl_inh
                      (msubst_pskl (msubst_compose (aenv_msubst Θ) κ) P0))
                   (⇓ᵇ[ Θ ] Q)).
  { rewrite (msubst_pskl_compose (aenv_msubst Θ) κ P0 Hside).
    pose proof (refine_syn_f_downarrow Hrs Hwfth
                  ltac:(intros x Hx; exfalso; clear - Hx; fsetdec)) as h.
    rewrite Heqinh in h.
    eapply ad_refine_syn_f_strengthen;
      [ exact h | exact HuqΘ | exact HwfΘ' | exact Hsub'
      | intros x Hx; exfalso; clear - Hx; fsetdec
      | intros γ Hγ; right; rewrite ftvar_in_bskl_inh in Hγ;
        clear - HO3 Hγ; fsetdec
      | intros γ Hγ; right; clear - HO2 Hγ; fsetdec ]. }
  (* ---- 8. the counterpart's wf at the truncation ---- *)
  assert (HwfQ' : Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl (⇓ᵇ[ Θ ] Q))).
  { rewrite bskl_to_pskl_msubst_bskl.
    eapply a_wf_pskl_strengthen;
      [ apply a_wf_pskl_downarrow;
          [ exact HwfQ | exact Hwfth
          | intros x Hx; exfalso; clear - Hx; fsetdec ]
      | exact HuqΘ | intros x Hx; exfalso; clear - Hx; fsetdec | exact Hsub'
      | intros γ Hγ; right;
        rewrite <- bskl_to_pskl_msubst_bskl in Hγ;
        rewrite ftvar_in_pskl_bskl_to_pskl in Hγ;
        clear - HO2 Hγ; fsetdec ]. }
  (* ---- 9. the slack, at the ⇓-composed metasubstitution ---- *)
  assert (Hακdom : α `in` dom κ).
  { rewrite Heqκ. rewrite dom_app.
    assert (Hαd : α `in` dom κb)
      by (eapply a_inc_flex_dom;
          [ exact Hincb | exact HwfΘ0 | exact Hfα0 ]).
    clear - Hαd. fsetdec. }
  assert (Hslack' : Θ' ⊢ (ptyp_to_uskl_syn (⇓ᵗ[ Θ ] τ'))
              ≡ᵘ (ptyp_to_uskl_syn
                    (msubst_lookup (msubst_compose (aenv_msubst Θ) κ) α))).
  { rewrite (msubst_lookup_compose (aenv_msubst Θ) κ (or_introl Hακdom)).
    rewrite <- Hddτ'.
    apply a_uskl_tyequiv__mono;
      [ exact Hmd | exact Hmd | exact Hwfd' | exact Hwfd'
      | apply a_tyequiv__refl; apply mono_ptyp_lc; exact Hmd ]. }
  (* ---- 10. the IH at the TRUNCATED problem ---- *)
  destruct (IH Ξ α P0 (ptyp_to_uskl_syn (⇓ᵗ[ Θ ] τ')) Ψ Θ'
              (msubst_compose (aenv_msubst Θ) κ) (⇓ᵇ[ Θ ] Q) ltac:(lia)
              HdeclsΞ HdomΞ Hwf' HwfΘ' HwfP0' Hfα0 HmodSK HmodTY
              Hinc_sub Hslack' Hjoin' Hrs' HwfQ')
    as [P1 [Θ1 [Hrun Hopt]]].
  (* ---- 11. the junk rename, and the re-attachment ---- *)
  destruct (a_sub_flex_sound_thm Hrun HdeclsΞ Hwf' HwfP0' Hαb' HmodSK HmodTY)
    as [[[w [Hidw Hincw]] Hdefs] HwfΘ1].
  assert (HscP1 : a_scope_pskl Θ1 P1)
    by (eapply a_sub_flex_out_scope;
        [ exact Hrun | exact HdeclsΞ | exact Hwf' | exact HwfP0'
        | exact Hαb' | exact HmodSK | exact HmodTY ]).
  assert (HβflexΘ1 : forall bd, binds β bd Θ1 ->
            bd = abind_flex_mono \/ exists τ, bd = abind_flex_mono_def τ)
    by (eapply a_sub_flex_out_flex_only;
        [ exact Hrun | exact HdeclsΞ | exact Hwf' | exact HwfP0'
        | exact Hαb' | exact HmodSK | exact HmodTY | exact HβΞΘ0 ]).
  assert (HβΞ : β `notin` ftvar_in_aenv Ξ).
  { pose proof (a_decls_no_ftvar HdeclsΞ) as h.
    clear - h HβΞΘ0. simpl_env in HβΞΘ0. fsetdec. }
  assert (HβΘ0 : β `notin` ftvar_in_aenv Θ0).
  { pose proof (a_wf_aenv_ftvar_dom HwfΘ0) as h.
    clear - h HβΞΘ0. simpl_env in HβΞΘ0. fsetdec. }
  destruct (atom_fresh (dom Θ1 `union` ftvar_in_aenv Θ1
                        `union` ftvar_in_pskl P1 `union` dom Ξ
                        `union` dom Θ0 `union` ftvar_in_aenv Θ0
                        `union` ftvar_in_aenv Ξ `union` ftvar_in_pskl P0
                        `union` singleton α `union` singleton β))
    as [β1 Fr].
  assert (Hβ1Qv : β1 `notin` ftvar_in_ptyp Qv)
    by (clear - HftvQv Fr; fsetdec).
  assert (Hrunsw : a_sub_flex NM M P0 Θ0 Ξ α
                     (swap_pskl β β1 P1) (swap_aenv β β1 Θ1)).
  { apply (a_sub_flex_swap_junk β β1 NM M P0 Θ0 Ξ α P1 Θ1 Hrun);
      [ intro Hc; subst; exact (Hne eq_refl)
      | clear - Fr; fsetdec
      | clear - HβΘ0 HβΞ Hnin; fsetdec
      | clear - Fr; fsetdec ]. }
  exists (swap_pskl β β1 P1),
         ((β ~ abind_var_typ Qv) ++ swap_aenv β β1 Θ1).
  split.
  { apply a_sub_flex__skip_tm_var;
      [ apply swap_junk_dom_out; clear - Fr; fsetdec
      | exact Hrunsw ]. }
  (* ---- 12. the package ---- *)
  intros κf Hidf Hincf.
  assert (Hincf' : κf ∷ (Ξ ++ Θ0) ⊑ swap_aenv β β1 Θ1)
    by (eapply a_inc_var_mid_strip_id;
        [ exact HdeclsΞ | exact Hidf | exact Hincf ]).
  assert (Heqw : w = κf)
    by (eapply is_id_inc_unique;
        [ exact Hincw | exact Hidw | exact Hincf' | exact Hidf ]).
  subst w.
  destruct (Hopt κf Hidf Hincw) as [ζ [Hζ [Hie Hprec]]].
  assert (Hkeysζ : forall γ, List.In γ (List.map fst ζ) -> γ `in` dom Θ1)
    by (intros γ hγ; eapply a_inc_keys_dom; [ exact Hζ | exact hγ ]).
  assert (Hkeysf : forall γ, List.In γ (List.map fst κf) ->
            γ `in` dom (Ξ ++ Θ0))
    by (intros γ hγ; eapply a_inc_keys_dom; [ exact Hincf' | exact hγ ]).
  assert (Hkey : forall γ, List.In γ (List.map fst κf) -> γ <> β /\ γ <> β1).
  { intros γ hγ. pose proof (Hkeysf γ hγ) as hd.
    split; [ intro Hc; subst; clear - hd HβΞΘ0; fsetdec
           | intro Hc; subst; clear - hd Fr; simpl_env in hd; fsetdec ]. }
  (* ⚙ THE SEMANTIC MIDDLE.  Both [a_inc__var] and
     [a_inc_equiv_mid_insert_var] want [Θ' ⊢ A' ≡ᵗ (·)Qv]; this is the
     consistency twin's [Hmiddle] (prop_consis_complete.v:5658). *)
  assert (Hmiddle : Θ' ⊢ A' ≡ᵗ
            msubst_ptyp (msubst_compose (aenv_msubst Θ) κb) Qv).
  { eapply a_tyequiv__trans; [ exact HeqA' | ].
    apply a_tyequiv__sym.
    eapply msubst_compose_downarrow_tyequiv
      with (Θpre := Ξv ++ (β ~ abind_var_typ A'));
      [ exact (eq_sym HeqW) | exact HuqΘ | exact Hwfth | exact HwfΘ'
      | eapply a_inc_msubst_lc; exact Hincb
      | intros α0 HXd;
        destruct (a_inc_dom_flex Hincb HXd) as [Hb | [τ0 Hb]];
        (eapply a_inc_lookup_wf; [ exact Hincb | exact HwfΘ0 | ]);
        [ right; left; exact Hb | right; right; exists τ0; exact Hb ]
      | exact HlcQv ]. }
  (* the Ξ-block is invisible to the payload ([ftv Qv ⊆ dom Θ0]) *)
  assert (Hag : msubst_ptyp (msubst_compose (aenv_msubst Θ) κ) Qv
              = msubst_ptyp (msubst_compose (aenv_msubst Θ) κb) Qv).
  { apply msubst_ptyp_agree. intros α0 HXQ.
    rewrite Heqκ. rewrite msubst_compose_app.
    apply msubst_lookup_app_notin.
    rewrite dom_msubst_compose. rewrite Hdκa.
    assert (Hα0Θ0 : α0 `in` dom Θ0) by (clear - HftvQv HXQ; fsetdec).
    clear - Huq Hα0Θ0. simpl_env in Huq. solve_uniq. }
  exists (kswap_msubst β β1 ζ).
  split.
  { (* the increase : [a_inc__var] over the swapped sub-output *)
    rewrite HeqΘ. apply a_inc__var; [ | | exact HsufΞv ].
    - apply (a_inc_kswap β β1 ζ Θ1 Θ' Hζ);
        [ clear - Fr; fsetdec | exact HwfΘ1 | clear - Fr; fsetdec
        | exact HβflexΘ1 ].
    - (* the SEMANTIC MIDDLE, read back through the junk swap *)
      assert (Hkw : msubst_ptyp (kswap_msubst β β1 ζ) Qv
                  = msubst_ptyp ζ Qv).
      { pose proof (msubst_ptyp_kswap β β1 ζ Qv
                      ltac:(clear - Fr; fsetdec)
                      ltac:(intro hc; pose proof (Hkeysζ β1 hc) as h;
                            clear - h Fr; fsetdec)
                      Hβ1Qv (or_introl HβQv)) as h.
        rewrite (swap_ptyp_fresh_id β β1 Qv HβQv Hβ1Qv) in h. exact h. }
      rewrite Hkw.
      assert (Hlc1 : msubst_lc (msubst_compose (aenv_msubst Θ) κ))
        by (eapply a_inc_msubst_lc; exact Hinc_sub).
      assert (Hlc2 : msubst_lc (msubst_compose ζ κf)).
      { apply msubst_lc_compose; [ eapply a_inc_msubst_lc; exact Hζ | ].
        intros a t Hin. eapply is_id_msubst_values_lc;
          [ exact Hidf | exact Hin ]. }
      pose proof (a_inc_equiv_msubst_ptyp HwfQv Hie Hwf' Hlc1 Hlc2) as Hmid.
      rewrite (msubst_compose_id_ptyp Hwf' HwfΘ1 Hidf Hincw Hζ HwfQv)
        in Hmid.
      rewrite Hag in Hmid.
      eapply a_tyequiv__trans; [ exact Hmiddle | exact Hmid ]. }
  split.
  { (* the equivalence *)
    rewrite (msubst_compose_kswap_id β β1 ζ κf Hidf Hkey).
    destruct (@a_inc_strip_decls_prefix Ξ Θ0 κf (swap_aenv β β1 Θ1)
                HdeclsΞ Hincf')
      as [κf1 [κf2 [Heqκf [Hdκf1 _]]]].
    assert (Hmi : a_inc_equiv (Ξ ++ (β ~ abind_var_typ Qv) ++ Θ0)
                    (msubst_compose (aenv_msubst Θ) κ)
                    (msubst_compose ζ κf)
                    (Ξv ++ (β ~ abind_var_typ A') ++ Θ')).
    { rewrite Heqκ. rewrite (msubst_compose_app (aenv_msubst Θ) κa κb).
      rewrite Heqκf. rewrite (msubst_compose_app ζ κf1 κf2).
      apply a_inc_equiv_mid_insert_var;
        [ exact HdeclsΞ | exact Huq'
        | rewrite dom_msubst_compose; exact Hdκa
        | rewrite dom_msubst_compose; exact Hdκf1
        | exact Hmiddle | exact HsufΞv | ].
      rewrite Heqκ in Hie.
      rewrite (msubst_compose_app (aenv_msubst Θ) κa κb) in Hie.
      rewrite Heqκf in Hie.
      rewrite (msubst_compose_app ζ κf1 κf2) in Hie.
      exact Hie. }
    rewrite <- HeqΘ in Hmi.
    eapply a_inc_equiv_trans; [ | exact Hwfth | exact Hmi ].
    pose proof (a_inc_equiv_self_downarrow Hinc (@nil (atom * abind)))
      as Hself.
    simpl in Hself. apply Hself; [ exact Hwfth | exact HuqΘ | exact Hwf ]. }
  { (* the precision — verbatim from §(M): the swap erases, then the package
       comes back from [(Θ', ⇓ᵇQ)] to [(Θ, Q)] *)
    rewrite (msubst_bskl_kswap_paint β β1 ζ P1);
      [ | clear - Fr; fsetdec
        | intro hc; pose proof (Hkeysζ β1 hc) as h; clear - h Fr; fsetdec
        | clear - Fr; fsetdec
        | destruct (AtomSetProperties.In_dec β (ftvar_in_pskl P1))
            as [hin | hout]; [ right | left; exact hout ];
          assert (hbt : a_binds_tvar β Θ1)
            by (eapply a_scope_pskl_ftv_binds; [ exact HscP1 | exact hin ]);
          destruct hbt as [hbt | [hbt | [τ0 hbt]]];
          [ exfalso; destruct (HβflexΘ1 abind_tvar hbt) as [hc | [τ1 hc]];
              discriminate
          | eapply a_inc_flex_in_keys; [ exact Hζ | left; exact hbt ]
          | eapply a_inc_flex_in_keys; [ exact Hζ | right; eexists; exact hbt ] ] ].
    assert (HprecΘ : Θ ⨟ empty ⊢ₚᵣᵃ (msubst_bskl ζ (pskl_to_bskl_syn P1))
                       ⊑ (bskl_to_pskl (⇓ᵇ[ Θ ] Q))).
    { unfold ad_precise in *.
      apply ad_refine_syn_f_forget with (F := empty).
      eapply ad_refine_syn_f_weaken_ctx;
        [ apply ad_refine_syn_f_empty_intro; exact Hprec | exact Hsub' ]. }
    unfold ad_precise in *.
    rewrite (bskl_to_pskl_msubst_bskl (aenv_msubst Θ) Q) in HprecΘ.
    eapply ad_refine_syn_trans;
      [ apply ad_precise_downarrow;
          [ exact HwfQ | exact Hwfth
          | intros x Hx; exfalso; clear - Hx; fsetdec ]
      | exact Hwfth
      | intros x Hx; exfalso; clear - Hx; fsetdec
      | rewrite bskl_to_pskl_pskl_to_bskl_inh; exact HwfQ
      | exact HprecΘ ]. }
Qed.

Print Assumptions a_sub_flex_complete_skip_tm_var.

(* ===================================================================== *)
(*  §(O) Flex-SkipTmVar (skl) — the TERM-VARIABLE head, skeleton binding  *)
(*                                                                        *)
(*  §(N) with the ≡ˢ semantic middle throughout, exactly as the twin       *)
(*  walk's [Assign-SkipTmSkl] mirrors its [Assign-SkipTmVar]               *)
(*  (prop_consis_complete.v:5692-6023).  The mech splits the paper's       *)
(*  single [x : P] entry into a type binding and a skeleton binding, so    *)
(*  the paper's one rule owes two completeness rows.                       *)
(* ===================================================================== *)

Lemma a_sub_flex_complete_skip_tm_skl :
  forall n NM M Θ0 Ξ α β Qv P0 R' Ψ Θ κ Q,
  (* length-guarded, as in [a_sub_flex_complete_skip_rigid] *)
  (forall Ξ' α' P0' R'' Ψ' Θ'' κ' Q',
     length Ξ' <= S (length Ξ) ->
     sub_flex_complete_concl n NM M Θ0 Ξ' α' P0' R'' Ψ' Θ'' κ' Q') ->
  sub_flex_complete_concl n NM M ((β ~ abind_var_skl Qv) ++ Θ0) Ξ α P0
    R' Ψ Θ κ Q.
Proof.
  intros n NM M Θ0 Ξ α β Qv P0 R' Ψ Θ κ Q IH.
  unfold sub_flex_complete_concl in *.
  intros HdeclsΞ HdomΞ Hwf Hwfth HwfP0 Hfα HmodSK HmodTY Hinc Hslack HD Hrs
         HwfQ.
  (* ---- 0. the stripped context, and the two DERIVED premises ---- *)
  assert (Huq : uniq (Ξ ++ (β ~ abind_var_skl Qv) ++ Θ0))
    by (apply a_wf_aenv_uniq; exact Hwf).
  assert (HβΞΘ0 : β `notin` dom (Ξ ++ Θ0)).
  { clear - Huq. simpl_env in Huq. destruct_uniq.
    unfold disjoint in *. simpl_env in *. fsetdec. }
  (* the subject survives the head strip: a term entry is not flexible *)
  assert (Hfα0 : a_flex_tvar Θ0 α).
  { destruct Hfα as [Hb | [τ0 Hb]];
      [ destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He1 He2] | Hb'];
        [ discriminate | left; exact Hb' ]
      | destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He1 He2] | Hb'];
        [ discriminate | right; exists τ0; exact Hb' ] ]. }
  assert (HαΘ0 : α `in` dom Θ0)
    by (destruct Hfα0 as [Hb | [? Hb]]; apply binds_In in Hb; exact Hb).
  assert (Hne : α <> β).
  { intro Hc; subst. clear - HαΘ0 HβΞΘ0. simpl_env in HβΞΘ0. fsetdec. }
  (* and no free variable of the well-formed [P0] is a term variable *)
  assert (Hnin : β `notin` ftvar_in_pskl P0).
  { intro Hx. destruct (a_wf_pskl_ftv_tvarish HwfP0 Hx) as [Hemp | Hbt];
      [ clear - Hemp; fsetdec | ].
    assert (Hbx : binds β (abind_var_skl Qv)
                    (Ξ ++ (β ~ abind_var_skl Qv) ++ Θ0))
      by (apply binds_app_3; left; reflexivity).
    destruct Hbt as [Hb | [Hb | [τ0 Hb]]];
      (pose proof (binds_unique _ _ _ _ _ Hb Hbx Huq) as Heqb;
       discriminate Heqb). }
  assert (Hwf' : a_wf_aenv (Ξ ++ Θ0))
    by (eapply a_wf_aenv_strip_mid; [ exact HdeclsΞ | exact Hwf ]).
  assert (Huq' : uniq (Ξ ++ Θ0)) by (apply a_wf_aenv_uniq; exact Hwf').
  assert (HwfΘ0 : a_wf_aenv Θ0) by (eapply a_wf_aenv_app_r; exact Hwf').
  assert (HwfP0' : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P0)
    by (eapply a_wf_pskl_strip_mid; [ exact HwfP0 | exact Hnin ]).
  (* the payload is scoped BELOW the entry *)
  assert (HwfaΘ0x : a_wf_aenv ((β ~ abind_var_skl Qv) ++ Θ0))
    by (eapply a_wf_aenv_app_r; exact Hwf).
  destruct (a_wf_aenv_var_skl_inv HwfaΘ0x) as [_ [HwfQv0 _]].
  assert (HwfQv : a_scope_pskl (Ξ ++ Θ0) Qv)
    by (eapply a_scope_pskl_weaken;
        [ intros ? ? Hb; apply binds_app_3; exact Hb | exact HwfQv0 ]).
  assert (HlcQv : lc_pskl Qv) by (eapply a_scope_pskl_lc; exact HwfQv0).
  assert (HftvQv : ftvar_in_pskl Qv [<=] dom Θ0)
    by (apply a_scope_pskl_ftv_dom'; exact HwfQv0).
  assert (HβQv : β `notin` ftvar_in_pskl Qv).
  { clear - HftvQv HβΞΘ0. simpl_env in HβΞΘ0. fsetdec. }
  assert (Hαb0 : a_binds_tvar α Θ0)
    by (destruct Hfα0 as [h | [τ0 h]];
        [ right; left; exact h | right; right; exists τ0; exact h ]).
  assert (Hαb' : a_binds_tvar α (Ξ ++ Θ0))
    by (destruct (a_flex_tvar_app_weaken Ξ Hfα0) as [h | [τ0 h]];
        [ right; left; exact h | right; right; exists τ0; exact h ]).
  assert (Hαbfull : a_binds_tvar α (Ξ ++ (β ~ abind_var_skl Qv) ++ Θ0)).
  { destruct (a_flex_tvar_app_weaken (Ξ ++ (β ~ abind_var_skl Qv)) Hfα0)
      as [h | [τ0 h]];
      [ right; left | right; right; exists τ0 ]; simpl_env in h; exact h. }
  assert (HuqΘ : uniq Θ) by (apply a_wf_aenv_uniq; exact Hwfth).
  (* ---- 1. peel Ξ off κ, then invert the TERM middle ---- *)
  destruct (@a_inc_strip_decls_prefix Ξ ((β ~ abind_var_skl Qv) ++ Θ0) κ Θ
              HdeclsΞ Hinc)
    as [κa [κb [Heqκ [Hdκa Hincxb]]]].
  destruct (a_inc_var_skl_inv Hincxb)
    as [Ξv [Qv' [Θ' [HeqΘ [HeqQv' [HsufΞv Hincb]]]]]].
  assert (HwfΘ' : a_wf_aenv Θ').
  { rewrite HeqΘ in Hwfth.
    eapply a_wf_aenv_app_r with (Θp := Ξv ++ (β ~ abind_var_skl Qv')).
    simpl_env. simpl_env in Hwfth. exact Hwfth. }
  assert (HeqW : (Ξv ++ (β ~ abind_var_skl Qv')) ++ Θ' = Θ)
    by (rewrite HeqΘ; simpl_env; reflexivity).
  assert (Hsub' : forall y c, binds y c Θ' -> binds y c Θ).
  { intros y c Hb. rewrite HeqΘ. apply binds_app_3. apply binds_app_3.
    exact Hb. }
  assert (Hincb_n : msubst_compose (aenv_msubst Θ) κb ∷ Θ0 ⊑ Θ').
  { pose proof (a_inc_self_downarrow Hincb (Ξv ++ (β ~ abind_var_skl Qv')))
      as Hs.
    rewrite HeqW in Hs.
    apply Hs; [ exact Hwfth | exact HuqΘ | exact HwfΘ0 ]. }
  (* ---- 2. the subject is a MONO painting, and ⇓ pins it to [κα̂] ---- *)
  assert (Hmκα : mono_ptyp (msubst_lookup κ α))
    by (eapply a_inc_lookup_mono; exact Hinc).
  assert (Hwfκα : a_wf_ptyp Θ (msubst_lookup κ α))
    by (eapply a_inc_lookup_wf; [ exact Hinc | exact Hwf | exact Hαbfull ]).
  destruct (a_uskl_tyequiv_mono_r_inv Hslack
              (eq_refl (ptyp_to_uskl_syn (msubst_lookup κ α))) Hmκα Hwfκα)
    as [τ' [HeqR' [Hmτ' [Hwfτ' Heqττ']]]].
  subst R'.
  assert (Hddτ' : ⇓ᵗ[ Θ ] τ' = ⇓ᵗ[ Θ ] (msubst_lookup κ α))
    by (apply a_tyequiv_downarrow; [ exact Hwfth | exact Heqττ' ]).
  (* ---- 3. the subject's image is scoped in the TRUNCATION ---- *)
  assert (Hακa : α `notin` dom κa).
  { rewrite Hdκa. clear - Huq HαΘ0. simpl_env in Huq. solve_uniq. }
  assert (Hwfα' : a_wf_ptyp Θ' (msubst_lookup κ α)).
  { rewrite Heqκ. rewrite (msubst_lookup_app_notin κa κb Hακa).
    eapply a_inc_lookup_wf; [ exact Hincb | exact HwfΘ0 | exact Hαb0 ]. }
  assert (Hftvα : ftvar_in_ptyp (msubst_lookup κ α) [<=] dom Θ')
    by (apply a_wf_ptyp_ftv_dom; exact Hwfα').
  assert (Hddα : ⇓ᵗ[ Θ ] (msubst_lookup κ α) = ⇓ᵗ[ Θ' ] (msubst_lookup κ α)).
  { rewrite <- HeqW.
    apply downarrow_app_agree_ptyp; [ rewrite HeqW; exact HuqΘ | exact Hftvα ]. }
  assert (HO1 : ftvar_in_ptyp (⇓ᵗ[ Θ ] τ') [<=] dom Θ').
  { rewrite Hddτ'. rewrite Hddα. apply a_wf_ptyp_ftv_dom.
    apply a_wf_ptyp_downarrow_mono;
      [ exact HwfΘ' | exact Hwfα' | exact Hmκα ]. }
  (* ---- 4. the JOIN's ⇓-confinement, and the FILL's source below it ---- *)
  assert (Hmono_img : forall γ, mono_ptyp (msubst_lookup (aenv_msubst Θ) γ))
    by (intros; apply aenv_msubst_image_mono; exact Hwfth).
  assert (HO2 : ftvar_in_bskl (⇓ᵇ[ Θ ] Q) [<=] dom Θ').
  { eapply sub_gv_bskl_downarrow_mono_scoped;
      [ exact HD | exact Hwfth | reflexivity | exact Hmτ' | exact HO1 ]. }
  assert (Heqinh : ⇓ᵇ[ Θ ] (pskl_to_bskl_inh (msubst_pskl κ P0))
                   = pskl_to_bskl_inh (⇓ˢ[ Θ ] (msubst_pskl κ P0)))
    by (apply msubst_bskl_pskl_to_bskl_inh; exact Hmono_img).
  assert (HO3 : ftvar_in_pskl (⇓ˢ[ Θ ] (msubst_pskl κ P0)) [<=] dom Θ').
  { pose proof (refine_syn_f_downarrow_source_ftv Hrs Hwfth
                  ltac:(intros x Hx; exfalso; clear - Hx; fsetdec)) as h.
    rewrite Heqinh in h. rewrite ftvar_in_bskl_inh in h.
    clear - h HO2. fsetdec. }
  (* ---- 5. the ⇓-composed increase at the TRUNCATION ---- *)
  assert (Hside : forall γ, γ `in` ftvar_in_pskl P0 ->
            γ `in` dom κ \/ γ `notin` dom (aenv_msubst Θ)).
  { intros γ Hγ.
    destruct (AtomSetProperties.In_dec γ (dom κ)) as [Hin | Hni];
      [ left; exact Hin | right ].
    intro Hin2. apply aenv_msubst_dom_inv in Hin2.
    destruct (a_wf_pskl_ftv_tvarish HwfP0 Hγ) as [Hemp | Hbt];
      [ clear - Hemp; fsetdec | ].
    destruct Hbt as [Htv | [Hfm | [τ0 Hfd]]].
    - assert (HtvΘ : binds γ abind_tvar Θ)
        by (eapply a_inc_binds_tvar; [ exact Hinc | exact Htv ]).
      destruct Hin2 as [Hb | [τ1 Hb]];
        (pose proof (binds_unique _ _ _ _ _ HtvΘ Hb HuqΘ) as Heqb;
         discriminate Heqb).
    - assert (Hyd : γ `in` dom κ)
        by (eapply a_inc_flex_dom; [ exact Hinc | exact Hwf | left; exact Hfm ]).
      contradiction.
    - assert (Hyd : γ `in` dom κ)
        by (eapply a_inc_flex_dom;
            [ exact Hinc | exact Hwf | right; exists τ0; exact Hfd ]).
      contradiction. }
  assert (Hgr : forall γ, γ `in` dom κa ->
            ftvar_in_ptyp (⇓ᵗ[ Θ ] (msubst_lookup κa γ)) [<=] dom Θ').
  { intros γ Hγ.
    assert (HXP : γ `in` ftvar_in_pskl P0)
      by (apply HdomΞ; rewrite <- Hdκa; exact Hγ).
    assert (Hγκ : γ `in` dom κ)
      by (rewrite Heqκ; rewrite dom_app; clear - Hγ; fsetdec).
    assert (Heqlk : ⇓ᵗ[ Θ ] (msubst_lookup κa γ)
                   = msubst_lookup (msubst_compose (aenv_msubst Θ) κ) γ).
    { rewrite (msubst_lookup_compose (aenv_msubst Θ) κ (or_introl Hγκ)).
      f_equal. rewrite Heqκ. symmetry. apply msubst_lookup_app_in; exact Hγ. }
    rewrite Heqlk.
    eapply AtomSetProperties.subset_trans;
      [ apply (msubst_pskl_ftv_lower
                 (msubst_compose (aenv_msubst Θ) κ) P0 HXP) | ].
    rewrite msubst_pskl_compose; [ exact HO3 | exact Hside ]. }
  assert (Hinc_sub : msubst_compose (aenv_msubst Θ) κ ∷ (Ξ ++ Θ0) ⊑ Θ').
  { assert (HincR : κa ++ κb ∷ (Ξ ++ (β ~ abind_var_skl Qv) ++ Θ0) ⊑ Θ)
      by (rewrite <- Heqκ; exact Hinc).
    rewrite Heqκ. rewrite msubst_compose_app.
    eapply a_inc_downarrow_prefix;
      [ exact HdeclsΞ | exact HincR | exact Huq | exact Hdκa | exact Hincb_n
      | exact Hwfth | exact HuqΘ | exact Hsub' | exact Hgr ]. }
  (* ---- 6. the JOIN, ⇓-normalized and strengthened ---- *)
  assert (Hmd : mono_ptyp (⇓ᵗ[ Θ ] τ'))
    by (apply mono_downarrow; [ exact Hwfth | exact Hwfτ' | exact Hmτ' ]).
  assert (Hwfd' : a_wf_ptyp Θ' (⇓ᵗ[ Θ ] τ')).
  { rewrite Hddτ'. rewrite Hddα.
    apply a_wf_ptyp_downarrow_mono;
      [ exact HwfΘ' | exact Hwfα' | exact Hmκα ]. }
  assert (Hjoin' : ad_pat_sub_gv n NM (mode_fn M) Ψ Θ'
                     (ptyp_to_uskl_syn (⇓ᵗ[ Θ ] τ')) (⇓ᵇ[ Θ ] Q)).
  { eapply ad_pat_sub_gv_mono_strengthen;
      [ eapply sub_gv_downarrow_mono;
          [ exact HD | exact Hwfth | reflexivity | exact Hmτ' | exact Hwfτ' ]
      | reflexivity | exact Hmd | exact HuqΘ | exact HwfΘ' | exact Hsub'
      | intros γ Hγ; clear - HO1 Hγ; fsetdec
      | intros γ Hγ; clear - HO2 Hγ; fsetdec ]. }
  (* ---- 7. the FILL, ⇓-normalized and strengthened ---- *)
  assert (Hrs' : ad_refine_syn_f empty Θ' empty
                   (pskl_to_bskl_inh
                      (msubst_pskl (msubst_compose (aenv_msubst Θ) κ) P0))
                   (⇓ᵇ[ Θ ] Q)).
  { rewrite (msubst_pskl_compose (aenv_msubst Θ) κ P0 Hside).
    pose proof (refine_syn_f_downarrow Hrs Hwfth
                  ltac:(intros x Hx; exfalso; clear - Hx; fsetdec)) as h.
    rewrite Heqinh in h.
    eapply ad_refine_syn_f_strengthen;
      [ exact h | exact HuqΘ | exact HwfΘ' | exact Hsub'
      | intros x Hx; exfalso; clear - Hx; fsetdec
      | intros γ Hγ; right; rewrite ftvar_in_bskl_inh in Hγ;
        clear - HO3 Hγ; fsetdec
      | intros γ Hγ; right; clear - HO2 Hγ; fsetdec ]. }
  (* ---- 8. the counterpart's wf at the truncation ---- *)
  assert (HwfQ' : Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl (⇓ᵇ[ Θ ] Q))).
  { rewrite bskl_to_pskl_msubst_bskl.
    eapply a_wf_pskl_strengthen;
      [ apply a_wf_pskl_downarrow;
          [ exact HwfQ | exact Hwfth
          | intros x Hx; exfalso; clear - Hx; fsetdec ]
      | exact HuqΘ | intros x Hx; exfalso; clear - Hx; fsetdec | exact Hsub'
      | intros γ Hγ; right;
        rewrite <- bskl_to_pskl_msubst_bskl in Hγ;
        rewrite ftvar_in_pskl_bskl_to_pskl in Hγ;
        clear - HO2 Hγ; fsetdec ]. }
  (* ---- 9. the slack, at the ⇓-composed metasubstitution ---- *)
  assert (Hακdom : α `in` dom κ).
  { rewrite Heqκ. rewrite dom_app.
    assert (Hαd : α `in` dom κb)
      by (eapply a_inc_flex_dom;
          [ exact Hincb | exact HwfΘ0 | exact Hfα0 ]).
    clear - Hαd. fsetdec. }
  assert (Hslack' : Θ' ⊢ (ptyp_to_uskl_syn (⇓ᵗ[ Θ ] τ'))
              ≡ᵘ (ptyp_to_uskl_syn
                    (msubst_lookup (msubst_compose (aenv_msubst Θ) κ) α))).
  { rewrite (msubst_lookup_compose (aenv_msubst Θ) κ (or_introl Hακdom)).
    rewrite <- Hddτ'.
    apply a_uskl_tyequiv__mono;
      [ exact Hmd | exact Hmd | exact Hwfd' | exact Hwfd'
      | apply a_tyequiv__refl; apply mono_ptyp_lc; exact Hmd ]. }
  (* ---- 10. the IH at the TRUNCATED problem ---- *)
  destruct (IH Ξ α P0 (ptyp_to_uskl_syn (⇓ᵗ[ Θ ] τ')) Ψ Θ'
              (msubst_compose (aenv_msubst Θ) κ) (⇓ᵇ[ Θ ] Q) ltac:(lia)
              HdeclsΞ HdomΞ Hwf' HwfΘ' HwfP0' Hfα0 HmodSK HmodTY
              Hinc_sub Hslack' Hjoin' Hrs' HwfQ')
    as [P1 [Θ1 [Hrun Hopt]]].
  (* ---- 11. the junk rename, and the re-attachment ---- *)
  destruct (a_sub_flex_sound_thm Hrun HdeclsΞ Hwf' HwfP0' Hαb' HmodSK HmodTY)
    as [[[w [Hidw Hincw]] Hdefs] HwfΘ1].
  assert (HscP1 : a_scope_pskl Θ1 P1)
    by (eapply a_sub_flex_out_scope;
        [ exact Hrun | exact HdeclsΞ | exact Hwf' | exact HwfP0'
        | exact Hαb' | exact HmodSK | exact HmodTY ]).
  assert (HβflexΘ1 : forall bd, binds β bd Θ1 ->
            bd = abind_flex_mono \/ exists τ, bd = abind_flex_mono_def τ)
    by (eapply a_sub_flex_out_flex_only;
        [ exact Hrun | exact HdeclsΞ | exact Hwf' | exact HwfP0'
        | exact Hαb' | exact HmodSK | exact HmodTY | exact HβΞΘ0 ]).
  assert (HβΞ : β `notin` ftvar_in_aenv Ξ).
  { pose proof (a_decls_no_ftvar HdeclsΞ) as h.
    clear - h HβΞΘ0. simpl_env in HβΞΘ0. fsetdec. }
  assert (HβΘ0 : β `notin` ftvar_in_aenv Θ0).
  { pose proof (a_wf_aenv_ftvar_dom HwfΘ0) as h.
    clear - h HβΞΘ0. simpl_env in HβΞΘ0. fsetdec. }
  destruct (atom_fresh (dom Θ1 `union` ftvar_in_aenv Θ1
                        `union` ftvar_in_pskl P1 `union` dom Ξ
                        `union` dom Θ0 `union` ftvar_in_aenv Θ0
                        `union` ftvar_in_aenv Ξ `union` ftvar_in_pskl P0
                        `union` singleton α `union` singleton β))
    as [β1 Fr].
  assert (Hβ1Qv : β1 `notin` ftvar_in_pskl Qv)
    by (clear - HftvQv Fr; fsetdec).
  assert (Hrunsw : a_sub_flex NM M P0 Θ0 Ξ α
                     (swap_pskl β β1 P1) (swap_aenv β β1 Θ1)).
  { apply (a_sub_flex_swap_junk β β1 NM M P0 Θ0 Ξ α P1 Θ1 Hrun);
      [ intro Hc; subst; exact (Hne eq_refl)
      | clear - Fr; fsetdec
      | clear - HβΘ0 HβΞ Hnin; fsetdec
      | clear - Fr; fsetdec ]. }
  exists (swap_pskl β β1 P1),
         ((β ~ abind_var_skl Qv) ++ swap_aenv β β1 Θ1).
  split.
  { apply a_sub_flex__skip_tm_skl;
      [ apply swap_junk_dom_out; clear - Fr; fsetdec
      | exact Hrunsw ]. }
  (* ---- 12. the package ---- *)
  intros κf Hidf Hincf.
  assert (Hincf' : κf ∷ (Ξ ++ Θ0) ⊑ swap_aenv β β1 Θ1)
    by (eapply a_inc_var_skl_mid_strip_id;
        [ exact HdeclsΞ | exact Hidf | exact Hincf ]).
  assert (Heqw : w = κf)
    by (eapply is_id_inc_unique;
        [ exact Hincw | exact Hidw | exact Hincf' | exact Hidf ]).
  subst w.
  destruct (Hopt κf Hidf Hincw) as [ζ [Hζ [Hie Hprec]]].
  assert (Hkeysζ : forall γ, List.In γ (List.map fst ζ) -> γ `in` dom Θ1)
    by (intros γ hγ; eapply a_inc_keys_dom; [ exact Hζ | exact hγ ]).
  assert (Hkeysf : forall γ, List.In γ (List.map fst κf) ->
            γ `in` dom (Ξ ++ Θ0))
    by (intros γ hγ; eapply a_inc_keys_dom; [ exact Hincf' | exact hγ ]).
  assert (Hkey : forall γ, List.In γ (List.map fst κf) -> γ <> β /\ γ <> β1).
  { intros γ hγ. pose proof (Hkeysf γ hγ) as hd.
    split; [ intro Hc; subst; clear - hd HβΞΘ0; fsetdec
           | intro Hc; subst; clear - hd Fr; simpl_env in hd; fsetdec ]. }
  (* ⚙ THE SEMANTIC MIDDLE.  Both [a_inc__var_skl] and
     [a_inc_equiv_mid_insert_var_skl] want [Θ' ⊢ Qv' ≡ˢ (·)Qv]; this is the
     consistency twin's [Hmiddle] (prop_consis_complete.v:5990). *)
  assert (Hmiddle : Θ' ⊢ Qv' ≡ˢ
            msubst_pskl (msubst_compose (aenv_msubst Θ) κb) Qv).
  { eapply a_pskl_tyequiv__trans; [ exact HeqQv' | ].
    apply a_pskl_tyequiv__sym.
    eapply msubst_pskl_compose_downarrow_tyequiv
      with (Θpre := Ξv ++ (β ~ abind_var_skl Qv'));
      [ exact (eq_sym HeqW) | exact HuqΘ | exact Hwfth | exact HwfΘ'
      | eapply a_inc_msubst_lc; exact Hincb
      | intros α0 HXd;
        destruct (a_inc_dom_flex Hincb HXd) as [Hb | [τ0 Hb]];
        (eapply a_inc_lookup_wf; [ exact Hincb | exact HwfΘ0 | ]);
        [ right; left; exact Hb | right; right; exists τ0; exact Hb ]
      | exact HlcQv ]. }
  (* the Ξ-block is invisible to the payload ([ftv Qv ⊆ dom Θ0]) *)
  assert (Hag : msubst_pskl (msubst_compose (aenv_msubst Θ) κ) Qv
              = msubst_pskl (msubst_compose (aenv_msubst Θ) κb) Qv).
  { apply msubst_pskl_agree. intros α0 HXQ.
    rewrite Heqκ. rewrite msubst_compose_app.
    apply msubst_lookup_app_notin.
    rewrite dom_msubst_compose. rewrite Hdκa.
    assert (Hα0Θ0 : α0 `in` dom Θ0) by (clear - HftvQv HXQ; fsetdec).
    clear - Huq Hα0Θ0. simpl_env in Huq. solve_uniq. }
  exists (kswap_msubst β β1 ζ).
  split.
  { (* the increase : [a_inc__var_skl] over the swapped sub-output *)
    rewrite HeqΘ. apply a_inc__var_skl; [ | | exact HsufΞv ].
    - apply (a_inc_kswap β β1 ζ Θ1 Θ' Hζ);
        [ clear - Fr; fsetdec | exact HwfΘ1 | clear - Fr; fsetdec
        | exact HβflexΘ1 ].
    - (* the SEMANTIC MIDDLE, read back through the junk swap *)
      assert (Hkw : msubst_pskl (kswap_msubst β β1 ζ) Qv
                  = msubst_pskl ζ Qv).
      { pose proof (msubst_pskl_kswap β β1 ζ Qv
                      ltac:(clear - Fr; fsetdec)
                      ltac:(intro hc; pose proof (Hkeysζ β1 hc) as h;
                            clear - h Fr; fsetdec)
                      Hβ1Qv (or_introl HβQv)) as h.
        rewrite (swap_pskl_fresh_id β β1 Qv HβQv Hβ1Qv) in h. exact h. }
      rewrite Hkw.
      assert (Hlc1 : msubst_lc (msubst_compose (aenv_msubst Θ) κ))
        by (eapply a_inc_msubst_lc; exact Hinc_sub).
      assert (Hlc2 : msubst_lc (msubst_compose ζ κf)).
      { apply msubst_lc_compose; [ eapply a_inc_msubst_lc; exact Hζ | ].
        intros a t Hin. eapply is_id_msubst_values_lc;
          [ exact Hidf | exact Hin ]. }
      pose proof (a_inc_equiv_msubst_pskl HwfQv Hie Hwf' Hlc1 Hlc2) as Hmid.
      rewrite (msubst_compose_id_pskl Hwf' HwfΘ1 Hidf Hincw Hζ HwfQv)
        in Hmid.
      rewrite Hag in Hmid.
      eapply a_pskl_tyequiv__trans; [ exact Hmiddle | exact Hmid ]. }
  split.
  { (* the equivalence *)
    rewrite (msubst_compose_kswap_id β β1 ζ κf Hidf Hkey).
    destruct (@a_inc_strip_decls_prefix Ξ Θ0 κf (swap_aenv β β1 Θ1)
                HdeclsΞ Hincf')
      as [κf1 [κf2 [Heqκf [Hdκf1 _]]]].
    assert (Hmi : a_inc_equiv (Ξ ++ (β ~ abind_var_skl Qv) ++ Θ0)
                    (msubst_compose (aenv_msubst Θ) κ)
                    (msubst_compose ζ κf)
                    (Ξv ++ (β ~ abind_var_skl Qv') ++ Θ')).
    { rewrite Heqκ. rewrite (msubst_compose_app (aenv_msubst Θ) κa κb).
      rewrite Heqκf. rewrite (msubst_compose_app ζ κf1 κf2).
      apply a_inc_equiv_mid_insert_var_skl;
        [ exact HdeclsΞ | exact Huq'
        | rewrite dom_msubst_compose; exact Hdκa
        | rewrite dom_msubst_compose; exact Hdκf1
        | exact Hmiddle | exact HsufΞv | ].
      rewrite Heqκ in Hie.
      rewrite (msubst_compose_app (aenv_msubst Θ) κa κb) in Hie.
      rewrite Heqκf in Hie.
      rewrite (msubst_compose_app ζ κf1 κf2) in Hie.
      exact Hie. }
    rewrite <- HeqΘ in Hmi.
    eapply a_inc_equiv_trans; [ | exact Hwfth | exact Hmi ].
    pose proof (a_inc_equiv_self_downarrow Hinc (@nil (atom * abind)))
      as Hself.
    simpl in Hself. apply Hself; [ exact Hwfth | exact HuqΘ | exact Hwf ]. }
  { (* the precision — verbatim from §(M): the swap erases, then the package
       comes back from [(Θ', ⇓ᵇQ)] to [(Θ, Q)] *)
    rewrite (msubst_bskl_kswap_paint β β1 ζ P1);
      [ | clear - Fr; fsetdec
        | intro hc; pose proof (Hkeysζ β1 hc) as h; clear - h Fr; fsetdec
        | clear - Fr; fsetdec
        | destruct (AtomSetProperties.In_dec β (ftvar_in_pskl P1))
            as [hin | hout]; [ right | left; exact hout ];
          assert (hbt : a_binds_tvar β Θ1)
            by (eapply a_scope_pskl_ftv_binds; [ exact HscP1 | exact hin ]);
          destruct hbt as [hbt | [hbt | [τ0 hbt]]];
          [ exfalso; destruct (HβflexΘ1 abind_tvar hbt) as [hc | [τ1 hc]];
              discriminate
          | eapply a_inc_flex_in_keys; [ exact Hζ | left; exact hbt ]
          | eapply a_inc_flex_in_keys; [ exact Hζ | right; eexists; exact hbt ] ] ].
    assert (HprecΘ : Θ ⨟ empty ⊢ₚᵣᵃ (msubst_bskl ζ (pskl_to_bskl_syn P1))
                       ⊑ (bskl_to_pskl (⇓ᵇ[ Θ ] Q))).
    { unfold ad_precise in *.
      apply ad_refine_syn_f_forget with (F := empty).
      eapply ad_refine_syn_f_weaken_ctx;
        [ apply ad_refine_syn_f_empty_intro; exact Hprec | exact Hsub' ]. }
    unfold ad_precise in *.
    rewrite (bskl_to_pskl_msubst_bskl (aenv_msubst Θ) Q) in HprecΘ.
    eapply ad_refine_syn_trans;
      [ apply ad_precise_downarrow;
          [ exact HwfQ | exact Hwfth
          | intros x Hx; exfalso; clear - Hx; fsetdec ]
      | exact Hwfth
      | intros x Hx; exfalso; clear - Hx; fsetdec
      | rewrite bskl_to_pskl_pskl_to_bskl_inh; exact HwfQ
      | exact HprecΘ ]. }
Qed.


Print Assumptions a_sub_flex_complete_skip_tm_skl.

(* ===================================================================== *)
(*  P7a IS COMPLETE — all SEVEN rows are [Qed]                            *)
(*                                                                        *)
(*  §(F) Flex-Depend, §(G) Flex-Skip, §(I) Flex-Assign, §(K) Flex-Solve,   *)
(*  §(M) Flex-SkipRigid and — since the printed rule box was repaired —    *)
(*  §(N) Flex-SkipTmVar with its skeleton twin §(O).  §(I) and §(K) are    *)
(*  the CROSS-HALF rows: they leave the flexible walk (both re-enter the   *)
(*  MAIN judgment), so their IH is the P7b motive [sub_complete_concl],    *)
(*  not this one.                                                         *)
(*                                                                        *)
(*  The DISPATCHER lives in prop_sub_complete_dispatch.v (DESIGN §12.1's   *)
(*  three layers, all [Qed]).  ⚙ Its flexible half owes ONE obligation     *)
(*  none of the rows above carries, because no rule has it as a premise:   *)
(*  the STUCK-CHECK.  With a RIGID head β and [β ∈ ftvar_in_pskl P0] there *)
(*  is no [a_sub_flex] rule at all ([__depend] wants β flexible,           *)
(*  [__skip_rigid] wants [β ∉ ftv P0]), so the dispatcher REFUTES that     *)
(*  configuration from the solution — [sub_flex_rigid_head_absurd], the    *)
(*  subtyping-level twin of [rigid_survives_solution] +                    *)
(*  [ad_pat_consis_rigid_ftv_rev_scoped] (prop_consis_complete.v:5060-5090,*)
(*  where the consistency walk pays exactly this).  A TERM-VARIABLE head   *)
(*  needs no such check: §(N)/§(O) apply unconditionally.                  *)
(* ===================================================================== *)
