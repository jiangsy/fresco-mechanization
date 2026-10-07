(** P6 — COMPLETENESS OF CONSTRAINT COLLECTION AND SOLVING (the "look"
    cluster [a_looksub]/[a_lookeq]/[a_solve_sub]/[a_solve_eq]/
    [a_solve_cstr]/[a_extract], algo/def_rules.v:287-498).

    Paper lemmas (docs/DESIGN-completeness-subtyping.md §7):
      P6-Cv  [a_solve_eq_complete_var]   consistency-proofs.tex:1180
      P6-Cs  [a_lookeq_solve_complete]   consistency-proofs.tex:920
      P6-Rv  [a_solve_sub_complete_var]  subtyping-proofs.tex:1696
      P6-Rs  [a_looksub_solve_complete]  subtyping-proofs.tex:2202
      P6-L   [a_extract_complete_gen]        subtyping-proofs.tex:2729

    THE ρ REPRESENTATION (design locked in DESIGN §7, 2026-07-24): the
    paper's ρ — a substitution from rigid type variables to decorated
    skeletons, with Ψ the solved tags it introduces — is mechanized as
    the RELATION [uskl_rsubst] "ψsub ⊒ρ[Δρ;Ψρ] ψa" (ψsub = ρ(ψa), Δρ = the
    replaced variables): same-constructor congruences + a REFL rule
    (identity-ρ call sites) + one replace-leaf [ψ'' ⊒ var α].  A relation
    rather than a function ([list (atom * uskl)] + msubst) NOT because of
    capture-avoidance — locally nameless + cofinite binders give that for
    free, as for κ — but because the main inductions run on the
    derivation over the SUBJECT ψsub, where each case needs, at its own
    position: (i) the copy-vs-replacement-leaf split (the
    [uskl_rsubst_*_l_inv] inversions); (ii) the image's tags Ψ'' AT THIS
    OCCURRENCE — a variable replaced in both arrow branches contributes
    its image's tags to BOTH copies, so Ψρ is a union WITHOUT cross-copy
    disjointness and the arrow case splits it per branch only by
    inversion; a function-form ρ has no positional reading of "the tags
    introduced by ρ"; (iii) the paper's per-instantiation wf/tags-sort
    premises, carried on the leaf rule.

    [paper-gap] The paper's positional side condition "for every rigid
    variable in ψa substituted by ρ, P_i has the same rigid variable in
    the same position" is mechanized WITHOUT a positional predicate: it
    is RECOVERED as a lemma ([ad_ppre_delta_var_inv]) from FRESHNESS of
    the replaced variables — [α ∈ Δ] (blocks the precision hole rule),
    [binds α abind_tvar Θ] (blocks flex_r), α avoided by κ's images, by
    Θ's definition images ([rsubst_fresh]), and by the subject's ∀◇-shielded
    variables ([pskl_shielded_ftv]).  Δ-membership ALONE is insufficient
    (counterexamples v4/v5, DESIGN §7): precision's tophole_remove/flex_l
    admit ∀◇-wrapped or definition-chained leaf positions whose
    SE-GhostForall output breaks the conclusion precision.  The freshness
    facts hold at the one leaf-creating call site (P6-Rv ForallL: the
    freshly opened binder postdates κ and Θ's definitions, and the
    [a_wf_pskl__tophole] empty-Δ-body discipline keeps it out of ∀◇
    bodies), and are threaded through the conclusions for chaining. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_basic.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.decl.prop_skeleton.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.def_meta.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo_decl.def_subtyping.
Require Import src.fresco.algo.prop_inc.
Require Import src.fresco.algo.prop_basic.
Require Import src.fresco.algo.prop_normal.
Require Import src.fresco.algo.prop_stability.
Require Import src.fresco.algo.prop_refine.
Require Import src.fresco.algo.consis.prop_soundness_consis.
Require Import src.fresco.algo.consis.prop_completeness_consis.
Require Import src.fresco.algo.prop_mono_bridge.
Require Import src.fresco.algo.prop_precise.
Require Import src.fresco.algo.prop_pat_sub.
Require Import src.fresco.algo.consis.prop_consis_precise.
Require Import src.fresco.algo.prop_swap.
Require Import src.fresco.algo.sub.prop_looksub.
Require Import src.fresco.algo.sub.prop_solve_sub.
Require Import src.fresco.algo.sub.prop_completeness_sub_precise.
Require Import src.fresco.algo.prop_metasubst.
Require Import src.fresco.algo.prop_compose.   (* a_inc_dom_flex, a_inc_lookup_mono *)

Set Implicit Arguments.

(* ===================================================================== *)
(*  The ρ relation  [ψsub ⊒ρ[Δρ;Ψρ] ψa]  (DESIGN §7).                      *)
(* ===================================================================== *)

Inductive uskl_rsubst (NM : a_sub_mode) (Θ : aenv)
  : atoms -> atoms -> uskl -> uskl -> Prop :=
| ursubst__refl : forall Δρ Ψρ R,
    lc_uskl R ->
    Ψρ [=] empty ->
    uskl_rsubst NM Θ Δρ Ψρ R R
| ursubst__leaf : forall Δρ Ψρ α Ψ'' ψ'',
    α `in` Δρ ->
    a_tags_sort NM Ψ'' ψ'' ->
    {{ Θ ⨟ empty ⊢ₚₛ ⌊ ψ'' ⌋ˢ }}a ->
    Ψρ [=] Ψ'' ->
    uskl_rsubst NM Θ Δρ Ψρ ψ'' (uskl_var_f α)
| ursubst__arrow : forall Δρ Ψρ Ψ1 Ψ2 R1' R2' R1 R2,
    uskl_rsubst NM Θ Δρ Ψ1 R1' R1 ->
    uskl_rsubst NM Θ Δρ Ψ2 R2' R2 ->
    Ψρ [=] Ψ1 `union` Ψ2 ->
    uskl_rsubst NM Θ Δρ Ψρ (uskl_arrow R1' R2') (uskl_arrow R1 R2)
| ursubst__all_syn : forall L Δρ Ψρ R' R,
    (forall α, α `notin` L ->
       uskl_rsubst NM Θ Δρ Ψρ
         (open_uskl_wrt_uskl R' (uskl_var_f α))
         (open_uskl_wrt_uskl R (uskl_var_f α))) ->
    uskl_rsubst NM Θ Δρ Ψρ (uskl_all_syn R') (uskl_all_syn R)
| ursubst__all_tag : forall L Δρ Ψρ ε R' R,
    (forall α, α `notin` L ->
       uskl_rsubst NM Θ Δρ Ψρ
         (open_uskl_wrt_uskl R' (uskl_var_f α))
         (open_uskl_wrt_uskl R (uskl_var_f α))) ->
    uskl_rsubst NM Θ Δρ Ψρ (uskl_all_tag ε R') (uskl_all_tag ε R)
| ursubst__tophole : forall Δρ Ψρ R' R,
    uskl_rsubst NM Θ Δρ Ψρ R' R ->
    uskl_rsubst NM Θ Δρ Ψρ (uskl_tophole R') (uskl_tophole R)
| ursubst__topholeg : forall Δρ Ψρ R' R,
    uskl_rsubst NM Θ Δρ Ψρ R' R ->
    uskl_rsubst NM Θ Δρ Ψρ (uskl_topholeg R') (uskl_topholeg R).

(** The subject's tags are bounded by the replacement tags plus ψa's. *)
Lemma uskl_rsubst_ftag_sub : forall NM Θ Δρ Ψρ R' R,
  uskl_rsubst NM Θ Δρ Ψρ R' R ->
  ftag_in_uskl R' [<=] Ψρ `union` ftag_in_uskl R.
Proof.
  intros NM Θ Δρ Ψρ R' R H; induction H; simpl; try fsetdec.
  - (* leaf: tags of the image are exactly Ψ'' *)
    pose proof (d_tags_skl_ftag (a_tags_sort_d_tags H0)) as Ht.
    fsetdec.
  - (* all_syn *)
    pick fresh α for L.
    pose proof (H0 α ltac:(solve_notin_auto)) as Hα.
    pose proof (ftag_in_uskl_open_var R' α).
    pose proof (ftag_in_uskl_open_var R α).
    fsetdec.
  - (* all_tag *)
    pick fresh α for L.
    pose proof (H0 α ltac:(solve_notin_auto)) as Hα.
    pose proof (ftag_in_uskl_open_var R' α).
    pose proof (ftag_in_uskl_open_var R α).
    fsetdec.
Qed.

(* ===================================================================== *)
(*  Inversion of [uskl_rsubst] BY SUBJECT SHAPE (P6-Cv/Rv consume these: the   *)
(*  induction is on the [ad_pat_consis]/[ad_pat_sub] derivation of the      *)
(*  ρ(ψa)-SUBJECT, so each case fixes the subject shape and reads off ψa's  *)
(*  shape — either a matching structural congruence / reflexive copy, or a  *)
(*  ρ-LEAF [ψa = var α] with the subject as X's image).                     *)
(* ===================================================================== *)

(** [ψa = var α] with the subject as X's ρ-image (the leaf disjunct). *)
Definition rsubst_leaf (NM : a_sub_mode) (Θ : aenv) (Δρ Ψρ : atoms)
    (R : uskl) (ψa : uskl) : Prop :=
  exists α Ψ'', ψa = uskl_var_f α /\ α `in` Δρ /\
    a_tags_sort NM Ψ'' R /\ {{ Θ ⨟ empty ⊢ₚₛ ⌊ R ⌋ˢ }}a /\ Ψρ [=] Ψ''.

(* [andsplit] splits ONLY [/\] goals — plain [split] would enter the
   single-constructor [a_tags_sort] inside [rsubst_leaf]. *)
Local Ltac rho_andsplit := repeat match goal with |- _ /\ _ => split end.
Local Ltac rho_refl_tac := left; split; [ reflexivity | assumption ].

Lemma uskl_rsubst_arrow_l_inv : forall NM Θ Δρ Ψρ R1' R2' ψa,
  uskl_rsubst NM Θ Δρ Ψρ (uskl_arrow R1' R2') ψa ->
  (ψa = uskl_arrow R1' R2' /\ Ψρ [=] empty)
  \/ rsubst_leaf NM Θ Δρ Ψρ (uskl_arrow R1' R2') ψa
  \/ (exists R1 R2 Ψ1 Ψ2, ψa = uskl_arrow R1 R2 /\
        uskl_rsubst NM Θ Δρ Ψ1 R1' R1 /\ uskl_rsubst NM Θ Δρ Ψ2 R2' R2 /\
        Ψρ [=] Ψ1 `union` Ψ2).
Proof.
  intros NM Θ Δρ Ψρ R1' R2' ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; left; exists α, Ψ''; rho_andsplit; try reflexivity; assumption.
  - right; right; exists R1, R2, Ψ1, Ψ2; rho_andsplit;
      try reflexivity; assumption.
Qed.

Lemma uskl_rsubst_unit_l_inv : forall NM Θ Δρ Ψρ ψa,
  uskl_rsubst NM Θ Δρ Ψρ uskl_unit ψa ->
  (ψa = uskl_unit /\ Ψρ [=] empty) \/ rsubst_leaf NM Θ Δρ Ψρ uskl_unit ψa.
Proof.
  intros NM Θ Δρ Ψρ ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; exists α, Ψ''; rho_andsplit; try reflexivity; assumption.
Qed.

Lemma uskl_rsubst_var_l_inv : forall NM Θ Δρ Ψρ β ψa,
  uskl_rsubst NM Θ Δρ Ψρ (uskl_var_f β) ψa ->
  (ψa = uskl_var_f β /\ Ψρ [=] empty) \/ rsubst_leaf NM Θ Δρ Ψρ (uskl_var_f β) ψa.
Proof.
  intros NM Θ Δρ Ψρ β ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; exists α, Ψ''; rho_andsplit; try reflexivity; assumption.
Qed.

Lemma uskl_rsubst_hole_l_inv : forall NM Θ Δρ Ψρ ψa,
  uskl_rsubst NM Θ Δρ Ψρ uskl_hole ψa ->
  (ψa = uskl_hole /\ Ψρ [=] empty) \/ rsubst_leaf NM Θ Δρ Ψρ uskl_hole ψa.
Proof.
  intros NM Θ Δρ Ψρ ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; exists α, Ψ''; rho_andsplit; try reflexivity; assumption.
Qed.

Lemma uskl_rsubst_holeg_l_inv : forall NM Θ Δρ Ψρ ψa,
  uskl_rsubst NM Θ Δρ Ψρ uskl_holeg ψa ->
  (ψa = uskl_holeg /\ Ψρ [=] empty) \/ rsubst_leaf NM Θ Δρ Ψρ uskl_holeg ψa.
Proof.
  intros NM Θ Δρ Ψρ ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; exists α, Ψ''; rho_andsplit; try reflexivity; assumption.
Qed.

Lemma uskl_rsubst_tophole_l_inv : forall NM Θ Δρ Ψρ R' ψa,
  uskl_rsubst NM Θ Δρ Ψρ (uskl_tophole R') ψa ->
  (ψa = uskl_tophole R' /\ Ψρ [=] empty)
  \/ rsubst_leaf NM Θ Δρ Ψρ (uskl_tophole R') ψa
  \/ (exists R, ψa = uskl_tophole R /\ uskl_rsubst NM Θ Δρ Ψρ R' R).
Proof.
  intros NM Θ Δρ Ψρ R' ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; left; exists α, Ψ''; rho_andsplit; try reflexivity; assumption.
  - right; right; exists R; split; [ reflexivity | assumption ].
Qed.

Lemma uskl_rsubst_topholeg_l_inv : forall NM Θ Δρ Ψρ R' ψa,
  uskl_rsubst NM Θ Δρ Ψρ (uskl_topholeg R') ψa ->
  (ψa = uskl_topholeg R' /\ Ψρ [=] empty)
  \/ rsubst_leaf NM Θ Δρ Ψρ (uskl_topholeg R') ψa
  \/ (exists R, ψa = uskl_topholeg R /\ uskl_rsubst NM Θ Δρ Ψρ R' R).
Proof.
  intros NM Θ Δρ Ψρ R' ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; left; exists α, Ψ''; rho_andsplit; try reflexivity; assumption.
  - right; right; exists R; split; [ reflexivity | assumption ].
Qed.

Lemma uskl_rsubst_all_syn_l_inv : forall NM Θ Δρ Ψρ R' ψa,
  uskl_rsubst NM Θ Δρ Ψρ (uskl_all_syn R') ψa ->
  (ψa = uskl_all_syn R' /\ Ψρ [=] empty)
  \/ rsubst_leaf NM Θ Δρ Ψρ (uskl_all_syn R') ψa
  \/ (exists L R, ψa = uskl_all_syn R /\
        forall α, α `notin` L ->
          uskl_rsubst NM Θ Δρ Ψρ (open_uskl_wrt_uskl R' (uskl_var_f α))
                              (open_uskl_wrt_uskl R (uskl_var_f α))).
Proof.
  intros NM Θ Δρ Ψρ R' ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; left; exists α, Ψ''; rho_andsplit; try reflexivity; assumption.
  - right; right; exists L, R; split; [ reflexivity | eassumption ].
Qed.

Lemma uskl_rsubst_all_tag_l_inv : forall NM Θ Δρ Ψρ ε R' ψa,
  uskl_rsubst NM Θ Δρ Ψρ (uskl_all_tag ε R') ψa ->
  (ψa = uskl_all_tag ε R' /\ Ψρ [=] empty)
  \/ rsubst_leaf NM Θ Δρ Ψρ (uskl_all_tag ε R') ψa
  \/ (exists L R, ψa = uskl_all_tag ε R /\
        forall α, α `notin` L ->
          uskl_rsubst NM Θ Δρ Ψρ (open_uskl_wrt_uskl R' (uskl_var_f α))
                              (open_uskl_wrt_uskl R (uskl_var_f α))).
Proof.
  intros NM Θ Δρ Ψρ ε R' ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; left; exists α, Ψ''; rho_andsplit; try reflexivity; assumption.
  - right; right; exists L, R; split; [ reflexivity | eassumption ].
Qed.

(* ===================================================================== *)
(*  Shielded free variables + the ρ-freshness pack (DESIGN §7).            *)
(*                                                                         *)
(*  [pskl_shielded_ftv P] collects the free type variables occurring       *)
(*  UNDER some ∀◇ of [P].  The replaced variables of ρ must avoid them     *)
(*  (together with κ's and Θ's definition images): this is what recovers   *)
(*  the paper's positional side condition as a LEMMA                       *)
(*  ([ad_ppre_delta_var_inv]) instead of a positional predicate.           *)
(* ===================================================================== *)

Fixpoint pskl_shielded_ftv (P : pskl) : atoms :=
  match P with
  | pskl_unit => {}
  | pskl_var_b _ => {}
  | pskl_var_f _ => {}
  | pskl_arrow P1 P2 => pskl_shielded_ftv P1 `union` pskl_shielded_ftv P2
  | pskl_all_syn P0 => pskl_shielded_ftv P0
  | pskl_hole => {}
  | pskl_tophole P0 => ftvar_in_pskl P0
  end.

Lemma pskl_shielded_ftv_sub_ftv : forall P,
  pskl_shielded_ftv P [<=] ftvar_in_pskl P.
Proof. induction P; simpl; fsetdec. Qed.

(** The ρ-freshness pack for the Θ/κ-stable components: every replaced
    variable is a rigid tvar of Θ that postdates κ's flexible images and
    Θ's definition images.  (The Pi-dependent component —
    [α ∉ pskl_shielded_ftv (msubst_pskl κ Pi)] — and the Δ-membership
    [α ∈ Δ] are separate premises, since Pi and Δ vary per case.) *)
Definition rsubst_fresh (Δρ : atoms) (Θ : aenv) (κ : metasubst) : Prop :=
  forall α0, α0 `in` Δρ ->
    binds α0 abind_tvar Θ /\
    (forall p, In p κ -> α0 `notin` ftvar_in_ptyp (snd p)) /\
    (forall α τ, binds α (abind_flex_mono_def τ) Θ ->
       α0 `notin` ftvar_in_ptyp τ).

(** ρ-freshness survives a RIGID context extension: the ∀ rows of P6-Cs /
    P6-Ss run their IH at [Θ,β], and a rigid entry adds neither a κ-image
    nor a definition, so the only conjunct that moves is the [binds]
    one — monotonically. *)
Lemma rsubst_fresh_weaken_tvar : forall Δρ Θ κ β,
  rsubst_fresh Δρ Θ κ ->
  rsubst_fresh Δρ ((β ~ abind_tvar) ++ Θ) κ.
Proof.
  intros Δρ Θ κ β Hrf α0 Hα0.
  destruct (Hrf α0 Hα0) as (Hb & Hκ & Hdef).
  repeat split.
  - apply binds_app_3; exact Hb.
  - exact Hκ.
  - intros α τ Hbd. analyze_binds Hbd. eapply Hdef; eassumption.
Qed.

(* ===================================================================== *)
(*  Leaf inversion: partial precision at a rigid replaced-variable target  *)
(*  forces the subject to be EXACTLY that variable.                        *)
(* ===================================================================== *)

(** No partial-precision derivation targets [var α0] from an [α0]-free
    subject when [α0] is a Δ-visible rigid tvar avoided by Θ's definition
    images: the var rule needs the occurrence, the hole rule is blocked
    by its Δ-disjointness premise, flex_l chains stay inside Θ's
    definition images, flex_r clashes with X's rigidity. *)
Lemma ad_ppre_var_target_absent : forall Θ Δ Ψ P ψ,
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  forall α', ψ = uskl_var_f α' ->
  {{ ⊢ Θ }}a ->
  α' `in` Δ ->
  binds α' abind_tvar Θ ->
  (forall α τ, binds α (abind_flex_mono_def τ) Θ ->
     α' `notin` ftvar_in_ptyp τ) ->
  α' `notin` ftvar_in_pskl P ->
  False.
Proof.
  intros Θ Δ Ψ P ψ H; induction H;
    intros α00 Heq Hwf Hα0Δ HXb Hdef Hftv; try discriminate Heq.
  - (* var *)
    inversion Heq; subst. simpl in Hftv. clear - Hftv; fsetdec.
  - (* hole: Δ ∩ ftvar(var α00) = ∅ vs α00 ∈ Δ *)
    subst ψ. simpl in H0. clear - H0 Hα0Δ; fsetdec.
  - (* tophole_remove *)
    simpl in Hftv. eapply IHad_partial_precise; eauto.
  - (* flex_l: subject var α unfolds to its Θ-scoped definition *)
    eapply IHad_partial_precise; eauto.
    pose proof (ptyp_to_pskl_ftv τ) as Hp.
    pose proof (Hdef _ _ H) as Hd. clear - Hp Hd; fsetdec.
  - (* flex_r: α00 both rigid and defined-flexible — wf-uniq clash *)
    inversion Heq; subst.
    pose proof (binds_unique _ _ _ _ _ H HXb (a_wf_aenv_uniq Hwf)) as Habs.
    discriminate Habs.
Qed.

(** THE LEAF INVERSION ([paper-gap]: the paper's positional side condition
    "P_i has the same rigid variable in the same position", recovered from
    the freshness of the replaced variable): at target [var α] with
    [α ∈ Δ], [α] rigid in Θ, [α] avoided by Θ's definition images and by
    the subject's ∀◇-shielded variables, the subject IS [var α] and the
    solved tags are empty. *)
Lemma ad_ppre_delta_var_inv : forall Θ Δ Ψ P ψ,
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  forall α', ψ = uskl_var_f α' ->
  {{ ⊢ Θ }}a ->
  α' `in` Δ ->
  binds α' abind_tvar Θ ->
  (forall α τ, binds α (abind_flex_mono_def τ) Θ ->
     α' `notin` ftvar_in_ptyp τ) ->
  α' `notin` pskl_shielded_ftv P ->
  P = pskl_var_f α' /\ Ψ [=] empty.
Proof.
  intros Θ Δ Ψ P ψ H; induction H;
    intros α0 Heq Hwf HαΔ HXb Hdef Hsh; try discriminate Heq.
  - (* var *)
    inversion Heq; subst. split; [ reflexivity | assumption ].
  - (* hole: blocked by Δ-disjointness *)
    exfalso. subst ψ. simpl in H0. clear - H0 HαΔ; fsetdec.
  - (* tophole_remove: the body is wholly shielded — absent-lemma kills *)
    exfalso. simpl in Hsh.
    eapply ad_ppre_var_target_absent; eauto.
  - (* flex_l: the unfolded definition is α0-free — absent-lemma kills *)
    exfalso.
    eapply (ad_ppre_var_target_absent H0 Heq Hwf HαΔ HXb Hdef).
    pose proof (ptyp_to_pskl_ftv τ) as Hp.
    pose proof (Hdef _ _ H) as Hd. clear - Hp Hd; fsetdec.
  - (* flex_r: rigidity clash *)
    exfalso. inversion Heq; subst.
    pose proof (binds_unique _ _ _ _ _ H HXb (a_wf_aenv_uniq Hwf)) as Habs.
    discriminate Habs.
Qed.

(* ===================================================================== *)
(*  Solve-cluster context transport + rigid-variable rename.               *)
(*  The -var lemmas conclude at Θ0; their binder cases get IH conclusions  *)
(*  at (β~tvar)++Θ0 and must strengthen back, then reassemble the          *)
(*  cofinite SE/SS-Forall premises from a single fresh witness by rename.  *)
(* ===================================================================== *)

(** Generic context change: the solve judgments consult Θ only through
    [a_flex_tvar] (positively), [a_flex] (negatively), and — the binder rows
    and SE-FlexR's [guess^TY] — as an AVOID-SET. *)
(* SHRINK-only since the freshness campaign: the exists-fresh binder rules
   carry freshness side conditions, so an ARBITRARY flex-preserving context
   change is FALSE (a new entry can capture a recorded witness).  A context
   that MENTIONS LESS keeps every side condition; growth needs the witness
   to be re-picked, which is the mid-block weakening
   [a_solve_sub_eq_weaken_mid_flex_size] (sub/look/prop_eq_cstr.v). *)
(* ⭐ THE AVOID-SET IS [ftvar_in_aenv], AND [dom] IS NO LONGER A CONDITION
   (2026-08-04).  SE-FlexR now calls [guess^TY], whose freshness is against
   [ftvar_in_aenv Θ] — a flexible's PAYLOAD may mention a name that is in no
   domain — so the five binder rows were strengthened to the same set
   (algo/def_rules.v).  After that NOTHING in the solve cluster reads [dom Θ],
   and the old [dom Θ' [<=] dom Θ] premise is dead weight: it is dropped, so
   this lemma is now strictly stronger than the one the freshness campaign
   left.  Every consumer supplied it for free anyway — they all drop or add
   whole entries. *)

(** Pushing / stripping a RIGID entry: it is never a flexible, so neither
    [a_flex] nor [a_flex_tvar] can see it.  These four are what the solve's
    ∀ rows need now that their premise runs at [(b ~ tvar) ++ Θ]. *)
Lemma a_flex_cons : forall b bd Θ P, a_flex Θ P -> a_flex ((b ~ bd) ++ Θ) P.
Proof.
  intros b bd Θ P H; inversion H; subst;
    [ apply a_flex__var with (α := α)
    | apply a_flex__var_def with (α := α) (τ := τ) ];
    unfold binds; simpl; right; assumption.
Qed.

Lemma a_flex_strip_tvar : forall b Θ P,
  a_flex ((b ~ abind_tvar) ++ Θ) P -> a_flex Θ P.
Proof.
  intros b Θ P H; inversion H; subst;
    match goal with Hb : binds _ _ _ |- _ =>
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq Habs] | Hb'];
        [ discriminate Habs | ] end;
    [ apply a_flex__var with (α := α)
    | apply a_flex__var_def with (α := α) (τ := τ) ]; assumption.
Qed.

Lemma a_flex_tvar_cons : forall b bd Θ α,
  a_flex_tvar Θ α -> a_flex_tvar ((b ~ bd) ++ Θ) α.
Proof.
  intros b bd Θ α [Hb | [τ Hb]];
    [ left | right; exists τ ]; unfold binds; simpl; right; assumption.
Qed.

(** The same, over an arbitrary PREFIX — what the threading rows need, their
    second premise running at [Ξ1 ++ Θ]. *)
Lemma a_flex_tvar_app_mono : forall Ξ Θ Θ' α,
  (forall a, a_flex_tvar Θ a -> a_flex_tvar Θ' a) ->
  a_flex_tvar (Ξ ++ Θ) α -> a_flex_tvar (Ξ ++ Θ') α.
Proof.
  intros Ξ Θ Θ' α Hm [Hb | [τ Hb]];
    destruct (binds_app_1 _ _ _ _ _ Hb) as [HbΞ | HbΘ].
  - left; apply binds_app_2; exact HbΞ.
  - destruct (Hm α (or_introl HbΘ)) as [Hb' | [τ Hb']];
      [ left | right; exists τ ]; apply binds_app_3; exact Hb'.
  - right; exists τ; apply binds_app_2; exact HbΞ.
  - destruct (Hm α (or_intror (ex_intro _ τ HbΘ))) as [Hb' | [τ0 Hb']];
      [ left | right; exists τ0 ]; apply binds_app_3; exact Hb'.
Qed.

Lemma a_flex_app_weaken : forall Ξ Θ P, a_flex Θ P -> a_flex (Ξ ++ Θ) P.
Proof.
  intros Ξ Θ P H; inversion H; subst;
    [ apply a_flex__var with (α := α)
    | apply a_flex__var_def with (α := α) (τ := τ) ];
    apply binds_app_3; assumption.
Qed.

Lemma a_flex_app_anti : forall Ξ Θ Θ' P,
  (forall p, a_flex Θ' p -> a_flex Θ p) ->
  a_flex (Ξ ++ Θ') P -> a_flex (Ξ ++ Θ) P.
Proof.
  intros Ξ Θ Θ' P Hl H; inversion H; subst;
    match goal with Hb : binds ?a ?bd (Ξ ++ Θ') |- _ =>
      destruct (binds_app_1 _ _ _ _ _ Hb) as [HbΞ | HbΘ] end.
  - apply a_flex__var with (α := α); apply binds_app_2; exact HbΞ.
  - apply a_flex_app_weaken. apply Hl.
    apply a_flex__var with (α := α); exact HbΘ.
  - apply a_flex__var_def with (α := α) (τ := τ); apply binds_app_2; exact HbΞ.
  - apply a_flex_app_weaken. apply Hl.
    apply a_flex__var_def with (α := α) (τ := τ); exact HbΘ.
Qed.

(* the shared script for the five binder rows: re-apply the rule (its
   freshness rides the avoid-set SHRINK) and hand the IH the SAME entry
   pushed on both sides *)
Ltac solve_ctx_change_ih :=
  match goal with
  | IH : forall Th2, ftvar_in_aenv Th2 [<=] _ -> _ |- _ =>
      apply IH;
        [ match goal with Hf : ftvar_in_aenv _ [<=] _ |- _ =>
            simpl; clear - Hf; fsetdec end
        | intros α0 Hft; apply a_flex_tvar_cons;
          match goal with Hm : forall a, a_flex_tvar _ a -> _ |- _ =>
            apply Hm; eapply a_flex_tvar_strip_tvar; exact Hft end
        | intros P0 Hf0; apply a_flex_cons;
          match goal with Hl : forall p, a_flex _ p -> _ |- _ =>
            apply Hl; eapply a_flex_strip_tvar; exact Hf0 end ]
  end.

(* the IH at the UNCHANGED context (first premise of a threading row) *)
Ltac solve_ctx_change_ih_here :=
  match goal with
  | IH : forall Th2, ftvar_in_aenv Th2 [<=] _ -> _ |- _ =>
      apply IH; assumption
  end.

(* the IH at [Ξ1 ++ Θ] (second premise of a threading row) *)
Ltac solve_ctx_change_ih_app :=
  match goal with
  | IH : forall Th2, ftvar_in_aenv Th2 [<=] ftvar_in_aenv (?X ++ _) -> _ |- _ =>
      apply IH;
        [ match goal with Hf : ftvar_in_aenv _ [<=] _ |- _ =>
            rewrite ! ftvar_in_aenv_app; clear - Hf; fsetdec end
        | intros α0 Hft;
          match goal with Hm : forall a, a_flex_tvar _ a -> _ |- _ =>
            eapply a_flex_tvar_app_mono; [ exact Hm | exact Hft ] end
        | intros P0 Hf0;
          match goal with Hl : forall p, a_flex _ p -> _ |- _ =>
            eapply a_flex_app_anti; [ exact Hl | exact Hf0 ] end ]
  end.

Ltac solve_ctx_change_binder :=
  econstructor;
  [ match goal with
    | Hfr : _ `notin` _ , Hf : ftvar_in_aenv _ [<=] _ |- _ =>
        clear - Hfr Hf; fsetdec
    end
  | solve_ctx_change_ih ].

Lemma a_solve_sub_eq_ctx_change :
  (forall Θ m P P3 Ξ P', {{ Θ ⊢ₛ P ≼[ m ] P3 ⤳ Ξ ⨾ P' }}a ->
     forall Θ',
     ftvar_in_aenv Θ' [<=] ftvar_in_aenv Θ ->
     (forall α, a_flex_tvar Θ α -> a_flex_tvar Θ' α) ->
     (forall P0, a_flex Θ' P0 -> a_flex Θ P0) ->
     {{ Θ' ⊢ₛ P ≼[ m ] P3 ⤳ Ξ ⨾ P' }}a) /\
  (forall Θ P P3 Ξ P', {{ Θ ⊢ₑ P ∼ P3 ⤳ Ξ ⨾ P' }}a ->
     forall Θ',
     ftvar_in_aenv Θ' [<=] ftvar_in_aenv Θ ->
     (forall α, a_flex_tvar Θ α -> a_flex_tvar Θ' α) ->
     (forall P0, a_flex Θ' P0 -> a_flex Θ P0) ->
     {{ Θ' ⊢ₑ P ∼ P3 ⤳ Ξ ⨾ P' }}a).
Proof.
  apply a_solve_sub_eq_mutind; intros;
    (* binder rows FIRST — [econstructor; eauto] would mis-pick for them *)
    try solve [ solve_ctx_change_binder ];
    (* SS-ForallR: the output passes THROUGH, so [econstructor] leaves the
       witness an evar — name it *)
    try solve
      [ match goal with
        | Hfr : ?b `notin` _ |- {{ _ ⊢ₛ _ ≼[ _ ] pskl_all_syn _ ⤳ _ ⨾ _ }}a =>
            apply a_solve_sub__forall_r with (β := b); [ | | | ];
            [ assumption
            | assumption
            | match goal with Hf : ftvar_in_aenv _ [<=] _ |- _ =>
                clear - Hfr Hf; fsetdec end
            | solve_ctx_change_ih ]
        end ];
    (* the THREADING rows: the second premise runs at [Ξ1 ++ Θ] *)
    try solve
      [ econstructor;
        [ solve_ctx_change_ih_here
        | solve_ctx_change_ih_app ] ];
    (* SE-FlexR: the flex tests transport by the two flex conditions, and
       [guess^TY] by the [ftvar_in_aenv] shrink *)
    try solve
      [ match goal with
        | Hb : a_flex_tvar _ _, Hnf : a_non_flex _ _,
          Hng : nonghost_pskl _,
          Hgu : a_guess_mono _ _ _ _,
          Hf : ftvar_in_aenv _ [<=] _,
          Hmono : forall a, a_flex_tvar _ a -> _,
          Hfl : forall p, a_flex _ p -> _ |- _ =>
            destruct Hnf as [Hlc Hnf'];
            apply a_solve_eq__flex_r;
              [ apply Hmono; exact Hb
              | split; [ exact Hlc | intro Hf0; exact (Hnf' (Hfl _ Hf0)) ]
              | exact Hng
              | eapply a_guess_mono_ctx_shrink; [ exact Hgu | exact Hf ] ]
        end ];
    (* the structural rows *)
    try solve [ econstructor; eauto ].
Qed.

(** Strengthening: drop a rigid tvar cons. *)
Lemma a_solve_eq_strengthen_tvar : forall β Θ0 P P3 Ξ P',
  {{ ((β ~ abind_tvar) ++ Θ0) ⊢ₑ P ∼ P3 ⤳ Ξ ⨾ P' }}a ->
  {{ Θ0 ⊢ₑ P ∼ P3 ⤳ Ξ ⨾ P' }}a.
Proof.
  intros β Θ0 P P3 Ξ P' H.
  eapply (proj2 a_solve_sub_eq_ctx_change); [ exact H | | | ].
  - simpl. fsetdec.
  - intros α Hft. eapply a_flex_tvar_strip_tvar; exact Hft.
  - intros P0 Hf. apply (a_flex_cons β abind_tvar); exact Hf.
Qed.

(* ===================================================================== *)
(*  RESTART NOTE (2026-08-04) — [a_solve_eq_weaken_tvar{,_size}] DELETED.  *)
(*                                                                        *)
(*  It claimed: a rigid-tvar CONS weakens an eq-solve,                     *)
(*    [{{ Θ0 ⊢ₑ P ∼ P3 ⤳ Ξ ⨾ P'  ⟹  ((β ~ tvar) ++ Θ0) }}a ⊢ₑ … ]       *)
(*  (EQ half only — every eq-∀ rule CLOSES its output, so a colliding      *)
(*  witness can be re-freshened with the output unchanged, whereas         *)
(*  SS-ForallR PINS its leaked witness and the sub twin is FALSE).         *)
(*                                                                        *)
(*  ⭐ IT HAS NO CONSUMERS, and had none at the pre-repair baseline        *)
(*  [d5f9169] either.  What the tree actually calls is the MID-BLOCK       *)
(*  twin [a_solve_sub_eq_weaken_mid_flex_size]                            *)
(*  (sub/look/prop_eq_cstr.v, P6-Cs), which inserts an [all_flex_mono]   *)
(*  block in the MIDDLE — a different statement, derivable neither way     *)
(*  from this one.  The solve's ∀ rows now push their witness onto the     *)
(*  context, but that is a rigid a MID-insertion absorbs by taking         *)
(*  [Ξl := (b ~ tvar) ++ Ξl]; it creates no new demand for a cons.         *)
(*                                                                        *)
(*  ⚠️ THE REPAIR ALSO MADE IT COSTLIER, which is why it is going rather   *)
(*  than being carried: under the repaired SolE-FlexR the statement is     *)
(*  FALSE without [β ∉ dom Ξ].  SE-FlexR calls [guess^TY], whose invented  *)
(*  names avoid [ftvar_in_aenv Θ0]; pushing a new entry β onto Θ0 enlarges *)
(*  that set, so a run that happened to generate the atom β cannot be      *)
(*  replayed — the hole row's side condition fails at exactly that α.      *)
(*  (Not an artefact: it says you may not retroactively add a context      *)
(*  entry COLLIDING with a name the algorithm invented, which is what the  *)
(*  reference implementation's global counter enforces.)  A re-proof needs *)
(*  that premise, the SWAP witness-move ([a_solve_eq_move_binder],         *)
(*  prop_solve_sub.v — the old proof's double RENAME cannot survive, since *)
(*  the witness now sits IN the premise's context) and an adjacent-rigid   *)
(*  EXCHANGE from [a_solve_sub_eq_ctx_change].  Restore from git if a      *)
(*  consumer ever appears.                                                *)
(* ===================================================================== *)

(* [a_solve_sub_eq_rename] REPLACED by the equivariance kit's
   [a_solve_sub_eq_swap] (prop_swap.v): a transposition needs no
   target-freshness side condition at all, which is what the freshness
   campaign's asymmetric rename shape was working around. *)

(* ===================================================================== *)
(*  Shape/tags helpers for the special cases (P0 = □; synthesized Q).      *)
(* ===================================================================== *)

(** Syn-paintings are synthesized skeletons. *)

(** Refining the hole yields a synthesized skeleton (paper: "by inversion
    on the refinement premise, Q is a synthesised skeleton"). *)
Lemma ad_refine_syn_hole_sskl : forall Θ Δ Qh Q,
  {{ Θ ⨟ Δ ⊢ᵣ Qh ⊳ Q }}ad ->
  Qh = bskl_hole ->
  is_sskl Q.
Proof.
  intros Θ Δ Qh Q H; induction H; intros Heq; try discriminate Heq.
  - (* hole *)
    apply is_sskl_pskl_to_bskl_syn.
    eapply a_wf_pskl_lc; eassumption.
  - (* flex_r *)
    auto with fresco.
Qed.

(** Consistency against a synthesized target solves no tags (the only
    tag-consuming rule targets [all_inh]). *)
Lemma ad_pat_consis_sskl_tags : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  {{ ⊢ Θ }}a ->
  is_sskl Q ->
  Ψ [=] empty.
Proof.
  intros Ψ Θ R Q H; induction H; intros Hwf Hsk;
    try solve [ assumption | inversion Hsk ].
  - (* arrow *)
    inversion Hsk; subst.
    specialize (IHad_pat_consis1 Hwf ltac:(assumption)).
    specialize (IHad_pat_consis2 Hwf ltac:(assumption)).
    fsetdec.
  - (* forall_syn_tagged *)
    inversion Hsk; subst.
    match goal with HskB : forall α, α `notin` ?L0 -> is_sskl _ |- _ =>
      pick fresh α for (L `union` L0 `union` dom Θ);
      apply (H0 α ltac:(solve_notin_auto));
      [ apply a_wf_aenv__tvar; [ fsetdec | exact Hwf ]
      | apply HskB; fsetdec ]
    end.
  - (* forall_syn *)
    inversion Hsk; subst.
    match goal with HskB : forall α, α `notin` ?L0 -> is_sskl _ |- _ =>
      pick fresh α for (L `union` L0 `union` dom Θ);
      apply (H0 α ltac:(solve_notin_auto));
      [ apply a_wf_aenv__tvar; [ fsetdec | exact Hwf ]
      | apply HskB; fsetdec ]
    end.
  - (* topholeg *)
    inversion Hsk; subst. apply IHad_pat_consis; assumption.
  - (* tophole *)
    inversion Hsk; subst. apply IHad_pat_consis; assumption.
  - (* tophole_drop *)
    apply IHad_pat_consis; assumption.
  - (* flex_l *)
    apply IHad_pat_consis; assumption.
  - (* flex_r *)
    apply IHad_pat_consis; [ assumption | ].
    unfold ptyp_to_bskl_syn.
    apply is_sskl_pskl_to_bskl_syn.
    apply ptyp_to_pskl_lc.
    eapply a_wf_ptyp_lc.
    eapply a_wf_aenv_binds_def_wf; eassumption.
Qed.

(* ===================================================================== *)
(*  Shielded-variable bounds through solving (chaining the freshness       *)
(*  pack through a_solve_cstr / the arrow case).                           *)
(* ===================================================================== *)

Lemma pskl_shielded_ftv_open_rec_lower : forall P P' k,
  pskl_shielded_ftv P [<=]
  pskl_shielded_ftv (open_pskl_wrt_pskl_rec k P' P).
Proof.
  induction P; intros P' k; simpl; try fsetdec.
  - pose proof (IHP1 P' k); pose proof (IHP2 P' k); fsetdec.
  - apply IHP.
  - pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_rec_lower P P' k); fsetdec.
Qed.

Lemma pskl_shielded_ftv_open_rec_upper : forall P P' k,
  pskl_shielded_ftv (open_pskl_wrt_pskl_rec k P' P) [<=]
  pskl_shielded_ftv P `union` ftvar_in_pskl P'.
Proof.
  induction P; intros P' k; simpl; try fsetdec.
  - (* var_b *)
    destruct (lt_eq_lt_dec n k) as [[Hlt | Heq] | Hgt]; simpl;
      try fsetdec.
    pose proof (pskl_shielded_ftv_sub_ftv P'); fsetdec.
  - pose proof (IHP1 P' k); pose proof (IHP2 P' k); fsetdec.
  - apply IHP.
  - pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_rec_upper P P' k); fsetdec.
Qed.

Lemma pskl_shielded_ftv_open_lower : forall P P',
  pskl_shielded_ftv P [<=]
  pskl_shielded_ftv (open_pskl_wrt_pskl P P').
Proof. intros; apply pskl_shielded_ftv_open_rec_lower. Qed.

Lemma pskl_shielded_ftv_open_upper : forall P P',
  pskl_shielded_ftv (open_pskl_wrt_pskl P P') [<=]
  pskl_shielded_ftv P `union` ftvar_in_pskl P'.
Proof. intros; apply pskl_shielded_ftv_open_rec_upper. Qed.

(* RESTART NOTE [freshness campaign]: [a_solve_sub_eq_shielded] (solving
   bounds the output's shielded variables by the subject's shielded ones
   plus the target's) was DELETED — it had NO consumers, and its SUB half is
   false under the faithful SS-ForallR (the leaked binder enters the
   output's shielded set).  A re-proof would mirror [a_solve_sub_eq_ftv]'s
   disjunctive shape: shielded-or-fresh-for-dom-Θ.
   ⭐ THE EQ HALF IS BACK (2026-08-04, [a_solve_eq_shielded] below), because
   the repair gave it a consumer: the eq-∀ rows now run their premise at
   [(β ~ tvar) ++ Θ], so [a_solve_eq_wf] must STRIP β back off, and the only
   sound way to do that is [a_wf_pskl_strip_tvar_mid]'s side condition
   "β is not SHIELDED in the output".  The SUB half stays deleted and stays
   false. *)

(* ===================================================================== *)
(*  msubst-avoidance: a variable fresh from κ's images survives msubst.    *)
(* ===================================================================== *)

Lemma msubst_lookup_ftv_avoid : forall κ α β,
  (forall p, In p κ -> α `notin` ftvar_in_ptyp (snd p)) ->
  α `in` ftvar_in_ptyp (msubst_lookup κ β) ->
  β = α.
Proof.
  induction κ as [ | [α2 τ] κ' IH ]; intros α β Hav Hα; simpl in Hα.
  - clear - Hα; fsetdec.
  - destruct (β == α2) as [Heq | Hne].
    + exfalso. apply (Hav (α2, τ) (or_introl eq_refl)). exact Hα.
    + apply IH; [ intros p Hp; apply Hav; right; exact Hp | exact Hα ].
Qed.

Lemma msubst_pskl_ftv_avoid : forall κ P α',
  (forall p, In p κ -> α' `notin` ftvar_in_ptyp (snd p)) ->
  α' `notin` ftvar_in_pskl P ->
  α' `notin` ftvar_in_pskl (msubst_pskl κ P).
Proof.
  intros κ P α' Hav.
  induction P as [ | n | β | Pa IHa Pb IHb | Pall IHall | | Pt IHt ];
    intros Hni Hα; simpl in *.
  - fsetdec.
  - fsetdec.
  - (* var *)
    pose proof (ftvar_ptyp_to_pskl (msubst_lookup κ β)) as Hp.
    assert (HX' : α' `in` ftvar_in_ptyp (msubst_lookup κ β))
      by (clear - Hα Hp; fsetdec).
    apply msubst_lookup_ftv_avoid in HX'; [ subst | exact Hav ].
    clear - Hni; fsetdec.
  - apply union_1 in Hα; destruct Hα as [Hα | Hα];
      [ apply IHa | apply IHb ];
      solve [ clear - Hni; fsetdec | exact Hα ].
  - apply IHall; [ clear - Hni; fsetdec | exact Hα ].
  - fsetdec.
  - apply IHt; [ clear - Hni; fsetdec | exact Hα ].
Qed.

(** Monotype paintings shield nothing. *)
Lemma pskl_shielded_ftv_ptyp_to_pskl : forall A,
  pskl_shielded_ftv (ptyp_to_pskl A) [=] {}.
Proof. induction A; simpl; fsetdec. Qed.

Lemma msubst_pskl_shielded_avoid : forall κ P α',
  (forall p, In p κ -> α' `notin` ftvar_in_ptyp (snd p)) ->
  α' `notin` pskl_shielded_ftv P ->
  α' `notin` pskl_shielded_ftv (msubst_pskl κ P).
Proof.
  intros κ P α' Hav.
  induction P as [ | n | β | Pa IHa Pb IHb | Pall IHall | | Pt IHt ];
    intros Hni Hα; simpl in *.
  - fsetdec.
  - fsetdec.
  - (* var: the image is a painting — nothing shielded *)
    pose proof (pskl_shielded_ftv_ptyp_to_pskl (msubst_lookup κ β)) as He.
    clear - He Hα; fsetdec.
  - apply union_1 in Hα; destruct Hα as [Hα | Hα];
      [ apply IHa | apply IHb ];
      solve [ clear - Hni; fsetdec | exact Hα ].
  - apply IHall; [ exact Hni | exact Hα ].
  - fsetdec.
  - (* tophole: the whole body's ftv *)
    revert Hα. apply msubst_pskl_ftv_avoid; [ exact Hav | exact Hni ].
Qed.

(** msubst-image of a var: recover the var (α avoided by κ's images). *)
Lemma msubst_pskl_var_inv : forall κ Pi α',
  (forall p, In p κ -> α' `notin` ftvar_in_ptyp (snd p)) ->
  msubst_pskl κ Pi = pskl_var_f α' ->
  Pi = pskl_var_f α'.
Proof.
  intros κ Pi α' Hav Heq.
  destruct Pi as [ | n | β | | | | ]; simpl in Heq; try discriminate Heq.
  f_equal.
  assert (Hα : α' `in` ftvar_in_ptyp (msubst_lookup κ β)).
  { pose proof (ftvar_ptyp_to_pskl (msubst_lookup κ β)) as Hp.
    rewrite Heq in Hp. simpl in Hp. clear - Hp; fsetdec. }
  eapply msubst_lookup_ftv_avoid; eassumption.
Qed.

(* ===================================================================== *)
(*  The packaged -var LEAF case (paper: <<If ψa is a rigid variable        *)
(*  substituted by ρ, then P_i = ψa.  The tag contexts Ψ_i and Ψ_a are     *)
(*  empty, and the goal follows from SE-Var (SS-Var), choosing             *)
(*  P_a = P_i and κ_a = κ.>>  consistency-proofs.tex:1249-1252).           *)
(*  Both P6-Cv and P6-Rv consume it: [SE-Var]/[SS-Var] fire on the         *)
(*  recovered var subject against ANY target.                              *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  P6-Cv support kit: solve-eq determinism on the hole subject, wf        *)
(*  preservation for [a_solve_eq], Θ-weakening of the ρ relation, and      *)
(*  the Θ-tvar strengthening of partial precision (for the binder cases    *)
(*  whose IH runs at [(α~tvar)++Θ]).                                       *)
(* ===================================================================== *)

(** Solving with the hole subject returns the target verbatim, and generates
    NOTHING (the only applicable rules are SE-GhostL and SE-VacuousR).  The
    paper uses this silently in every [P_i = □] subcase: the IH's
    existential output IS the target.

    ⚠️ SE-FlexR is what would break this, and it is exactly why its subject
    carries [nonghost_pskl] (algo/def_rules.v): under the repaired row
    [guess^TY(◇)] invents a FRESH flexible, so [◇ ∼ α̂] would ALSO derive
    [⤳ (α̂1 ~ flex) ⨾ α̂1].  The reference implementation never takes that
    branch — its match puts SolE-GhostL first — and neither does this. *)
Lemma a_solve_eq_hole_subject_inv : forall Θ P Ξ P',
  {{ Θ ⊢ₑ pskl_hole ∼ P ⤳ Ξ ⨾ P' }}a ->
  Ξ = nil /\ P' = P.
Proof.
  intros Θ P Ξ P' H; inversion H; subst; try solve [ split; reflexivity ];
    (* SE-FlexR is barred by [nonghost_pskl ◇]; SE-GhostGuarded by the
       subject shape *)
    try solve [ match goal with H0 : nonghost_pskl pskl_hole |- _ =>
                  inversion H0 end ];
    inv_guarded_hole.
Qed.

(** Θ-weakening of the ρ relation (binds-monotone; the leaf's image wf
    weakens). *)
(* ===================================================================== *)
(*  Inversion of [uskl_rsubst] BY TARGET SHAPE — the mirror family            *)
(*                                                                        *)
(*  P6-Cs (and P6-Ss's Arrow / ∀ rows) dispatch on the IDEAL subject       *)
(*  [R'], not on the derivation, so what they need is the opposite         *)
(*  reading: the TARGET's shape is known and the ρ-IMAGE's has to be read  *)
(*  off.  That direction is strictly simpler than [_l_inv] — for every     *)
(*  NON-VARIABLE target only [ursubst__refl] and the matching congruence      *)
(*  apply ([ursubst__leaf] demands a variable target) — and the two collapse: *)
(*  [ursubst__refl] carries [lc_uskl], so its components are themselves       *)
(*  reflexive ρ-images at [Ψρ = ∅].  Hence a SINGLE congruence conclusion, *)
(*  with no [rsubst_leaf] disjunct to dispatch.                              *)
(* ===================================================================== *)

Lemma uskl_rsubst_arrow_r_inv : forall NM Θ Δρ Ψρ R' ψ1 ψ2,
  uskl_rsubst NM Θ Δρ Ψρ R' (uskl_arrow ψ1 ψ2) ->
  exists R1' R2' Ψ1 Ψ2,
    R' = uskl_arrow R1' R2' /\
    uskl_rsubst NM Θ Δρ Ψ1 R1' ψ1 /\ uskl_rsubst NM Θ Δρ Ψ2 R2' ψ2 /\
    Ψρ [=] Ψ1 `union` Ψ2.
Proof.
  intros NM Θ Δρ Ψρ R' ψ1 ψ2 H; inversion H; subst.
  - (* refl : lc splits, so each component is reflexive at ∅ *)
    match goal with Hlc : lc_uskl (uskl_arrow _ _) |- _ =>
      inversion Hlc; subst end.
    exists ψ1, ψ2, empty, empty; rho_andsplit;
      [ reflexivity
      | apply ursubst__refl; [ assumption | clear; fsetdec ]
      | apply ursubst__refl; [ assumption | clear; fsetdec ]
      | clear - H1; fsetdec ].
  - exists R1', R2', Ψ1, Ψ2; rho_andsplit;
      try reflexivity; assumption.
Qed.

Lemma uskl_rsubst_tophole_r_inv : forall NM Θ Δρ Ψρ R' ψ,
  uskl_rsubst NM Θ Δρ Ψρ R' (uskl_tophole ψ) ->
  exists R0, R' = uskl_tophole R0 /\ uskl_rsubst NM Θ Δρ Ψρ R0 ψ.
Proof.
  intros NM Θ Δρ Ψρ R' ψ H; inversion H; subst.
  - match goal with Hlc : lc_uskl (uskl_tophole _) |- _ =>
      inversion Hlc; subst end.
    exists ψ; split;
      [ reflexivity | apply ursubst__refl; assumption ].
  - exists R'0; split; [ reflexivity | assumption ].
Qed.

Lemma uskl_rsubst_topholeg_r_inv : forall NM Θ Δρ Ψρ R' ψ,
  uskl_rsubst NM Θ Δρ Ψρ R' (uskl_topholeg ψ) ->
  exists R0, R' = uskl_topholeg R0 /\ uskl_rsubst NM Θ Δρ Ψρ R0 ψ.
Proof.
  intros NM Θ Δρ Ψρ R' ψ H; inversion H; subst.
  - match goal with Hlc : lc_uskl (uskl_topholeg _) |- _ =>
      inversion Hlc; subst end.
    exists ψ; split;
      [ reflexivity | apply ursubst__refl; assumption ].
  - exists R'0; split; [ reflexivity | assumption ].
Qed.

Lemma uskl_rsubst_all_syn_r_inv : forall NM Θ Δρ Ψρ R' ψ,
  uskl_rsubst NM Θ Δρ Ψρ R' (uskl_all_syn ψ) ->
  exists L R0, R' = uskl_all_syn R0 /\
    forall α, α `notin` L ->
      uskl_rsubst NM Θ Δρ Ψρ (open_uskl_wrt_uskl R0 (uskl_var_f α))
                          (open_uskl_wrt_uskl ψ (uskl_var_f α)).
Proof.
  intros NM Θ Δρ Ψρ R' ψ H; inversion H; subst.
  - match goal with Hlc : lc_uskl (uskl_all_syn _) |- _ =>
      inversion Hlc; subst end.
    exists empty, ψ; split; [ reflexivity | ].
    intros α Hα; apply ursubst__refl; [ auto | assumption ].
  - exists L, R'0; split; [ reflexivity | eassumption ].
Qed.

Lemma uskl_rsubst_all_tag_r_inv : forall NM Θ Δρ Ψρ R' ε ψ,
  uskl_rsubst NM Θ Δρ Ψρ R' (uskl_all_tag ε ψ) ->
  exists L R0, R' = uskl_all_tag ε R0 /\
    forall α, α `notin` L ->
      uskl_rsubst NM Θ Δρ Ψρ (open_uskl_wrt_uskl R0 (uskl_var_f α))
                          (open_uskl_wrt_uskl ψ (uskl_var_f α)).
Proof.
  intros NM Θ Δρ Ψρ R' ε ψ H; inversion H; subst.
  - match goal with Hlc : lc_uskl (uskl_all_tag _ _) |- _ =>
      inversion Hlc; subst end.
    exists empty, ψ; split; [ reflexivity | ].
    intros α Hα; apply ursubst__refl; [ auto | assumption ].
  - exists L, R'0; split; [ reflexivity | eassumption ].
Qed.

Lemma uskl_rsubst_is_tskl : forall NM Θ Δρ Ψρ R' R,
  uskl_rsubst NM Θ Δρ Ψρ R' R ->
  is_tskl R ->
  is_tskl R'.
Proof.
  intros NM Θ Δρ Ψρ R' R H; induction H; intros Ht.
  - exact Ht.
  - (* leaf: the image is tags-sorted, hence decorated *)
    inversion H0; assumption.
  - inversion Ht; subst; apply is_tskl__arrow; auto.
  - (* ∀ (untagged): not a decorated shape *) inversion Ht.
  - (* ∀^ε *)
    inversion Ht; subst.
    match goal with Hb : forall α, α `notin` ?L1 -> is_tskl _ |- _ =>
      apply is_tskl__all_tag with (L := L `union` L1); intros α Hα;
      apply H0; [ clear - Hα; solve_notin | apply Hb; clear - Hα; solve_notin ]
    end.
  - (* ∀◇ : not a decorated shape *) inversion Ht.
  - inversion Ht; subst; apply is_tskl__topholeg; auto.
Qed.

Lemma uskl_rsubst_ftv_subject_bound : forall NM Θ Δρ Ψρ R' R,
  uskl_rsubst NM Θ Δρ Ψρ R' R ->
  ftvar_in_uskl R' [<=] ftvar_in_uskl R `union` dom Θ.
Proof.
  intros NM Θ Δρ Ψρ R' R H; induction H; cbn [ftvar_in_uskl];
    try solve [ clear; fsetdec | clear - IHuskl_rsubst; fsetdec
              | clear - IHuskl_rsubst1 IHuskl_rsubst2; fsetdec ].
  - (* leaf : the image is well-formed in Θ *)
    pose proof (a_wf_pskl_ftv_dom H1) as Hd.
    (* [uskl_to_pskl_ftv] is a duplicate of this one and lives DOWNSTREAM *)
    rewrite ftvar_in_pskl_uskl_to_pskl in Hd. clear - Hd; fsetdec.
  - (* ∀ (untagged) *)
    pick fresh α for (L `union` ftvar_in_uskl R' `union` ftvar_in_uskl R).
    pose proof (H0 α ltac:(clear - Fr; solve_notin)) as Hα.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R' (uskl_var_f α)).
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R (uskl_var_f α)).
    cbn [ftvar_in_uskl] in *. clear - Hα H1 H2 Fr. fsetdec.
  - (* ∀^ε *)
    pick fresh α for (L `union` ftvar_in_uskl R' `union` ftvar_in_uskl R).
    pose proof (H0 α ltac:(clear - Fr; solve_notin)) as Hα.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R' (uskl_var_f α)).
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R (uskl_var_f α)).
    cbn [ftvar_in_uskl] in *. clear - Hα H1 H2 Fr. fsetdec.
Qed.

(** …and the SHARP version, which drops the [dom Θ] slack entirely.  ρ only
    ever acts at a [Δρ]-variable ([ursubst__leaf] is the only non-congruence
    rule), so an ideal that mentions no [Δρ]-variable is its own image.

    This is what P6-Ss Phase B needs: the ftv-𝒞 conclusion must survive a
    Sub-ForallR, whose fresh binder β enters the DERIVATION's context — so a
    bound naming [dom Θ] (or P6-Cs's [dom Θs], the ρ-images' scope, which a
    nested Sub-ForallL's guess drags β into) readmits exactly the binder being
    stripped.  Under the apartness premise no context appears at all.
    P6-Cs keeps Δρ constant and never moves ψa, and P6-Ss's main induction
    picks every Sub-ForallL binder fresh for ψa, so both preserve it.
    See docs/DESIGN-completeness-subtyping.md §8 (h). *)
Lemma uskl_rsubst_ftv_apart : forall NM Θ Δρ Ψρ R' R,
  uskl_rsubst NM Θ Δρ Ψρ R' R ->
  (ftvar_in_uskl R) ∩ Δρ [=] empty ->
  ftvar_in_uskl R' [<=] ftvar_in_uskl R.
Proof.
  intros NM Θ Δρ Ψρ R' R H; induction H; intros Hap; cbn [ftvar_in_uskl] in *;
    try solve [ clear; fsetdec
              | apply IHuskl_rsubst; clear - Hap; fsetdec
              | (* arrow *)
                pose proof (IHuskl_rsubst1 ltac:(clear - Hap; solve_notin_auto));
                pose proof (IHuskl_rsubst2 ltac:(clear - Hap; solve_notin_auto));
                clear - H2 H3; fsetdec ].
  - (* leaf : the ideal IS a Δρ-variable, which the premise forbids *)
    exfalso. clear - H Hap; fsetdec.
  - (* ∀ (untagged) — open with a binder that is itself Δρ-fresh *)
    pick fresh α for (L `union` Δρ `union` ftvar_in_uskl R'
                        `union` ftvar_in_uskl R).
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R' (uskl_var_f α)) as Hlo.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R (uskl_var_f α)) as Hup.
    cbn [ftvar_in_uskl] in Hup.
    pose proof (H0 α ltac:(clear - Fr; solve_notin)
                  ltac:(clear - Hap Hup Fr; solve_notin_auto)) as Hα.
    clear - Hα Hlo Hup Fr; fsetdec.
  - (* ∀^ε *)
    pick fresh α for (L `union` Δρ `union` ftvar_in_uskl R'
                        `union` ftvar_in_uskl R).
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R' (uskl_var_f α)) as Hlo.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R (uskl_var_f α)) as Hup.
    cbn [ftvar_in_uskl] in Hup.
    pose proof (H0 α ltac:(clear - Fr; solve_notin)
                  ltac:(clear - Hap Hup Fr; solve_notin_auto)) as Hα.
    clear - Hα Hlo Hup Fr; fsetdec.
Qed.

Lemma uskl_rsubst_weaken : forall NM Θ Δρ Ψρ R' R,
  uskl_rsubst NM Θ Δρ Ψρ R' R ->
  forall Θ', (forall x b, binds x b Θ -> binds x b Θ') ->
  uskl_rsubst NM Θ' Δρ Ψρ R' R.
Proof.
  intros NM Θ Δρ Ψρ R' R H; induction H; intros Θ' Hmon.
  - apply ursubst__refl; assumption.
  - eapply ursubst__leaf; [ exact H | exact H0 | | exact H2 ].
    eapply a_wf_pskl_weaken; eassumption.
  - eapply ursubst__arrow; eauto.
  - eapply ursubst__all_syn with (L := L); eauto.
  - eapply ursubst__all_tag with (L := L); eauto.
  - apply ursubst__tophole; eauto.
  - apply ursubst__topholeg; eauto.
Qed.

(** Drop a mid entry a binding does not match. *)
Lemma binds_mid_drop : forall (Θ1 Θ0 : aenv) α β (b bmid : abind),
  binds β b (Θ1 ++ (α ~ bmid) ++ Θ0) ->
  (β = α -> b <> bmid) ->
  binds β b (Θ1 ++ Θ0).
Proof.
  intros Θ1 Θ0 α β b bmid Hb Hne.
  unfold binds in *.
  apply in_app_iff in Hb; destruct Hb as [Hb | Hb].
  - apply in_app_iff; left; exact Hb.
  - simpl in Hb; destruct Hb as [Heq | Hb].
    + inversion Heq; subst. exfalso. exact (Hne eq_refl eq_refl).
    + apply in_app_iff; right; exact Hb.
Qed.

(** Partial precision does not need a rigid tvar entry the subject-side Δ
    already covers: the binder cases' IH concludes at [(β~tvar)++Θ] and
    must come back to [Θ] (the conclusion's context), with [β ∈ Δ]
    re-deriving the var rule's tvar side. *)
Lemma ad_partial_precise_strengthen_tvar_mid : forall Θfull Δ Ψ P ψ,
  {{ Θfull ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  forall α1 Θ1 Θ0,
  Θfull = Θ1 ++ (α1 ~ abind_tvar) ++ Θ0 ->
  α1 `in` Δ ->
  {{ (Θ1 ++ Θ0) ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad.
Proof.
  intros Θfull Δ Ψ P ψ H; induction H; intros α1 Θ1 Θ0 Heq Hα2Δ; subst.
  - apply ad_ppre__unit; assumption.
  - apply ad_ppre__var; [ assumption | ].
    destruct H0 as [HΔ | [Hb | [Hb | [τ Hb]]]].
    + left; exact HΔ.
    + destruct (α == α1) as [HeqXZ | HneXZ];
        [ subst; left; exact Hα2Δ
        | right; left; exact (binds_remove_mid _ _ _ _ _ _ _ Hb HneXZ) ].
    + right; right; left.
      eapply binds_mid_drop; [ exact Hb | intros _ Habs; discriminate Habs ].
    + right; right; right; exists τ.
      eapply binds_mid_drop; [ exact Hb | intros _ Habs; discriminate Habs ].
  - eapply ad_ppre__arrow;
      [ apply (IHad_partial_precise1 α1 Θ1 Θ0 eq_refl Hα2Δ)
      | apply (IHad_partial_precise2 α1 Θ1 Θ0 eq_refl Hα2Δ)
      | assumption ].
  - eapply ad_ppre__forall with (L := L);
      [ intros α Hα;
        apply (H0 α Hα α1 Θ1 Θ0 eq_refl); clear - Hα2Δ; fsetdec
      | assumption ].
  - apply ad_ppre__hole; assumption.
  - apply ad_ppre__tophole_remove.
    apply (IHad_partial_precise α1 Θ1 Θ0 eq_refl Hα2Δ).
  - eapply ad_ppre__tophole_fill with (L := L).
    intros α Hα.
    apply (H0 α Hα α1 ((α ~ abind_tvar) ++ Θ1) Θ0 eq_refl Hα2Δ).
  - apply ad_ppre__tophole_keep.
    apply (IHad_partial_precise α1 Θ1 Θ0 eq_refl Hα2Δ).
  - eapply ad_ppre__flex_l;
      [ eapply binds_mid_drop;
        [ exact H | intros _ Habs; discriminate Habs ]
      | apply (IHad_partial_precise α1 Θ1 Θ0 eq_refl Hα2Δ) ].
  - eapply ad_ppre__flex_r;
      [ eapply binds_mid_drop;
        [ exact H | intros _ Habs; discriminate Habs ]
      | apply (IHad_partial_precise α1 Θ1 Θ0 eq_refl Hα2Δ) ].
Qed.

Lemma ad_partial_precise_strengthen_tvar : forall α1 Θ0 Δ Ψ P ψ,
  {{ ((α1 ~ abind_tvar) ++ Θ0) ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  α1 `in` Δ ->
  {{ Θ0 ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad.
Proof.
  intros α1 Θ0 Δ Ψ P ψ H Hα2.
  exact (@ad_partial_precise_strengthen_tvar_mid _ _ _ _ _ H α1 nil Θ0
           eq_refl Hα2).
Qed.

(* ===================================================================== *)
(*  ⭐ STRIPPING A RIGID FROM THE MIDDLE OF A wf CONTEXT (2026-08-04).      *)
(*                                                                        *)
(*  The repair forces this.  The solve's ∀ rows now run their premise at   *)
(*  [(β ~ tvar) ++ Θ] (so a guess below the binder cannot generate β and   *)
(*  be captured by the [close]), so every wf-preservation proof over the   *)
(*  solve gets its IH conclusion at a context CARRYING β and has to        *)
(*  strengthen back before re-closing.                                    *)
(*                                                                        *)
(*  ⚠️ THE NAIVE STATEMENT IS FALSE.  [a_wf_pskl__tophole] runs the body at *)
(*  the EMPTY Δ, so inside a ∀◇ a variable can be justified ONLY by the    *)
(*  context — and dropping β breaks exactly those.  Witness: [∀◇(β→β)] is  *)
(*  wf at [(β ~ tvar)] for any Δ, and at [nil] for none.                   *)
(*                                                                        *)
(*  So the side condition is [β ∉ pskl_shielded_ftv P] — β does not occur  *)
(*  UNDER a ∀◇ — which is the same "∀◇ bodies are CLOSED" discipline the   *)
(*  paper states in prose and [pskl_top_guarded] elsewhere renders.  Two   *)
(*  inductions: the ∀◇ case cannot use the main IH (its Δ is ∅, so         *)
(*  [β ∈ Δ] is unavailable) and instead calls the β-absent lemma below.    *)
(* ===================================================================== *)

Lemma pskl_shielded_ftv_close_rec : forall P β k,
  pskl_shielded_ftv (close_pskl_wrt_pskl_rec k β P)
    [<=] remove β (pskl_shielded_ftv P).
Proof.
  induction P; intros β k; simpl;
    (* [var_b] shifts and [var_f] branches; neither shields anything *)
    repeat match goal with
           | |- context [ if ?e then _ else _ ] => destruct e
           end;
    simpl;
    try solve [ clear; fsetdec
              | specialize (IHP β k); clear - IHP; fsetdec
              | specialize (IHP β (S k)); clear - IHP; fsetdec
              | specialize (IHP1 β k); specialize (IHP2 β k);
                clear - IHP1 IHP2; fsetdec ].
  (* ∀◇ : the body's WHOLE ftv is shielded, and [close] removes β from it *)
  pose proof (ftvar_in_pskl_close_pskl_wrt_pskl_rec P β k) as Hcl.
  clear - Hcl. fsetdec.
Qed.

Corollary pskl_shielded_ftv_close : forall P β,
  pskl_shielded_ftv (close_pskl_wrt_pskl β P)
    [<=] remove β (pskl_shielded_ftv P).
Proof. intros. apply pskl_shielded_ftv_close_rec. Qed.

(** A ghost-free skeleton shields nothing — it has no ∀◇ to shield with. *)
Lemma pskl_ghost_free_shielded : forall P,
  pskl_ghost_free P -> pskl_shielded_ftv P [=] empty.
Proof.
  induction P; intros Hgf; simpl in *;
    try solve [ clear; fsetdec | contradiction ].
  - destruct Hgf as [Hgf1 Hgf2].
    specialize (IHP1 Hgf1); specialize (IHP2 Hgf2).
    clear - IHP1 IHP2; fsetdec.
  - exact (IHP Hgf).
Qed.

(** β ABSENT: then every rule transports, [∀◇] included. *)
Lemma a_wf_pskl_strip_tvar_absent : forall Θs Δ P,
  {{ Θs ⨟ Δ ⊢ₚₛ P }}a ->
  forall Ξ β Θ, Θs = Ξ ++ (β ~ abind_tvar) ++ Θ ->
  β `notin` ftvar_in_pskl P ->
  {{ (Ξ ++ Θ) ⨟ Δ ⊢ₚₛ P }}a.
Proof.
  intros Θs Δ P H; induction H; intros Ξ0 β Θ0 Heq Hβ; subst.
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var.
    destruct H as [HΔ | Htv]; [ left; exact HΔ | right ].
    assert (Hne : α <> β) by (simpl in Hβ; clear - Hβ; fsetdec).
    destruct Htv as [Hb | [Hb | [τ Hb]]];
      [ left | right; left | right; right; exists τ ];
      (eapply binds_mid_drop; [ exact Hb | intros Heq0; contradiction ]).
  - simpl in Hβ.
    apply a_wf_pskl__arrow;
      [ eapply IHa_wf_pskl1 | eapply IHa_wf_pskl2 ];
      solve [ reflexivity | clear - Hβ; fsetdec ].
  - (* ∀ : re-pick the cofinite bound away from β *)
    apply a_wf_pskl__all with (L := add β L). intros α Hα.
    eapply H0;
      [ clear - Hα; fsetdec | reflexivity | ].
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f α)) as Hup.
    cbn [ftvar_in_pskl] in Hup.
    assert (Hne : β `notin` singleton α) by (clear - Hα; fsetdec).
    clear - Hβ Hup Hne; fsetdec.
  - apply a_wf_pskl__hole.
  - (* ∀◇ : the body is β-absent too, so the IH applies at Δ = ∅ *)
    simpl in Hβ.
    apply a_wf_pskl__tophole; [ exact H | ].
    eapply IHa_wf_pskl; [ reflexivity | clear - Hβ; fsetdec ].
Qed.

(** β IN Δ, and NOT SHIELDED: the usable form. *)
Lemma a_wf_pskl_strip_tvar_mid : forall Θs Δ P,
  {{ Θs ⨟ Δ ⊢ₚₛ P }}a ->
  forall Ξ β Θ, Θs = Ξ ++ (β ~ abind_tvar) ++ Θ ->
  β `in` Δ ->
  β `notin` pskl_shielded_ftv P ->
  {{ (Ξ ++ Θ) ⨟ Δ ⊢ₚₛ P }}a.
Proof.
  intros Θs Δ P H; induction H; intros Ξ0 β Θ0 Heq HβΔ Hsh; subst.
  - apply a_wf_pskl__unit.
  - (* var : if it IS β, Δ carries it; otherwise the binding survives *)
    apply a_wf_pskl__var.
    destruct (α == β) as [-> | Hne]; [ left; exact HβΔ | ].
    destruct H as [HΔ | Htv]; [ left; exact HΔ | right ].
    destruct Htv as [Hb | [Hb | [τ Hb]]];
      [ left | right; left | right; right; exists τ ];
      (eapply binds_mid_drop; [ exact Hb | intros Heq0; contradiction ]).
  - simpl in Hsh.
    apply a_wf_pskl__arrow;
      [ eapply IHa_wf_pskl1 | eapply IHa_wf_pskl2 ];
      solve [ reflexivity | exact HβΔ | clear - Hsh; fsetdec ].
  - (* ∀ : Δ grows, so [β ∈ Δ] survives; re-pick L away from β *)
    apply a_wf_pskl__all with (L := add β L). intros α Hα.
    eapply H0;
      [ clear - Hα; fsetdec | reflexivity | clear - HβΔ; fsetdec | ].
    pose proof (pskl_shielded_ftv_open_upper P (pskl_var_f α)) as Hup.
    cbn [ftvar_in_pskl] in Hup.
    assert (Hne : β `notin` singleton α) by (clear - Hα; fsetdec).
    simpl in Hsh. clear - Hsh Hup Hne; fsetdec.
  - apply a_wf_pskl__hole.
  - (* ⚠️ ∀◇ : Δ RESETS to ∅, so the IH is unusable — but the body is
       exactly what [pskl_shielded_ftv] measures, so β is ABSENT there *)
    apply a_wf_pskl__tophole; [ exact H | ].
    eapply a_wf_pskl_strip_tvar_absent;
      [ exact H0 | reflexivity | simpl in Hsh; exact Hsh ].
Qed.

(* ===================================================================== *)
(*  wf of [guess^TY]'s OUTPUT — at [Ξ ++ Θ], since the guess invents the   *)
(*  block [Ξ] and its result mentions it.                                 *)
(* ===================================================================== *)

(** ⭐ A WELL-FORMED SKELETON SHIELDS ONLY CONTEXT VARIABLES.  [∀◇] bodies
    are wf at the EMPTY Δ ([a_wf_pskl__tophole]), so nothing a binder
    introduced can appear under one — which is exactly the paper's prose
    "a ∀◇ is well-formed only over a CLOSED guarded body".

    This is what makes the strip usable: at a solve ∀ row the witness β is
    fresh for [Θ], so opening at β cannot put β under a ∀◇ of a WELL-FORMED
    input, hence not under one of the output either. *)
Lemma a_wf_pskl_shielded_dom : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a -> pskl_shielded_ftv P [<=] dom Θ.
Proof.
  intros Θ Δ P H; induction H; cbn [pskl_shielded_ftv];
    try solve [ clear; fsetdec | clear - IHa_wf_pskl1 IHa_wf_pskl2; fsetdec ].
  - (* ∀ : the body's shielded set only GROWS when opened, so the cofinite
       premise's bound already covers it *)
    pick fresh α for (L `union` dom Θ `union` ftvar_in_pskl P `union` Δ).
    pose proof (H0 α ltac:(clear - Fr; solve_notin_auto)) as Hb.
    pose proof (pskl_shielded_ftv_open_lower P (pskl_var_f α)) as Hlo.
    clear - Hb Hlo; fsetdec.
  - (* ∀◇ : the body is wf at the EMPTY Δ, so ALL of its ftv is in dom Θ *)
    pose proof (a_wf_pskl_ftv_dom H0) as Hd. clear - Hd; fsetdec.
Qed.

(* ⚙️ the stdlib's [app_assoc] orientation is version-dependent and its
   [rewrite] kept mis-firing here; a local, explicitly-oriented copy. *)
Lemma list_app_assoc : forall (A : Type) (X Y Z : list A),
  (X ++ Y) ++ Z = X ++ (Y ++ Z).
Proof. intros A X Y Z; induction X as [| p X IH]; simpl; f_equal; auto. Qed.

Notation aenv_app_assoc := (@list_app_assoc (atom * abind)).

Lemma a_wf_pskl_app_weaken : forall Ξ Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a -> {{ (Ξ ++ Θ) ⨟ Δ ⊢ₚₛ P }}a.
Proof.
  intros Ξ Θ Δ P H.
  eapply a_wf_pskl_weaken; [ | exact H ].
  intros x b Hb. apply binds_app_3; exact Hb.
Qed.

(* ⚙ RENAMED from [a_guess_mono_wf] 2026-08-09 (cleanup audit §8.1c): it collided with a
   DIFFERENT lemma of that name, and this one concludes a_wf_pskl of the PAINTING, not a_wf_ptyp (prop_soundness_typing.v's). *)
Lemma a_guess_mono_wf_pskl : forall Θ P Ξ A,
  a_guess_mono Θ P Ξ A ->
  forall Δ, {{ Θ ⨟ Δ ⊢ₚₛ P }}a -> {{ (Ξ ++ Θ) ⨟ Δ ⊢ₚₛ (ptyp_to_pskl A) }}a.
Proof.
  (* ⚠️ [cbn [app]] would unfold [app] to its fixpoint body and break
     [app_assoc]'s pattern in the arrow case — reduce the concrete
     appends per-case with [simpl] instead. *)
  intros Θ P Ξ A H; induction H; intros Δ Hwf; cbn [ptyp_to_pskl].
  - (* ◇ ↦ a fresh flexible, which the block declares *)
    simpl. apply a_wf_pskl__var. right. right. left.
    unfold binds; simpl; auto.
  - (* ∀◇ : the guess DROPS the universal ghost; its body is wf at ∅ *)
    destruct (a_wf_pskl_tophole_inv Hwf) as [_ Hwf0].
    apply (a_wf_pskl_delta_mono (IHa_guess_mono empty Hwf0)).
    clear; fsetdec.
  - (* var / unit : the guess is the identity *)
    simpl. exact Hwf.
  - simpl. apply a_wf_pskl__unit.
  - (* arrow : both IHs land at their OWN block, and each weakens into the
       union.  No [app_assoc] rewrite — just supply the binds monotonicity
       for [(Ξ1 ++ Ξ2) ++ Θ] directly. *)
    inversion Hwf; subst.
    apply a_wf_pskl__arrow.
    + eapply a_wf_pskl_weaken;
        [ | exact (IHa_guess_mono1 Δ ltac:(assumption)) ].
      intros x b Hb.
      destruct (binds_app_1 _ _ _ _ _ Hb) as [HbΞ | HbΘ];
        [ apply binds_app_2; apply binds_app_2; exact HbΞ
        | apply binds_app_3; exact HbΘ ].
    + eapply a_wf_pskl_weaken;
        [ | exact (IHa_guess_mono2 Δ ltac:(assumption)) ].
      intros x b Hb.
      destruct (binds_app_1 _ _ _ _ _ Hb) as [HbΞ | HbΘ];
        [ apply binds_app_2; apply binds_app_3; exact HbΞ
        | apply binds_app_3; exact HbΘ ].
  - (* ∀ : open at THIS rule's β, run the IH there, strip β, re-close *)
    assert (HβΘ : β `notin` dom Θ)
      by (pose proof (dom_subset_ftvar_in_aenv Θ) as Hd; clear - H Hd; fsetdec).
    assert (HβΞ : β `notin` dom Ξ)
      by (eapply a_guess_mono_generated_fresh_binder; exact H0).
    apply (@a_wf_pskl_all_of_one (Ξ ++ Θ) Δ
             (ptyp_to_pskl (close_ptyp_wrt_ptyp β A)) β).
    + rewrite <- ptyp_to_pskl_open.
      rewrite open_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp.
      (* the IH lives at [Ξ ++ (β ~ tvar) ++ Θ]; strip β, which is legal
         because [guess^TY]'s result is GHOST-FREE and shields nothing *)
      eapply a_wf_pskl_strip_tvar_mid;
        [ apply IHa_guess_mono;
          apply a_wf_pskl_app_weaken with (Ξ := (β ~ abind_tvar));
          apply a_wf_pskl_all_inv_at; [ exact Hwf | clear - H; fsetdec ]
        | reflexivity
        | clear; fsetdec
        | pose proof (pskl_ghost_free_shielded _
                        (ptyp_to_pskl_ghost_free A)) as He;
          clear - He; fsetdec ].
    + rewrite dom_app. clear - HβΘ HβΞ; fsetdec.
    + pose proof (ftvar_ptyp_to_pskl (close_ptyp_wrt_ptyp β A)) as Hco.
      pose proof (ftvar_in_ptyp_close_ptyp_wrt_ptyp A β) as Hcl.
      clear - Hco Hcl; fsetdec.
Qed.

(** ⭐ THE SHIELDED-ftv BOUND.  What can sit UNDER a ∀◇ in the eq-solve's
    output is bounded by what sat under a ∀◇ in its inputs, plus the block
    it generated.  (The SUB half has no such bound — SS-GhostLF builds
    [∀◇(P1' → P2')], shielding its whole output — which is why this is
    stated for the eq half alone, exactly where it is needed.)

    Its use: the three eq-∀ rows need [β ∉ pskl_shielded_ftv P'] to strip
    their own witness back off the context ([a_wf_pskl_strip_tvar_mid]), and
    the rule's own freshness gives [β ∉ ftv P ∪ ftv Q] while
    [a_solve_eq_generated_apart_binder] gives [β ∉ dom Ξ]. *)
Lemma a_solve_eq_shielded : forall Θ P P0 Ξ P',
  {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a ->
  pskl_shielded_ftv P'
    [<=] pskl_shielded_ftv P `union` pskl_shielded_ftv P0 `union` dom Ξ.
Proof.
  intros Θ P P0 Ξ P' H; induction H; cbn [pskl_shielded_ftv];
    try solve [ clear; fsetdec
              | clear - IHa_solve_eq; fsetdec
              | (* SE-FlexR : [guess^TY]'s result is ghost-free, so it
                   shields nothing *)
                match goal with
                | Hg : a_guess_mono _ _ _ ?A0 |- _ =>
                    pose proof (pskl_ghost_free_shielded _
                                  (ptyp_to_pskl_ghost_free A0)) as He;
                    clear - He; fsetdec
                end
              | (* SE-Arrow : the two blocks split *)
                rewrite dom_app;
                clear - IHa_solve_eq1 IHa_solve_eq2; fsetdec ].
  (* What is left are the rows whose subject or target is a ∀◇ — there the
     bound flips from "shielded" to the FULL ftv, because a ∀◇ shields its
     whole body — plus the three ∀-CLOSE rows. *)
  all: pose proof (pskl_shielded_ftv_sub_ftv P) as HsP;
       pose proof (pskl_shielded_ftv_sub_ftv Q) as HsQ.
  all: try solve
         [ (* SE-UnivGhost : [⫯P ∼ ⫯Q ⤳ ⫯P'] shields ALL of P', so this row
              needs the full-ftv bound, not the shielded one *)
           match goal with
           | Hd : {{ _ ⊢ₑ _ ∼ _ ⤳ _ ⨾ _ }}a |- _ =>
               pose proof (a_solve_eq_ftv Hd) as Hf; clear - Hf; fsetdec
           end
         | (* SE-GhostGuarded / SE-GuardedGhost : the ∀◇ is PEELED, so the
              IH's shielded bound only has to be relaxed to ftv on one side *)
           cbn [pskl_shielded_ftv] in IHa_solve_eq;
           clear - IHa_solve_eq HsP HsQ; fsetdec ].
  (* the three ∀-CLOSE rows, uniformly: the [close] drops β, and each
     opening costs at most β — which the [close] then removes again *)
  all: match goal with
       | |- pskl_shielded_ftv (close_pskl_wrt_pskl ?b ?p') [<=] _ =>
           pose proof (pskl_shielded_ftv_close p' b) as Hcl;
           pose proof (pskl_shielded_ftv_open_upper P (pskl_var_f b)) as HuP;
           pose proof (pskl_shielded_ftv_open_upper Q (pskl_var_f b)) as HuQ;
           cbn [ftvar_in_pskl] in HuP, HuQ;
           cbn [pskl_shielded_ftv] in IHa_solve_eq;
           clear - IHa_solve_eq Hcl HuP HuQ HsP HsQ; fsetdec
       end.
Qed.

(** wf preservation for [a_solve_eq] (Δ-uniform; a non-mutual induction —
    the eq half never calls the sub half).  Discharges the paper's
    [Θ0 ⊢ P_a] conclusion of the -var lemmas OUTSIDE their inductions.

    ⭐ THE CONCLUSION MOVED TO [Ξ ++ Θ] (2026-08-04): SE-FlexR's output is
    [guess^TY]'s, which mentions the block the guess just invented, so it is
    wf only where that block is declared.  The ∀ rows then need
    [a_wf_pskl_strip_tvar_mid] to drop their own witness back off, and its
    "not shielded" side condition comes from [a_solve_eq_shielded]. *)
Lemma a_solve_eq_wf : forall Θ P P0 Ξ P',
  {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a ->
  forall Δ,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  {{ Θ ⨟ Δ ⊢ₚₛ P0 }}a ->
  {{ (Ξ ++ Θ) ⨟ Δ ⊢ₚₛ P' }}a.
Proof.
  intros Θ P P0 Ξ P' H; induction H; intros Δ HwfP HwfQ;
    (* the rows that generate nothing: [nil ++ Θ] IS [Θ] *)
    try solve [ cbn [app]; apply a_wf_pskl__unit
              | cbn [app]; exact HwfP
              | cbn [app]; exact HwfQ ].
  - (* SE-FlexR — the one generating row *)
    eapply a_guess_mono_wf_pskl; eassumption.
  - (* SE-Arrow — the blocks split, and the second premise already ran at
       [Ξ1 ++ Θ], so its IH needs the inputs weakened there *)
    inversion HwfP; subst; inversion HwfQ; subst.
    rewrite aenv_app_assoc.
    apply a_wf_pskl__arrow.
    + eapply a_wf_pskl_weaken;
        [ | exact (IHa_solve_eq1 Δ ltac:(assumption) ltac:(assumption)) ].
      intros x b Hb.
      destruct (binds_app_1 _ _ _ _ _ Hb) as [HbΞ | HbΘ];
        [ apply binds_app_3; apply binds_app_2; exact HbΞ
        | apply binds_app_3; apply binds_app_3; exact HbΘ ].
    + apply IHa_solve_eq2;
        apply a_wf_pskl_app_weaken; assumption.
  - (* SE-Forall — exists-fresh + CLOSE.  Open both wf premises at THIS
       rule's own binder β ([a_wf_pskl_all_inv_at]), run the single IH at
       [(β ~ tvar) ++ Θ], STRIP β back off, and re-close. *)
    assert (HβΞ : β `notin` dom Ξ)
      by (eapply a_solve_eq_generated_apart_binder; eassumption).
    assert (HβΘ : β `notin` dom Θ)
      by (pose proof (dom_subset_ftvar_in_aenv Θ) as Hd; clear - H Hd; fsetdec).
    assert (Hsh : β `notin` pskl_shielded_ftv P').
    { pose proof (a_solve_eq_shielded H0) as Hb.
      (* β is fresh for Θ, and a WF input shields only [dom Θ] *)
      pose proof (a_wf_pskl_shielded_dom
                    (a_wf_pskl_all_inv_at HwfP (β := β)
                       ltac:(clear - H; solve_notin_auto))) as HsP.
      pose proof (a_wf_pskl_shielded_dom
                    (a_wf_pskl_all_inv_at HwfQ (β := β)
                       ltac:(clear - H; solve_notin_auto))) as HsQ.
      clear - Hb HsP HsQ HβΘ HβΞ. fsetdec. }
    apply (@a_wf_pskl_all_of_one (Ξ ++ Θ) Δ (close_pskl_wrt_pskl β P') β).
    + rewrite open_pskl_wrt_pskl_close_pskl_wrt_pskl.
      eapply a_wf_pskl_strip_tvar_mid;
        [ apply IHa_solve_eq;
          (apply a_wf_pskl_app_weaken with (Ξ := (β ~ abind_tvar));
           apply a_wf_pskl_all_inv_at;
             [ eassumption | clear - H; fsetdec ])
        | reflexivity
        | clear; fsetdec
        | exact Hsh ].
    + rewrite dom_app.
      pose proof (dom_subset_ftvar_in_aenv Θ) as Hd.
      clear - H Hd HβΞ; fsetdec.
    + pose proof (ftvar_in_pskl_close_pskl_wrt_pskl P' β) as Hcl.
      clear - Hcl; fsetdec.
  - (* SE-UnivGhost *)
    destruct (a_wf_pskl_tophole_inv HwfP) as [HgP HwfP0].
    destruct (a_wf_pskl_tophole_inv HwfQ) as [HgQ HwfQ0].
    apply a_wf_pskl__tophole.
    + eapply (proj2 a_solve_sub_eq_guarded);
        eauto using a_wf_pskl_lc.
    + apply IHa_solve_eq; assumption.
  - (* SE-GhostForall — as SE-Forall; the ∀◇ LHS is Δ-uniform, so it moves
       to [add β Δ] by plain Δ-monotonicity. *)
    assert (HβΞ : β `notin` dom Ξ)
      by (eapply a_solve_eq_generated_apart_binder; eassumption).
    assert (HβΘ : β `notin` dom Θ)
      by (pose proof (dom_subset_ftvar_in_aenv Θ) as Hd; clear - H Hd; fsetdec).
    assert (Hsh : β `notin` pskl_shielded_ftv P').
    { pose proof (a_solve_eq_shielded H0) as Hb.
      cbn [pskl_shielded_ftv] in Hb.
      pose proof (a_wf_pskl_shielded_dom HwfP) as HsP.
      cbn [pskl_shielded_ftv] in HsP.
      pose proof (a_wf_pskl_shielded_dom
                    (a_wf_pskl_all_inv_at HwfQ (β := β)
                       ltac:(clear - H; solve_notin_auto))) as HsQ.
      clear - Hb HsP HsQ HβΘ HβΞ. fsetdec. }
    apply (@a_wf_pskl_all_of_one (Ξ ++ Θ) Δ (close_pskl_wrt_pskl β P') β).
    + rewrite open_pskl_wrt_pskl_close_pskl_wrt_pskl.
      eapply a_wf_pskl_strip_tvar_mid;
        [ apply IHa_solve_eq;
            [ apply a_wf_pskl_app_weaken with (Ξ := (β ~ abind_tvar));
              apply (a_wf_pskl_delta_mono HwfP); clear; fsetdec
            | apply a_wf_pskl_app_weaken with (Ξ := (β ~ abind_tvar));
              apply a_wf_pskl_all_inv_at;
                [ exact HwfQ | clear - H; fsetdec ] ]
        | reflexivity
        | clear; fsetdec
        | exact Hsh ].
    + rewrite dom_app.
      pose proof (dom_subset_ftvar_in_aenv Θ) as Hd.
      clear - H Hd HβΞ; fsetdec.
    + pose proof (ftvar_in_pskl_close_pskl_wrt_pskl P' β) as Hcl.
      clear - Hcl; fsetdec.
  - (* SE-GhostGuarded *)
    destruct (a_wf_pskl_tophole_inv HwfP) as [HgP HwfP0].
    apply IHa_solve_eq;
      [ apply (a_wf_pskl_delta_mono HwfP0); clear; fsetdec | exact HwfQ ].
  - (* SE-ForallGhost — mirror of SE-GhostForall. *)
    assert (HβΞ : β `notin` dom Ξ)
      by (eapply a_solve_eq_generated_apart_binder; eassumption).
    assert (HβΘ : β `notin` dom Θ)
      by (pose proof (dom_subset_ftvar_in_aenv Θ) as Hd; clear - H Hd; fsetdec).
    assert (Hsh : β `notin` pskl_shielded_ftv P').
    { pose proof (a_solve_eq_shielded H0) as Hb.
      cbn [pskl_shielded_ftv] in Hb.
      pose proof (a_wf_pskl_shielded_dom
                    (a_wf_pskl_all_inv_at HwfP (β := β)
                       ltac:(clear - H; solve_notin_auto))) as HsP.
      pose proof (a_wf_pskl_shielded_dom HwfQ) as HsQ.
      cbn [pskl_shielded_ftv] in HsQ.
      clear - Hb HsP HsQ HβΘ HβΞ. fsetdec. }
    apply (@a_wf_pskl_all_of_one (Ξ ++ Θ) Δ (close_pskl_wrt_pskl β P') β).
    + rewrite open_pskl_wrt_pskl_close_pskl_wrt_pskl.
      eapply a_wf_pskl_strip_tvar_mid;
        [ apply IHa_solve_eq;
            [ apply a_wf_pskl_app_weaken with (Ξ := (β ~ abind_tvar));
              apply a_wf_pskl_all_inv_at;
                [ exact HwfP | clear - H; fsetdec ]
            | apply a_wf_pskl_app_weaken with (Ξ := (β ~ abind_tvar));
              apply (a_wf_pskl_delta_mono HwfQ); clear; fsetdec ]
        | reflexivity
        | clear; fsetdec
        | exact Hsh ].
    + rewrite dom_app.
      pose proof (dom_subset_ftvar_in_aenv Θ) as Hd.
      clear - H Hd HβΞ; fsetdec.
    + pose proof (ftvar_in_pskl_close_pskl_wrt_pskl P' β) as Hcl.
      clear - Hcl; fsetdec.
  - (* SE-GuardedGhost *)
    destruct (a_wf_pskl_tophole_inv HwfQ) as [HgQ HwfQ0].
    apply IHa_solve_eq;
      [ exact HwfP
      | apply (a_wf_pskl_delta_mono HwfQ0); clear; fsetdec ].
Qed.

(* ===================================================================== *)
(*  P6-Cv induction support: the reusable leaf-disjunct closer, painting   *)
(*  inversions, and the refinement→precision bridges.                      *)
(* ===================================================================== *)

Lemma pskl_to_bskl_inh_arrow_inv : forall P Q1 Q2,
  pskl_to_bskl_inh P = bskl_arrow Q1 Q2 ->
  exists P1 P2, P = pskl_arrow P1 P2 /\
    pskl_to_bskl_inh P1 = Q1 /\ pskl_to_bskl_inh P2 = Q2.
Proof.
  intros P Q1 Q2 H; destruct P; simpl in H; try discriminate.
  inversion H; subst. exists P1, P2; repeat split; reflexivity.
Qed.

(** Refinement→precision bridge for the [unit] target.  An inherited
    painting that refines to [bskl_unit] is precise to [uskl_unit]; the
    induction follows [flex_l] definition chains and strips ∀◇ via
    [tophole_remove].  Discharges the [Pi = □] and ∀◇-[P0] subcases of the
    Unit consistency case (conclusion: [msubst κ P0 ⊑ᵖ[∅] unit]). *)
Lemma ad_refine_inh_unit_ppre : forall Θ Δr Qlhs Qrhs,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δr ⊢ᵣ Qlhs ⊳ Qrhs }}ad ->
  Qrhs = bskl_unit ->
  forall P' Δ, Qlhs = pskl_to_bskl_inh P' ->
  {{ Θ ⨟ Δ ⊢ˢ P' ⊑ᵖ[ empty ] uskl_unit }}ad.
Proof.
  intros Θ Δr Qlhs Qrhs Hwf H; induction H; intros HR P' Δo Heq;
    try discriminate HR; subst.
  - (* unit *)
    destruct P'; simpl in Heq; try discriminate Heq.
    apply ad_ppre__unit. fsetdec.
  - (* hole: Qrhs = pskl_to_bskl_syn P, forced = unit *)
    destruct P'; simpl in Heq; try discriminate Heq.
    apply ad_ppre__hole; [ fsetdec | simpl; fsetdec ].
  - (* tophole_remove *)
    destruct P'; simpl in Heq; try discriminate Heq.
    inversion Heq; subst.
    apply ad_ppre__tophole_remove. eapply IHad_refine_syn; eauto.
  - (* flex_l *)
    destruct P'; simpl in Heq; try discriminate Heq.
    inversion Heq; subst.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    eapply ad_ppre__flex_l; [ eassumption | ].
    apply (IHad_refine_syn Hwf eq_refl (ptyp_to_pskl τ) Δo).
    symmetry. apply ptyp_to_bskl_inh_syn_eq; assumption.
Qed.

(* ---- a_inc / refinement facts for the P0 = variable subcases ---- *)

Lemma msubst_pskl_tvar_id : forall Θ0 κ Θ α,
  {{ ⊢ Θ0 }}a ->
  κ ∷ Θ0 ⊑ Θ ->
  binds α abind_tvar Θ0 ->
  msubst_pskl κ (pskl_var_f α) = pskl_var_f α.
Proof.
  intros Θ0 κ Θ α Hwf Hinc Hb.
  simpl. rewrite msubst_lookup_notin; [ reflexivity | ].
  intros Hin. pose proof (a_inc_dom_flex Hinc Hin) as Hfl.
  pose proof (a_wf_aenv_uniq Hwf) as Huniq.
  destruct Hfl as [Hbf | [τ Hbf]];
    pose proof (binds_unique _ _ _ _ _ Hb Hbf Huniq) as Hc; discriminate Hc.
Qed.

(** A rigid variable cannot refine into [unit] (only [flex_l] could fire,
    but its [α] would be a defined flexible, clashing with rigidity).  Used
    to discharge the P0 = rigid-variable subcase of the Unit case. *)
Lemma ad_refine_syn_rigid_var_unit_absurd : forall Θ Δ α,
  {{ ⊢ Θ }}a ->
  binds α abind_tvar Θ ->
  {{ Θ ⨟ Δ ⊢ᵣ (bskl_var_f α) ⊳ bskl_unit }}ad ->
  False.
Proof.
  intros Θ Δ α Hwf Hb H; inversion H; subst;
    match goal with
    | Hbd : binds _ (abind_flex_mono_def _) _ |- _ =>
        pose proof (binds_unique _ _ _ _ _ Hb Hbd (a_wf_aenv_uniq Hwf)) as Hc;
        discriminate Hc
    end.
Qed.

(* ---- the Unit consistency case, as a standalone size-induction lemma ---- *)
(*    P0 wf at empty Δ (paper's Θ0 ⊢ P0); Pi carries the binder ctx Δ.       *)
(* Precision into the unit target carries no tags. *)
Lemma ad_ppre_unit_tags_empty : forall Θ Δ P Ψ,
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] uskl_unit }}ad -> Ψ [=] empty.
Proof.
  intros Θ Δ P Ψ H; remember uskl_unit as u eqn:Hu.
  induction H; try discriminate Hu; subst; auto.
Qed.

(* ==== the Unit consistency case, as a standalone lemma ==== *)
(* P0 is well-formed at empty Δ (the paper's [Θ0 ⊢ P0]); Pi carries the
   binder context Δ.  Strong induction on [size Pi + size P0] so the ∀◇
   stripping (Pi and P0 sides) recurses. *)
Lemma a_solve_eq_unit : forall n Θ0 Θ κ Δ Ψi Pi P0,
  size_pskl Pi + size_pskl P0 <= n ->
  {{ ⊢ Θ }}a -> {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a -> {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  κ ∷ Θ0 ⊑ Θ ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] uskl_unit }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ bskl_unit }}ad ->
  exists Pa, {{ Θ0 ⊢ₑ Pi ∼ P0 ⤳ nil ⨾ Pa }}a /\
             {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pa) ⊑ᵖ[ Ψi ] uskl_unit }}ad.
Proof.
  induction n; intros Θ0 Θ κ Δ Ψi Pi P0 Hn
    HwfΘ HwfΘ0 HwfPi HwfP0 Hκ Hpre Hrefine.
  { pose proof (size_pskl_min Pi); pose proof (size_pskl_min P0); lia. }
  pose proof (ad_ppre_unit_tags_empty Hpre) as HΨi.
  destruct Pi as [ | nb | α | Pi1 Pi2 | Pib | | Pi' ].
  - (* Pi = unit *)
    destruct P0 as [ | nb0 | α | P0a P0b | P0b | | P0' ].
    + (* P0 = unit : SE-Unit *)
      exists pskl_unit; split;
        [ apply a_solve_eq__unit | simpl; apply ad_ppre__unit; exact HΨi ].
    + (* P0 = var_b : not wf *) inversion HwfP0.
    + (* P0 = var_f α : 3-way *)
      inversion HwfP0; subst;
      match goal with H : _ \/ a_binds_tvar α _ |- _ =>
        destruct H as [Hemp | Habt] end; [ clear - Hemp; fsetdec | ].
      destruct Habt as [Hrig | [Hfm | [τ Hfd]]].
      * (* rigid : refinement absurd *)
        exfalso.
        assert (Hmid : msubst_pskl κ (pskl_var_f α) = pskl_var_f α)
          by (eapply msubst_pskl_tvar_id; eauto).
        rewrite Hmid in Hrefine; simpl in Hrefine.
        eapply ad_refine_syn_rigid_var_unit_absurd;
          [ exact HwfΘ | eapply a_inc_binds_tvar; eauto | exact Hrefine ].
      (* ⭐ BOTH FLEXIBLE CASES CHANGED (2026-08-04).  The repaired SE-FlexR
         returns [guess^TY(P_i)], not the flexible — and here the subject is
         [unit], whose guess is [(·; unit)].  So the witness is [unit], the
         block is empty, and the precision obligation collapses from "the
         flexible is precise into unit" to [ad_ppre__unit].  This is the
         repair paying for itself: the old witness needed the whole
         [ad_refine_inh_unit_ppre] detour through the refinement. *)
      * (* undefined flex : SE-FlexR *)
        exists pskl_unit; split.
        -- apply a_solve_eq__flex_r with (A := ptyp_unit);
             [ left; exact Hfm
             | split; [ constructor | intros Hf; inversion Hf ]
             | apply nonghost_pskl__unit
             | apply a_guess_mono__unit ].
        -- simpl. apply ad_ppre__unit. exact HΨi.
      * (* defined flex : SE-FlexR *)
        exists pskl_unit; split.
        -- apply a_solve_eq__flex_r with (A := ptyp_unit);
             [ right; exists τ; exact Hfd
             | split; [ constructor | intros Hf; inversion Hf ]
             | apply nonghost_pskl__unit
             | apply a_guess_mono__unit ].
        -- simpl. apply ad_ppre__unit. exact HΨi.
    + (* P0 = arrow : refinement absurd *)
      simpl in Hrefine; inversion Hrefine.
    + (* P0 = all_syn : refinement absurd *)
      simpl in Hrefine; inversion Hrefine.
    + (* P0 = hole : SE-VacuousR *)
      exists pskl_unit; split; [ apply a_solve_eq__hole_r | exact Hpre ].
    + (* P0 = tophole P0' : SE-GuardedGhost (unit guarded), recurse (unit,P0') *)
      simpl in Hrefine. inversion Hrefine; subst.
      inversion HwfP0; subst.
      match goal with
      | Href' : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ P0') ⊳ bskl_unit }}ad,
        HwfP0' : {{ _ ⨟ _ ⊢ₚₛ P0' }}a |- _ =>
        destruct (IHn Θ0 Θ κ Δ Ψi pskl_unit P0'
                    ltac:(simpl in Hn; simpl; lia)
                    HwfΘ HwfΘ0 HwfPi HwfP0' Hκ Hpre Href')
          as [Pa [Hsolve Hprec]]
      end.
      exists Pa; split;
        [ apply a_solve_eq__tophole_r_guarded; [ constructor | exact Hsolve ]
        | exact Hprec ].
  - (* Pi = var_b : not wf *) inversion HwfPi.
  - (* Pi = var_f α : SE-Var *)
    exists (pskl_var_f α); split; [ apply a_solve_eq__var | exact Hpre ].
  - (* Pi = arrow : precision absurd *) simpl in Hpre; inversion Hpre.
  - (* Pi = all_syn : precision absurd *) simpl in Hpre; inversion Hpre.
  - (* Pi = hole : SE-GhostL, Pa := P0 *)
    exists P0; split;
      [ apply a_solve_eq__hole_l
      | eapply ad_partial_precise_psi_cong;
          [ eapply ad_refine_inh_unit_ppre;
              [ exact HwfΘ | exact Hrefine | reflexivity | reflexivity ]
          | clear - HΨi; fsetdec ] ].
  - (* Pi = tophole Pi' *)
    simpl in Hpre. inversion Hpre; subst.
    inversion HwfPi; subst.
    destruct P0 as [ | nb0 | α | P0a P0b | P0b | | P0' ].
    + (* P0 = unit : GhostGuarded, recurse (Pi',unit) *)
      match goal with
      | Hpre' : {{ _ ⨟ _ ⊢ˢ msubst_pskl κ Pi' ⊑ᵖ[ _ ] uskl_unit }}ad,
        HwfPi' : {{ _ ⨟ _ ⊢ₚₛ Pi' }}a |- _ =>
        destruct (IHn Θ0 Θ κ Δ Ψi Pi' pskl_unit
                    ltac:(simpl in Hn; simpl; lia)
                    HwfΘ HwfΘ0 HwfPi' HwfP0 Hκ Hpre' Hrefine)
          as [Pa [Hsolve Hprec]]
      end.
      exists Pa; split;
        [ apply a_solve_eq__tophole_l_guarded; [ constructor | exact Hsolve ]
        | exact Hprec ].
    + (* P0 = var_b *) inversion HwfP0.
    + (* P0 = var_f α : GhostGuarded (var guarded), recurse (Pi', var α) *)
      match goal with
      | Hpre' : {{ _ ⨟ _ ⊢ˢ msubst_pskl κ Pi' ⊑ᵖ[ _ ] uskl_unit }}ad,
        HwfPi' : {{ _ ⨟ _ ⊢ₚₛ Pi' }}a |- _ =>
        destruct (IHn Θ0 Θ κ Δ Ψi Pi' (pskl_var_f α)
                    ltac:(simpl in Hn; simpl; lia)
                    HwfΘ HwfΘ0 HwfPi' HwfP0 Hκ Hpre' Hrefine)
          as [Pa [Hsolve Hprec]]
      end.
      exists Pa; split;
        [ apply a_solve_eq__tophole_l_guarded; [ constructor | exact Hsolve ]
        | exact Hprec ].
    + (* P0 = arrow : refinement absurd *) simpl in Hrefine; inversion Hrefine.
    + (* P0 = all_syn : refinement absurd *) simpl in Hrefine; inversion Hrefine.
    + (* P0 = hole : SE-VacuousR, Pa := tophole Pi' *)
      exists (pskl_tophole Pi'); split; [ apply a_solve_eq__hole_r | exact Hpre ].
    + (* P0 = tophole P0' : SE-UnivGhost, recurse (Pi', P0') *)
      simpl in Hrefine. inversion Hrefine; subst.
      inversion HwfP0; subst.
      match goal with
      | Hpre' : {{ _ ⨟ _ ⊢ˢ msubst_pskl κ Pi' ⊑ᵖ[ _ ] uskl_unit }}ad,
        Href' : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ P0') ⊳ bskl_unit }}ad,
        HwfPi' : {{ _ ⨟ _ ⊢ₚₛ Pi' }}a,
        HwfP0' : {{ _ ⨟ _ ⊢ₚₛ P0' }}a |- _ =>
        destruct (IHn Θ0 Θ κ Δ Ψi Pi' P0'
                    ltac:(simpl in Hn; simpl; lia)
                    HwfΘ HwfΘ0 HwfPi' HwfP0' Hκ Hpre' Href')
          as [Pa [Hsolve Hprec]]
      end.
      exists (pskl_tophole Pa); split;
        [ apply a_solve_eq__tophole_both; exact Hsolve
        | simpl; apply ad_ppre__tophole_remove; exact Hprec ].
Qed.

(* ===================================================================== *)
(*  P6-Cv Var case — kit (Phase 1): mono-paint computations/inversions,   *)
(*  definition chains, mono-paint reflexivity, and the defined-flex        *)
(*  TARGET-unfold transports for precision and refinement.                 *)
(* ===================================================================== *)

(* ---- mono-paint shape inversions (uskl side) ---- *)

Lemma ptyp_to_uskl_syn_unit_inv : forall τ,
  ptyp_to_uskl_syn τ = uskl_unit -> τ = ptyp_unit.
Proof. intros τ H; destruct τ; simpl in H; try discriminate; reflexivity. Qed.

Lemma ptyp_to_uskl_syn_var_inv : forall τ α,
  ptyp_to_uskl_syn τ = uskl_var_f α -> τ = ptyp_var_f α.
Proof.
  intros τ α H; destruct τ; simpl in H; try discriminate.
  inversion H; reflexivity.
Qed.

Lemma ptyp_to_uskl_syn_arrow_inv : forall τ ψ1 ψ2,
  ptyp_to_uskl_syn τ = uskl_arrow ψ1 ψ2 ->
  exists τ1 τ2, τ = ptyp_arrow τ1 τ2 /\
    ψ1 = ptyp_to_uskl_syn τ1 /\ ψ2 = ptyp_to_uskl_syn τ2.
Proof.
  intros τ ψ1 ψ2 H; destruct τ; simpl in H; try discriminate.
  inversion H; subst. exists τ1, τ2; repeat split; reflexivity.
Qed.

Lemma ptyp_to_uskl_syn_all_tag_absurd : forall τ ε ψ,
  ptyp_to_uskl_syn τ = uskl_all_tag ε ψ -> False.
Proof. intros τ ε ψ H; destruct τ; simpl in H; discriminate. Qed.

Lemma ptyp_to_uskl_syn_topholeg_absurd : forall τ ψ,
  ptyp_to_uskl_syn τ = uskl_topholeg ψ -> False.
Proof. intros τ ψ H; destruct τ; simpl in H; discriminate. Qed.

(* ---- mono-paint shape inversions (bskl side) ---- *)

Lemma ptyp_to_bskl_syn_unit_inv : forall τ,
  ptyp_to_bskl_syn τ = bskl_unit -> τ = ptyp_unit.
Proof. intros τ H; destruct τ; simpl in H; try discriminate; reflexivity. Qed.

Lemma ptyp_to_bskl_syn_var_inv : forall τ α,
  ptyp_to_bskl_syn τ = bskl_var_f α -> τ = ptyp_var_f α.
Proof.
  intros τ α H; destruct τ; simpl in H; try discriminate.
  inversion H; reflexivity.
Qed.

Lemma ptyp_to_bskl_syn_arrow_inv : forall τ Q1 Q2,
  ptyp_to_bskl_syn τ = bskl_arrow Q1 Q2 ->
  exists τ1 τ2, τ = ptyp_arrow τ1 τ2 /\
    Q1 = ptyp_to_bskl_syn τ1 /\ Q2 = ptyp_to_bskl_syn τ2.
Proof.
  intros τ Q1 Q2 H; destruct τ; simpl in H; try discriminate.
  inversion H; subst. exists τ1, τ2; repeat split; reflexivity.
Qed.

Lemma ptyp_to_bskl_syn_all_inh_absurd : forall τ Q,
  ptyp_to_bskl_syn τ = bskl_all_inh Q -> False.
Proof. intros τ Q H; destruct τ; simpl in H; discriminate. Qed.

Lemma ptyp_to_bskl_syn_all_syn_mono_absurd : forall τ Q,
  mono_ptyp τ ->
  ptyp_to_bskl_syn τ = bskl_all_syn Q -> False.
Proof.
  intros τ Q Hm H; destruct τ; simpl in H; try discriminate.
  inversion Hm.
Qed.

Lemma ptyp_to_bskl_syn_tophole_absurd : forall τ Q,
  ptyp_to_bskl_syn τ = bskl_tophole Q -> False.
Proof. intros τ Q H; destruct τ; simpl in H; discriminate. Qed.

Lemma ptyp_to_bskl_syn_hole_absurd : forall τ,
  ptyp_to_bskl_syn τ = bskl_hole -> False.
Proof. intros τ H; destruct τ; simpl in H; discriminate. Qed.

(* ---- κ-image monotypes ---- *)

(** Its companion: a FLEXIBLE's image is SCOPED BY THE TARGET.  ([a_inc]'s
    two flex rows carry [a_wf_ptyp Θ' τ] as a premise; the flexibility is what
    guarantees one of those rows is where the lookup lands.)  The
    [a_binds_tvar] form is prop_compose.v's [a_inc_lookup_wf], which this file
    does not import. *)
Lemma a_inc_lookup_flex_ftv_dom : forall Θ0 κ Θ α,
  κ ∷ Θ0 ⊑ Θ ->
  a_flex_tvar Θ0 α ->
  ftvar_in_ptyp (msubst_lookup κ α) [<=] dom Θ.
Proof.
  intros Θ0 κ Θ α Hinc; induction Hinc; intros Hf; simpl in *.
  - destruct Hf as [Hb | (τx & Hb)]; inversion Hb.
  - destruct (α == α0) as [-> | Hne];
      [ eapply a_wf_ptyp_ftv_dom; eassumption | ].
    apply IHHinc.
    destruct Hf as [Hb | (τx & Hb)];
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq _] | Hb'];
      solve [ exfalso; apply Hne; exact Heq
            | left; exact Hb' | right; exists τx; exact Hb' ].
  - destruct (α == α0) as [-> | Hne];
      [ eapply a_wf_ptyp_ftv_dom; eassumption | ].
    apply IHHinc.
    destruct Hf as [Hb | (τx & Hb)];
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq _] | Hb'];
      solve [ exfalso; apply Hne; exact Heq
            | left; exact Hb' | right; exists τx; exact Hb' ].
  - (* var / var_skl / tvar: the entry is not flexible, and the target grows *)
    assert (Hf' : a_flex_tvar Θ α)
      by (destruct Hf as [Hb | (τx & Hb)];
          destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
          solve [ discriminate Hc | left; exact Hb' | right; exists τx; exact Hb' ]).
    pose proof (IHHinc Hf') as Hd.
    assert (Hdom : dom Θ' [<=] dom (Ξ ++ (x ~ abind_var_typ A') ++ Θ'))
      by (repeat rewrite dom_app; clear; simpl; fsetdec).
    clear - Hd Hdom; fsetdec.
  - assert (Hf' : a_flex_tvar Θ α)
      by (destruct Hf as [Hb | (τx & Hb)];
          destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
          solve [ discriminate Hc | left; exact Hb' | right; exists τx; exact Hb' ]).
    pose proof (IHHinc Hf') as Hd.
    assert (Hdom : dom Θ' [<=] dom (Ξ ++ (x ~ abind_var_skl P') ++ Θ'))
      by (repeat rewrite dom_app; clear; simpl; fsetdec).
    clear - Hd Hdom; fsetdec.
  - assert (Hf' : a_flex_tvar Θ α)
      by (destruct Hf as [Hb | (τx & Hb)];
          destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
          solve [ discriminate Hc | left; exact Hb' | right; exists τx; exact Hb' ]).
    pose proof (IHHinc Hf') as Hd.
    assert (Hdom : dom Θ' [<=] dom (Ξ ++ (α0 ~ abind_tvar) ++ Θ'))
      by (repeat rewrite dom_app; clear; simpl; fsetdec).
    clear - Hd Hdom; fsetdec.
Qed.

(* ---- pointwise disjointness to set-level inter emptiness ---- *)

(* ---- the Δ-vs-definitions freshness side condition (the paper's
   implicit wf of the Δ-extended context: Δ's binders postdate every
   definition image in Θ).  See DESIGN §6(h)/WF-SIDE-CONDITIONS. ---- *)

Definition delta_def_fresh (Δ : atoms) (Θ : aenv) : Prop :=
  forall β α τ, β `in` Δ ->
    binds α (abind_flex_mono_def τ) Θ ->
    β `notin` ftvar_in_ptyp τ.

(* ---- definition chains (target-side flex unfolding) ---- *)

Inductive a_def_chain (Θ : aenv) : ptyp -> ptyp -> Prop :=
| a_def_chain_refl : forall τ, a_def_chain Θ τ τ
| a_def_chain_step : forall α τd τe,
    binds α (abind_flex_mono_def τd) Θ ->
    a_def_chain Θ τd τe ->
    a_def_chain Θ (ptyp_var_f α) τe.

Lemma a_def_chain_trans : forall Θ τ1 τ2 τ3,
  a_def_chain Θ τ1 τ2 ->
  a_def_chain Θ τ2 τ3 ->
  a_def_chain Θ τ1 τ3.
Proof.
  intros Θ τ1 τ2 τ3 H1; revert τ3; induction H1; intros τ3 H2; auto.
  eapply a_def_chain_step; eauto.
Qed.

(* ---- mono paints are well-formed skeletons / reflexively precise ---- *)

Lemma mono_ptyp_wf_to_pskl_wf : forall τ Θ,
  a_wf_ptyp Θ τ -> mono_ptyp τ ->
  forall Δ, {{ Θ ⨟ Δ ⊢ₚₛ (ptyp_to_pskl τ) }}a.
Proof.
  intros τ Θ Hwf Hm; revert Hwf; induction Hm; intros Hwf Δ; simpl.
  - apply a_wf_pskl__unit.
  - inversion Hwf; subst. apply a_wf_pskl__var; auto.
  - inversion Hwf; subst. apply a_wf_pskl__arrow; auto.
Qed.

Lemma ad_ppre_mono_paint_refl : forall τ Θ Δ,
  a_wf_ptyp Θ τ -> mono_ptyp τ ->
  {{ Θ ⨟ Δ ⊢ˢ (ptyp_to_pskl τ) ⊑ᵖ[ empty ] (ptyp_to_uskl_syn τ) }}ad.
Proof.
  intros τ Θ Δ Hwf Hm; revert Hwf; induction Hm; intros Hwf; simpl.
  - apply ad_ppre__unit. clear; fsetdec.
  - inversion Hwf; subst.
    apply ad_ppre__var; [ clear; fsetdec | auto ].
  - inversion Hwf; subst.
    apply ad_ppre__arrow with (Ψ1 := empty) (Ψ2 := empty); auto.
    clear; fsetdec.
Qed.

Lemma ad_refine_mono_paint_refl : forall τ Θ Δr,
  a_wf_ptyp Θ τ -> mono_ptyp τ ->
  {{ Θ ⨟ Δr ⊢ᵣ (ptyp_to_bskl_syn τ) ⊳ (ptyp_to_bskl_syn τ) }}ad.
Proof.
  intros τ Θ Δr Hwf Hm; revert Hwf; induction Hm; intros Hwf; simpl.
  - apply ad_refine_syn__unit.
  - inversion Hwf; subst. apply ad_refine_syn__var; auto.
  - inversion Hwf; subst. apply ad_refine_syn__arrow; auto.
Qed.

(* ---- precision into a mono paint carries no tags ---- *)

Lemma ad_ppre_mono_tags_empty : forall Θ Δ P ψ Ψ,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  forall τ, ψ = ptyp_to_uskl_syn τ -> mono_ptyp τ ->
  Ψ [=] empty.
Proof.
  intros Θ Δ P ψ Ψ HwfΘ H; induction H; intros τu Hequ Hmu.
  - (* unit *) assumption.
  - (* var *) assumption.
  - (* arrow *)
    symmetry in Hequ.
    destruct (ptyp_to_uskl_syn_arrow_inv _ Hequ)
      as (τ1 & τ2 & -> & Heq1 & Heq2).
    assert (Hm1 : mono_ptyp τ1) by (inversion Hmu; assumption).
    assert (Hm2 : mono_ptyp τ2) by (inversion Hmu; assumption).
    pose proof (IHad_partial_precise1 HwfΘ τ1 Heq1 Hm1) as He1.
    pose proof (IHad_partial_precise2 HwfΘ τ2 Heq2 Hm2) as He2.
    clear - H1 He1 He2; fsetdec.
  - (* forall: target all_tag, never a mono paint *)
    exfalso; eapply ptyp_to_uskl_syn_all_tag_absurd; symmetry; exact Hequ.
  - (* hole *) assumption.
  - (* tophole_remove *)
    eapply IHad_partial_precise; eauto.
  - (* tophole_fill: target all_tag *)
    exfalso; eapply ptyp_to_uskl_syn_all_tag_absurd; symmetry; exact Hequ.
  - (* tophole_keep: target topholeg *)
    exfalso; eapply ptyp_to_uskl_syn_topholeg_absurd; symmetry; exact Hequ.
  - (* flex_l *)
    eapply IHad_partial_precise; eauto.
  - (* flex_r: target var α, unfold the definition *)
    symmetry in Hequ.
    apply ptyp_to_uskl_syn_var_inv in Hequ; subst.
    eapply IHad_partial_precise;
      [ exact HwfΘ | reflexivity | eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

(* ---- defined-flex TARGET unfolding: precision ---- *)

Lemma ad_ppre_flexdef_target_unfold : forall Θ Δ Ψ P ψ,
  {{ ⊢ Θ }}a ->
  delta_def_fresh Δ Θ ->
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  forall α τd, ψ = uskl_var_f α ->
  binds α (abind_flex_mono_def τd) Θ ->
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τd) }}ad.
Proof.
  intros Θ Δ Ψ P ψ HwfΘ Hdf H; induction H; intros α0 τd Heq Hbd;
    try discriminate Heq.
  - (* var: subject IS the target var — go through the definition *)
    inversion Heq; subst.
    eapply ad_ppre__flex_l; [ exact Hbd | ].
    eapply ad_partial_precise_psi_cong;
      [ apply ad_ppre_mono_paint_refl;
          [ eapply a_wf_aenv_binds_def_wf; eauto
          | eapply a_wf_aenv_binds_def_mono; eauto ]
      | clear - H; fsetdec ].
  - (* hole *)
    apply ad_ppre__hole; [ assumption | ].
    rewrite ftvar_ptyp_to_uskl_syn.
    apply inter_empty_pointwise.
    intros y Hy. eapply Hdf; eauto.
  - (* tophole_remove *)
    apply ad_ppre__tophole_remove. eauto.
  - (* flex_l *)
    eapply ad_ppre__flex_l; eauto.
  - (* flex_r: same definition by uniqueness *)
    inversion Heq; subst.
    pose proof (binds_unique _ _ _ _ _ H Hbd (a_wf_aenv_uniq HwfΘ)) as Hc.
    inversion Hc; subst. assumption.
Qed.

(* ---- defined-flex TARGET unfolding: refinement ---- *)

Lemma ad_refine_flexdef_target_unfold : forall Θ Δr Q' Q,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δr ⊢ᵣ Q' ⊳ Q }}ad ->
  forall α τd, Q = bskl_var_f α ->
  binds α (abind_flex_mono_def τd) Θ ->
  {{ Θ ⨟ Δr ⊢ᵣ Q' ⊳ (ptyp_to_bskl_syn τd) }}ad.
Proof.
  intros Θ Δr Q' Q HwfΘ H; induction H; intros α0 τd Heq Hbd;
    try discriminate Heq.
  - (* var: subject IS the target var *)
    inversion Heq; subst.
    eapply ad_refine_syn__flex_l; [ exact Hbd | ].
    apply ad_refine_mono_paint_refl;
      [ eapply a_wf_aenv_binds_def_wf; eauto
      | eapply a_wf_aenv_binds_def_mono; eauto ].
  - (* hole: rebuild at the definition's paint *)
    destruct P; simpl in Heq; try discriminate Heq.
    unfold ptyp_to_bskl_syn.
    apply ad_refine_syn__hole.
    apply mono_ptyp_wf_to_pskl_wf;
      [ eapply a_wf_aenv_binds_def_wf; eauto
      | eapply a_wf_aenv_binds_def_mono; eauto ].
  - (* tophole_remove *)
    apply ad_refine_syn__tophole_remove. eauto.
  - (* flex_l *)
    eapply ad_refine_syn__flex_l; eauto.
  - (* flex_r: same definition by uniqueness *)
    inversion Heq; subst.
    pose proof (binds_unique _ _ _ _ _ H Hbd (a_wf_aenv_uniq HwfΘ)) as Hc.
    inversion Hc; subst. assumption.
Qed.

(* ---- chain transports ---- *)

Lemma ad_ppre_chain_unfold : forall Θ τ τe,
  a_def_chain Θ τ τe ->
  {{ ⊢ Θ }}a ->
  forall Δ Ψ P,
  delta_def_fresh Δ Θ ->
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τ) }}ad ->
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τe) }}ad.
Proof.
  intros Θ τ τe Hc; induction Hc; intros HwfΘ Δ Ψ P Hdf Hpre; auto.
  apply IHHc; auto.
  eapply ad_ppre_flexdef_target_unfold;
    [ exact HwfΘ | exact Hdf | exact Hpre | reflexivity | exact H ].
Qed.

Lemma ad_ppre_chain_fold : forall Θ τ τe,
  a_def_chain Θ τ τe ->
  forall Δ Ψ P,
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τe) }}ad ->
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τ) }}ad.
Proof.
  intros Θ τ τe Hc; induction Hc; intros Δ Ψ P Hpre; auto.
  simpl. eapply ad_ppre__flex_r; eauto.
Qed.

Lemma ad_refine_chain_unfold : forall Θ τ τe,
  a_def_chain Θ τ τe ->
  {{ ⊢ Θ }}a ->
  forall Δr Q,
  {{ Θ ⨟ Δr ⊢ᵣ Q ⊳ (ptyp_to_bskl_syn τ) }}ad ->
  {{ Θ ⨟ Δr ⊢ᵣ Q ⊳ (ptyp_to_bskl_syn τe) }}ad.
Proof.
  intros Θ τ τe Hc; induction Hc; intros HwfΘ Δr Q Href; auto.
  apply IHHc; auto.
  eapply ad_refine_flexdef_target_unfold;
    [ exact HwfΘ | exact Href | reflexivity | exact H ].
Qed.

(* ===================================================================== *)
(*  Phase 2: chain-based shape inversions.  A subject shape meets a mono  *)
(*  paint target only after the target's defined-flex chain is unfolded;  *)
(*  each inversion returns the chain together with the residual premise.  *)
(* ===================================================================== *)

Lemma ad_ppre_unit_subject_chain_inv : forall Θ Δ Ψ P ψ,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  P = pskl_unit ->
  forall τ, ψ = ptyp_to_uskl_syn τ -> mono_ptyp τ ->
  a_def_chain Θ τ ptyp_unit /\ Ψ [=] empty.
Proof.
  intros Θ Δ Ψ P ψ HwfΘ H; induction H; intros HeqS τu Hequ Hmu;
    try discriminate HeqS.
  - (* unit *)
    symmetry in Hequ. apply ptyp_to_uskl_syn_unit_inv in Hequ; subst.
    split; [ apply a_def_chain_refl | assumption ].
  - (* flex_r *)
    symmetry in Hequ. apply ptyp_to_uskl_syn_var_inv in Hequ; subst.
    assert (Hmd : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    destruct (IHad_partial_precise HwfΘ eq_refl τ eq_refl Hmd) as [Hc HΨ].
    split; [ eapply a_def_chain_step; eauto | assumption ].
Qed.

Lemma ad_ppre_arrow_subject_chain_inv : forall Θ Δ Ψ P ψ,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  forall P1 P2, P = pskl_arrow P1 P2 ->
  forall τ, ψ = ptyp_to_uskl_syn τ -> mono_ptyp τ ->
  exists τ1 τ2 Ψ1 Ψ2,
    a_def_chain Θ τ (ptyp_arrow τ1 τ2) /\
    mono_ptyp τ1 /\ mono_ptyp τ2 /\
    {{ Θ ⨟ Δ ⊢ˢ P1 ⊑ᵖ[ Ψ1 ] (ptyp_to_uskl_syn τ1) }}ad /\
    {{ Θ ⨟ Δ ⊢ˢ P2 ⊑ᵖ[ Ψ2 ] (ptyp_to_uskl_syn τ2) }}ad /\
    Ψ [=] Ψ1 `union` Ψ2.
Proof.
  intros Θ Δ Ψ P ψ HwfΘ H; induction H; intros S1' S2' HeqS τu Hequ Hmu;
    try discriminate HeqS.
  - (* arrow *)
    inversion HeqS; subst.
    symmetry in Hequ.
    destruct (ptyp_to_uskl_syn_arrow_inv _ Hequ)
      as (τ1 & τ2 & -> & Heq1 & Heq2).
    subst.
    assert (Hm1 : mono_ptyp τ1) by (inversion Hmu; assumption).
    assert (Hm2 : mono_ptyp τ2) by (inversion Hmu; assumption).
    exists τ1, τ2, Ψ1, Ψ2.
    repeat (split; [ solve [ apply a_def_chain_refl | assumption ] | ]).
    assumption.
  - (* flex_r *)
    symmetry in Hequ. apply ptyp_to_uskl_syn_var_inv in Hequ; subst.
    assert (Hmd : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    destruct (IHad_partial_precise HwfΘ S1' S2' eq_refl τ eq_refl Hmd)
      as (τ1 & τ2 & Ψ1 & Ψ2 & Hc & Hm1 & Hm2 & Hp1 & Hp2 & HΨ).
    exists τ1, τ2, Ψ1, Ψ2.
    repeat (split; [ solve [ eapply a_def_chain_step; eauto | assumption ] | ]).
    assumption.
Qed.

Lemma ad_ppre_tophole_subject_chain_inv : forall Θ Δ Ψ P ψ,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  forall P0, P = pskl_tophole P0 ->
  forall τ, ψ = ptyp_to_uskl_syn τ -> mono_ptyp τ ->
  exists τe,
    a_def_chain Θ τ τe /\ mono_ptyp τe /\
    {{ Θ ⨟ Δ ⊢ˢ P0 ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τe) }}ad.
Proof.
  intros Θ Δ Ψ P ψ HwfΘ H; induction H; intros S0' HeqS τu Hequ Hmu;
    try discriminate HeqS.
  - (* tophole_remove *)
    inversion HeqS; subst.
    exists τu. split; [ apply a_def_chain_refl | split; assumption ].
  - (* tophole_fill: target all_tag, never a mono paint *)
    exfalso; eapply ptyp_to_uskl_syn_all_tag_absurd; symmetry; exact Hequ.
  - (* tophole_keep: target topholeg *)
    exfalso; eapply ptyp_to_uskl_syn_topholeg_absurd; symmetry; exact Hequ.
  - (* flex_r *)
    symmetry in Hequ. apply ptyp_to_uskl_syn_var_inv in Hequ; subst.
    assert (Hmd : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    destruct (IHad_partial_precise HwfΘ S0' eq_refl τ eq_refl Hmd)
      as (τe & Hc & Hme & Hp).
    exists τe. split; [ eapply a_def_chain_step; eauto | split; assumption ].
Qed.

Lemma ad_ppre_allsyn_subject_mono_absurd : forall Θ Δ Ψ P ψ,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  forall P0, P = pskl_all_syn P0 ->
  forall τ, ψ = ptyp_to_uskl_syn τ -> mono_ptyp τ ->
  False.
Proof.
  intros Θ Δ Ψ P ψ HwfΘ H; induction H; intros S0' HeqS τu Hequ Hmu;
    try discriminate HeqS.
  - (* forall: target all_tag, never a mono paint *)
    eapply ptyp_to_uskl_syn_all_tag_absurd; symmetry; exact Hequ.
  - (* flex_r *)
    symmetry in Hequ. apply ptyp_to_uskl_syn_var_inv in Hequ; subst.
    eapply IHad_partial_precise;
      [ exact HwfΘ | reflexivity | reflexivity
      | eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

Lemma ad_refine_tophole_lhs_chain_inv : forall Θ Δr Q' Q,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δr ⊢ᵣ Q' ⊳ Q }}ad ->
  forall Qb, Q' = bskl_tophole Qb ->
  forall τ, Q = ptyp_to_bskl_syn τ -> mono_ptyp τ ->
  exists τe,
    a_def_chain Θ τ τe /\ mono_ptyp τe /\
    {{ Θ ⨟ Δr ⊢ᵣ Qb ⊳ (ptyp_to_bskl_syn τe) }}ad.
Proof.
  intros Θ Δr Q' Q HwfΘ H; induction H; intros Qb' HeqL τu Hequ Hmu;
    try discriminate HeqL.
  - (* tophole_remove *)
    inversion HeqL; subst.
    exists τu. split; [ apply a_def_chain_refl | split; assumption ].
  - (* tophole_fill: target all_syn, never a MONO paint *)
    exfalso; eapply ptyp_to_bskl_syn_all_syn_mono_absurd;
      [ exact Hmu | symmetry; exact Hequ ].
  - (* tophole_keep: target tophole, never a paint *)
    exfalso; eapply ptyp_to_bskl_syn_tophole_absurd; symmetry; exact Hequ.
  - (* flex_r *)
    symmetry in Hequ. apply ptyp_to_bskl_syn_var_inv in Hequ; subst.
    assert (Hmd : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    destruct (IHad_refine_syn HwfΘ Qb' eq_refl τ eq_refl Hmd)
      as (τe & Hc & Hme & Hr).
    exists τe. split; [ eapply a_def_chain_step; eauto | split; assumption ].
Qed.

Lemma ad_refine_allinh_lhs_mono_absurd : forall Θ Δr Q' Q,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δr ⊢ᵣ Q' ⊳ Q }}ad ->
  forall Qb, Q' = bskl_all_inh Qb ->
  forall τ, Q = ptyp_to_bskl_syn τ -> mono_ptyp τ ->
  False.
Proof.
  intros Θ Δr Q' Q HwfΘ H; induction H; intros Qb' HeqL τu Hequ Hmu;
    try discriminate HeqL.
  - (* all: target all_inh, never a paint *)
    eapply ptyp_to_bskl_syn_all_inh_absurd; symmetry; exact Hequ.
  - (* flex_r *)
    symmetry in Hequ. apply ptyp_to_bskl_syn_var_inv in Hequ; subst.
    eapply IHad_refine_syn;
      [ exact HwfΘ | reflexivity | reflexivity
      | eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

(* ===================================================================== *)
(*  Phase 3: refinement→precision bridges for mono-paint targets.          *)
(*  Bridge A: a mono-paint LHS (κ-image of a flexible counterpart) is      *)
(*  precise to the target at ANY Δ — paints contain no ghosts, so no       *)
(*  Δ-sensitive rule fires.  Bridge B: an arbitrary inherited-painting     *)
(*  LHS, given the □-precision at the same target (the Pi = □ case);      *)
(*  ghost leaves reuse the □-precision, def-chain hops use Δ-def-freshness.*)
(* ===================================================================== *)

Lemma ad_refine_mono_paint_lhs_ppre : forall Θ Δr Q' Q,
  {{ ⊢ Θ }}a ->
  Δr [=] empty ->
  {{ Θ ⨟ Δr ⊢ᵣ Q' ⊳ Q }}ad ->
  forall τb τ, Q' = ptyp_to_bskl_syn τb -> Q = ptyp_to_bskl_syn τ ->
  mono_ptyp τb -> mono_ptyp τ ->
  forall Δ, {{ Θ ⨟ Δ ⊢ˢ (ptyp_to_pskl τb) ⊑ᵖ[ empty ] (ptyp_to_uskl_syn τ) }}ad.
Proof.
  intros Θ Δr Q' Q HwfΘ HΔr H; induction H;
    intros τb τu HeqL HeqQ Hmb Hmu Δo;
    try solve [ exfalso; symmetry in HeqL;
                solve [ eapply ptyp_to_bskl_syn_all_inh_absurd; exact HeqL
                      | eapply ptyp_to_bskl_syn_hole_absurd; exact HeqL
                      | eapply ptyp_to_bskl_syn_tophole_absurd; exact HeqL ] ].
  - (* unit *)
    symmetry in HeqL; apply ptyp_to_bskl_syn_unit_inv in HeqL; subst.
    symmetry in HeqQ; apply ptyp_to_bskl_syn_unit_inv in HeqQ; subst.
    simpl. apply ad_ppre__unit. clear; fsetdec.
  - (* var *)
    symmetry in HeqL; apply ptyp_to_bskl_syn_var_inv in HeqL; subst.
    symmetry in HeqQ; apply ptyp_to_bskl_syn_var_inv in HeqQ.
    inversion HeqQ; subst.
    simpl. apply ad_ppre__var; [ clear; fsetdec | ].
    match goal with
    | Hd : _ \/ a_binds_tvar _ _ |- _ =>
        destruct Hd as [ Hin | Hb ]; [ exfalso; clear - Hin HΔr; fsetdec
                                     | right; exact Hb ]
    end.
  - (* arrow *)
    symmetry in HeqL.
    destruct (ptyp_to_bskl_syn_arrow_inv _ HeqL)
      as (τb1 & τb2 & -> & Heqb1 & Heqb2).
    symmetry in HeqQ.
    destruct (ptyp_to_bskl_syn_arrow_inv _ HeqQ)
      as (τ1 & τ2 & -> & Heq1 & Heq2).
    assert (Hmb1 : mono_ptyp τb1) by (inversion Hmb; assumption).
    assert (Hmb2 : mono_ptyp τb2) by (inversion Hmb; assumption).
    assert (Hm1 : mono_ptyp τ1) by (inversion Hmu; assumption).
    assert (Hm2 : mono_ptyp τ2) by (inversion Hmu; assumption).
    simpl.
    apply ad_ppre__arrow with (Ψ1 := empty) (Ψ2 := empty);
      [ apply IHad_refine_syn1; auto
      | apply IHad_refine_syn2; auto
      | clear; fsetdec ].
  - (* flex_l *)
    symmetry in HeqL; apply ptyp_to_bskl_syn_var_inv in HeqL; subst.
    simpl.
    eapply ad_ppre__flex_l; [ eassumption | ].
    apply IHad_refine_syn; auto;
      [ eapply a_wf_aenv_binds_def_mono; eauto ].
  - (* flex_r *)
    symmetry in HeqQ; apply ptyp_to_bskl_syn_var_inv in HeqQ; subst.
    simpl.
    eapply ad_ppre__flex_r; [ eassumption | ].
    apply IHad_refine_syn; auto;
      [ eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

Lemma ad_refine_inh_hole_ppre : forall Θ Δr Q' Q,
  {{ ⊢ Θ }}a ->
  Δr [=] empty ->
  {{ Θ ⨟ Δr ⊢ᵣ Q' ⊳ Q }}ad ->
  forall P' τ, Q' = pskl_to_bskl_inh P' -> Q = ptyp_to_bskl_syn τ ->
  mono_ptyp τ ->
  forall Δ Ψ, delta_def_fresh Δ Θ ->
  {{ Θ ⨟ Δ ⊢ˢ pskl_hole ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τ) }}ad ->
  {{ Θ ⨟ Δ ⊢ˢ P' ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τ) }}ad.
Proof.
  intros Θ Δr Q' Q HwfΘ HΔr H; induction H;
    intros P' τu HeqL HeqQ Hmu Δo Ψo Hdf Hhp.
  - (* unit *)
    destruct P'; simpl in HeqL; try discriminate HeqL.
    symmetry in HeqQ; apply ptyp_to_bskl_syn_unit_inv in HeqQ; subst.
    assert (HΨ : Ψo [=] empty)
      by (eapply ad_ppre_mono_tags_empty;
            [ exact HwfΘ | exact Hhp | reflexivity | exact Hmu ]).
    simpl. apply ad_ppre__unit. exact HΨ.
  - (* var *)
    destruct P'; simpl in HeqL; try discriminate HeqL.
    inversion HeqL; subst.
    symmetry in HeqQ; apply ptyp_to_bskl_syn_var_inv in HeqQ.
    inversion HeqQ; subst.
    assert (HΨ : Ψo [=] empty)
      by (eapply ad_ppre_mono_tags_empty;
            [ exact HwfΘ | exact Hhp | reflexivity | exact Hmu ]).
    simpl. apply ad_ppre__var; [ exact HΨ | ].
    match goal with
    | Hd : _ \/ a_binds_tvar _ _ |- _ =>
        destruct Hd as [ Hin | Hb ]; [ exfalso; clear - Hin HΔr; fsetdec
                                     | right; exact Hb ]
    end.
  - (* arrow *)
    symmetry in HeqQ.
    destruct (ptyp_to_bskl_syn_arrow_inv _ HeqQ)
      as (τ1 & τ2 & -> & Heq1 & Heq2).
    destruct (pskl_to_bskl_inh_arrow_inv _ (eq_sym HeqL))
      as (Pb1 & Pb2 & -> & HeqPb1 & HeqPb2).
    assert (Hm1 : mono_ptyp τ1) by (inversion Hmu; assumption).
    assert (Hm2 : mono_ptyp τ2) by (inversion Hmu; assumption).
    simpl in Hhp.
    inversion Hhp; subst.
    + (* hole rule *)
      match goal with
      | HΨe : Ψo [=] empty |- _ => rename HΨe into HPsiE
      end.
      match goal with
      | Hint : _ ∩ _ [=] empty |- _ => rename Hint into HInt
      end.
      rewrite ftvar_ptyp_to_uskl_syn in HInt.
      simpl in HInt.
      assert (Hhp1 : {{ Θ ⨟ Δo ⊢ˢ pskl_hole ⊑ᵖ[ empty ] (ptyp_to_uskl_syn τ1) }}ad)
        by (apply ad_ppre__hole;
              [ clear; fsetdec
              | rewrite ftvar_ptyp_to_uskl_syn;
                clear - HInt; fsetdec ]).
      assert (Hhp2 : {{ Θ ⨟ Δo ⊢ˢ pskl_hole ⊑ᵖ[ empty ] (ptyp_to_uskl_syn τ2) }}ad)
        by (apply ad_ppre__hole;
              [ clear; fsetdec
              | rewrite ftvar_ptyp_to_uskl_syn;
                clear - HInt; fsetdec ]).
      simpl.
      apply ad_ppre__arrow with (Ψ1 := empty) (Ψ2 := empty);
        [ eapply IHad_refine_syn1;
            [ exact HwfΘ | exact HΔr | reflexivity
            | reflexivity | exact Hm1 | exact Hdf | exact Hhp1 ]
        | eapply IHad_refine_syn2;
            [ exact HwfΘ | exact HΔr | reflexivity
            | reflexivity | exact Hm2 | exact Hdf | exact Hhp2 ]
        | clear - HPsiE; fsetdec ].
  - (* all: target is an all_inh, never a mono paint *)
    exfalso; eapply ptyp_to_bskl_syn_all_inh_absurd; symmetry; exact HeqQ.
  - (* hole: LHS painting forces P' = □; the □-precision IS the goal *)
    destruct P'; simpl in HeqL; try discriminate HeqL.
    exact Hhp.
  - (* tophole_remove *)
    destruct P'; simpl in HeqL; try discriminate HeqL.
    inversion HeqL; subst.
    apply ad_ppre__tophole_remove.
    eapply IHad_refine_syn; eauto.
  - (* tophole_fill: target all_syn, never a MONO paint *)
    exfalso; eapply ptyp_to_bskl_syn_all_syn_mono_absurd;
      [ exact Hmu | symmetry; exact HeqQ ].
  - (* tophole_keep: target tophole, never a paint *)
    exfalso; eapply ptyp_to_bskl_syn_tophole_absurd; symmetry; exact HeqQ.
  - (* flex_l *)
    destruct P'; simpl in HeqL; try discriminate HeqL.
    inversion HeqL; subst.
    eapply ad_ppre__flex_l; [ eassumption | ].
    assert (Hmα : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; eauto).
    eapply IHad_refine_syn;
      [ exact HwfΘ | exact HΔr
      | symmetry; apply ptyp_to_bskl_inh_syn_eq; exact Hmα
      | reflexivity | exact Hmu | exact Hdf | exact Hhp ].
  - (* flex_r *)
    symmetry in HeqQ; apply ptyp_to_bskl_syn_var_inv in HeqQ; subst.
    assert (HmX : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; eauto).
    simpl in Hhp.
    assert (Hhp' : {{ Θ ⨟ Δo ⊢ˢ pskl_hole ⊑ᵖ[ Ψo ] (ptyp_to_uskl_syn τ) }}ad).
    { inversion Hhp; subst.
      - (* hole rule at the variable target: rebuild at the definition *)
        apply ad_ppre__hole; [ assumption | ].
        rewrite ftvar_ptyp_to_uskl_syn.
        apply inter_empty_pointwise.
        intros y Hy. eapply Hdf; eauto.
      - (* flex_r: same definition by uniqueness *)
        match goal with
        | Hb2 : binds _ (abind_flex_mono_def _) _ |- _ =>
            pose proof (binds_unique _ _ _ _ _ Hb2 H
                          (a_wf_aenv_uniq HwfΘ)) as Hcc;
            inversion Hcc; subst; assumption
        end. }
    simpl.
    eapply ad_ppre__flex_r; [ eassumption | ].
    eapply IHad_refine_syn;
      [ exact HwfΘ | exact HΔr | reflexivity
      | reflexivity | exact HmX | exact Hdf | exact Hhp' ].
Qed.

(* ---- a rigid variable never refines into a non-variable target ---- *)

Lemma ad_refine_syn_rigid_var_nonvar_absurd : forall Θ Δr α Q,
  {{ ⊢ Θ }}a ->
  binds α abind_tvar Θ ->
  {{ Θ ⨟ Δr ⊢ᵣ (bskl_var_f α) ⊳ Q }}ad ->
  (forall β, Q <> bskl_var_f β) ->
  False.
Proof.
  intros Θ Δr α Q HwfΘ Hb H Hnv; inversion H; subst.
  - eapply Hnv; reflexivity.
  - match goal with
    | Hbd : binds _ (abind_flex_mono_def _) _ |- _ =>
        pose proof (binds_unique _ _ _ _ _ Hb Hbd (a_wf_aenv_uniq HwfΘ)) as Hc;
        discriminate Hc
    end.
  - eapply Hnv; reflexivity.
Qed.

(* ===================================================================== *)
(*  Phase 4: the mono-target case lemma.  Subsumes Unit (τ = 1) and Var    *)
(*  (τ = α): the target is the painting of a MONO ptyp, the shape all      *)
(*  defined-flex chains stay inside.  Strong induction on                  *)
(*  size Pi + size P0 (∀◇-stripping both sides); the target's def-chain    *)
(*  unfolding is handled by the Phase-2 chain inversions (which ride the   *)
(*  premise derivations, not the size).                                    *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  ⭐⭐ THE κ-EXTENSION WITNESS, MONO-TARGET FORM (2026-08-04).             *)
(*                                                                        *)
(*  This is what the SolE-FlexR repair costs the completeness proofs.  The *)
(*  repaired row returns [guess^TY(P_i)] instead of the target flexible,   *)
(*  and [guess^TY] INVENTS a fresh flexible for every ghost of [P_i] — so  *)
(*  the solve's output is no longer interpretable under the ambient [κ].   *)
(*  It has to be EXTENDED, positionally, over exactly that block.          *)
(*                                                                        *)
(*  We do not consume a given guess: the conclusion is existential in the  *)
(*  block, so [a_guess_mono] and the extension [κ'] are BUILT              *)
(*  SIMULTANEOUSLY, descending [P_i] and reading the counterpart's         *)
(*  matching monotype off the precision premise at each step.  At a ◇ the  *)
(*  guess invents [α̂1] and [κ'] sends it to the monotype standing at that  *)
(*  position — after which the obligation is just precision-reflexivity    *)
(*  at a monotype.  ([ad_ppre__hole] — a ghost is precise into ANYTHING at *)
(*  [Ψ = ∅] — is what licenses the descent reaching a ◇ at all.)           *)
(*                                                                        *)
(*  Same shape as [a_guess_ty_witness] (sub/look/prop_extract.v §9),  *)
(*  which does this for the FINAL guess against the refinement; this is    *)
(*  the SOLVE's guess against the precision judgment, and it is the easier *)
(*  of the two because the target is a MONOTYPE.                           *)
(*                                                                        *)
(*  ⚙️ L-BOUNDED CONTEXT QUANTIFICATION: the guess is valid at any context *)
(*  whose mentioned names stay inside [L], and [L] is fixed BEFORE the     *)
(*  block is picked.  That is what lets the arrow case run its second IH   *)
(*  at [L ∪ dom Ξ1] and get the two blocks disjoint for free.              *)
(* ===================================================================== *)

(** Precision is REFLEXIVE at a monotype.  The scoping premise is what
    [ad_ppre__var] demands, and [a_wf_ptyp] is exactly its supply. *)
Lemma ad_ppre_mono_refl : forall Θ Δ τ,
  mono_ptyp τ ->
  a_wf_ptyp Θ τ ->
  {{ Θ ⨟ Δ ⊢ˢ (ptyp_to_pskl τ) ⊑ᵖ[ empty ] (ptyp_to_uskl_syn τ) }}ad.
Proof.
  intros Θ Δ τ Hm; induction Hm; intros Hwf;
    cbn [ptyp_to_pskl ptyp_to_uskl_syn].
  - apply ad_ppre__unit. clear; fsetdec.
  - apply ad_ppre__var;
      [ clear; fsetdec | right; inversion Hwf; assumption ].
  - inversion Hwf; subst.
    apply ad_ppre__arrow with (Ψ1 := empty) (Ψ2 := empty);
      [ auto | auto | clear; fsetdec ].
Qed.

(** wf transports along a definition chain — each step unfolds a defined
    flexible, whose payload the context's own well-formedness bounds. *)
Lemma a_def_chain_wf : forall Θ τ τe,
  a_def_chain Θ τ τe -> {{ ⊢ Θ }}a -> a_wf_ptyp Θ τ -> a_wf_ptyp Θ τe.
Proof.
  intros Θ τ τe Hc; induction Hc; intros Hwf Hp; auto.
  apply IHHc; [ exact Hwf | ].
  eapply a_wf_aenv_binds_def_wf; eauto.
Qed.

(** A RIGID variable has no definition, so every chain out of it is the
    reflexive one.  This is what makes the [τ = rigid var] target harmless
    below: each branch that would need [a_wf_ptyp Θw τ] first inverts a chain
    from [τ] to a compound, and here there is none. *)
Lemma a_def_chain_rigid_var_inv : forall Θ α τe,
  a_def_chain Θ (ptyp_var_f α) τe ->
  {{ ⊢ Θ }}a ->
  binds α abind_tvar Θ ->
  τe = ptyp_var_f α.
Proof.
  intros Θ α τe Hc HwfΘ Hrig.
  inversion Hc as [ | α0 τd τe0 Hb Hc0 ]; subst; [ reflexivity | ].
  exfalso.
  pose proof (binds_unique _ _ _ _ _ Hrig Hb (a_wf_aenv_uniq HwfΘ)) as Hcc.
  discriminate Hcc.
Qed.

(** ⭐ The wf-or-rigid DISJUNCTION propagates along a definition chain, which
    is what lets a P6 ∀ row carry a BOUND-RIGID target all the way down: the
    chain either unfolds a definition (and then the target was wf at [Θw] to
    begin with, so wf transports) or it is reflexive at the rigid. *)
(** ⭐ The same, but reporting well-formedness in a DIFFERENT context [Θw] —
    one that has all of [Θ]'s definitions.  This is what lets the κ-extension
    stay interpretable UNDER A BINDER: a P6 ∀ row runs its body at
    [(α ~ tvar) ++ Θ], and the payloads it invents there must still be wf
    OUTSIDE the binder, because the solve's ∀ rows pass the generated block
    through unchanged (the flexibles are declared outside).  A rigid entry
    carries no definition, so [Hdefs] is immediate at every such row. *)
(** A tvar-ish binding survives into a SUBCONTEXT that still has the
    variable: the two contexts agree on the binding by uniqueness. *)
(* ⚙ RENAMED from [a_binds_tvar_strengthen] 2026-08-09 (cleanup audit §8.1c): it collided with a
   DIFFERENT lemma of that name, and this one same theorem as prop_metasubst.v's with the premises in a different ORDER. *)
Lemma a_binds_tvar_strengthen_kit : forall Θ Θw α,
  uniq Θ ->
  (forall x b, binds x b Θw -> binds x b Θ) ->
  a_binds_tvar α Θ ->
  α `in` dom Θw ->
  a_binds_tvar α Θw.
Proof.
  intros Θ Θw α Hu Hmon Hbt Hin.
  apply binds_In_inv in Hin. destruct Hin as [b Hb].
  assert (Hb' : binds α b Θ) by (apply Hmon; exact Hb).
  destruct Hbt as [Hr | [Hf | (τ & Hd)]].
  - pose proof (binds_unique _ _ _ _ _ Hb' Hr Hu) as ->.
    left; exact Hb.
  - pose proof (binds_unique _ _ _ _ _ Hb' Hf Hu) as ->.
    right; left; exact Hb.
  - pose proof (binds_unique _ _ _ _ _ Hb' Hd Hu) as ->.
    right; right; exists τ; exact Hb.
Qed.

(** …hence a MONOTYPE well-formed in [Θ] and scoped inside [dom Θw] is
    well-formed in [Θw]. *)
Lemma a_wf_ptyp_mono_strengthen_dom : forall Θ Θw τ,
  {{ ⊢ Θ }}a ->
  (forall x b, binds x b Θw -> binds x b Θ) ->
  mono_ptyp τ ->
  a_wf_ptyp Θ τ ->
  ftvar_in_ptyp τ [<=] dom Θw ->
  a_wf_ptyp Θw τ.
Proof.
  intros Θ Θw τ HwfΘ Hmon Hm Hwf Hsub.
  apply mono_ptyp_wf; [ exact Hm | ].
  intros α Hα.
  eapply a_binds_tvar_strengthen_kit;
    [ apply a_wf_aenv_uniq; exact HwfΘ
    | exact Hmon
    | eapply a_wf_ptyp_ftv_binds; [ exact Hwf | exact Hα ]
    | clear - Hsub Hα; fsetdec ].
Qed.

Lemma a_def_chain_wf_at : forall Θ Θw τ τe,
  a_def_chain Θ τ τe ->
  {{ ⊢ Θw }}a ->
  (forall α τ0, binds α (abind_flex_mono_def τ0) Θ ->
     binds α (abind_flex_mono_def τ0) Θw) ->
  a_wf_ptyp Θw τ ->
  a_wf_ptyp Θw τe.
Proof.
  intros Θ Θw τ τe Hc; induction Hc; intros Hwf Hdefs Hp; auto.
  apply IHHc; [ exact Hwf | exact Hdefs | ].
  eapply a_wf_aenv_binds_def_wf; [ exact Hwf | apply Hdefs; eassumption ].
Qed.

(** ⭐ …and the SCOPE bound the position-wise payload route threads
    (2026-08-05).  A chain STEP lands on a DEFINITION of [Θ], which [Hdefs]
    places in [Θw] and [Θw]'s own well-formedness scopes — so the bound is
    restored outright after one step and merely carried by reflexivity. *)
Lemma a_def_chain_ftv_at : forall Θ Θw Δ τ τe,
  a_def_chain Θ τ τe ->
  {{ ⊢ Θw }}a ->
  (forall α τ0, binds α (abind_flex_mono_def τ0) Θ ->
     binds α (abind_flex_mono_def τ0) Θw) ->
  ftvar_in_ptyp τ [<=] dom Θw `union` Δ ->
  ftvar_in_ptyp τe [<=] dom Θw `union` Δ.
Proof.
  intros Θ Θw Δ τ τe Hc; induction Hc; intros HwfΘw Hdefs Hft; [ exact Hft | ].
  apply IHHc; [ exact HwfΘw | exact Hdefs | ].
  assert (Hb : binds α (abind_flex_mono_def τd) Θw)
    by (apply Hdefs; assumption).
  assert (Hd : ftvar_in_ptyp τd [<=] dom Θw)
    by (eapply a_wf_aenv_def_ftv_dom; [ exact HwfΘw | exact Hb ]).
  clear - Hd; fsetdec.
Qed.

(** ⭐⭐ THE POSITION-WISE PAYLOAD SCOPE (2026-08-05).  A HOLE subject reaches
    its target either directly ([ad_ppre__hole], whose OWN side condition is
    the Δ-apartness) or across a flexible DEFINITION lookup
    ([ad_ppre__flex_r], whose target variable is a defined flexible and so
    already lives in [Θw]).  Either way the monotype standing at the hole is
    [Θw]-scoped — with no cleanliness premise anywhere.

    This is what lets [a_guess_ty_witness_mono_gen] below take the counterpart
    well-formed only in [Θ]: the flexibles [guess^TY] invents sit exactly at
    the holes, and nowhere else does the construction read a payload. *)
Lemma ppre_hole_payload_wf : forall Θ Θw Δ Ψ τ,
  {{ ⊢ Θ }}a -> {{ ⊢ Θw }}a ->
  (forall x b, binds x b Θw -> binds x b Θ) ->
  (forall α τ0, binds α (abind_flex_mono_def τ0) Θ ->
     binds α (abind_flex_mono_def τ0) Θw) ->
  mono_ptyp τ -> a_wf_ptyp Θ τ ->
  ftvar_in_ptyp τ [<=] dom Θw `union` Δ ->
  {{ Θ ⨟ Δ ⊢ˢ pskl_hole ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τ) }}ad ->
  a_wf_ptyp Θw τ.
Proof.
  intros Θ Θw Δ Ψ τ HwfΘ HwfΘw Hmon Hdefs Hm Hwf Hft Hpre.
  inversion Hpre; subst.
  - (* ad_ppre__hole : the rule's OWN side condition is the Δ-apartness *)
    assert (Hap : ftvar_in_ptyp τ ∩ Δ [=] empty).
    { match goal with Hd : Δ ∩ ftvar_in_uskl _ [=] empty |- _ =>
        rewrite ftvar_ptyp_to_uskl_syn in Hd; clear - Hd; fsetdec
      end. }
    eapply a_wf_ptyp_mono_strengthen_dom;
      [ exact HwfΘ | exact Hmon | exact Hm | exact Hwf
      | clear - Hft Hap; fsetdec ].
  - (* ad_ppre__flex_r : the target is a DEFINED FLEXIBLE, hence in [Θw] *)
    destruct τ; simpl in *; try discriminate.
    match goal with Heq : uskl_var_f _ = ptyp_to_uskl_syn _ |- _ =>
      cbn [ptyp_to_uskl_syn] in Heq; inversion Heq; subst end.
    apply a_wf_ptyp__var. right; right.
    match goal with Hb : binds _ (abind_flex_mono_def ?τ0) Θ |- _ =>
      exists τ0; apply Hdefs; exact Hb end.
Qed.

(* ⭐ [Θw] IS THE WELL-FORMEDNESS CONTEXT OF THE EXTENSION, AND IT IS NOT
   [Θ] (2026-08-04).  [Θ] is where the PRECISION lives and where the
   definition chains are read; [Θw] is where the invented flexibles' payloads
   have to be well-formed.  They differ exactly under a binder: a P6 ∀ row
   runs its body at [(α ~ tvar) ++ Θ], but the block the body generates is
   emitted OUTSIDE the ∀ (the solve's ∀ rows pass [Ξ] through unchanged), so a
   payload mentioning the bound rigid would be ill-scoped.  Keeping [Θw]
   fixed all the way down is what makes the construction compose; the caller
   supplies [a_wf_ptyp Θw τ], which it can because at an SE-FlexR node the
   counterpart monotype is a κ-IMAGE, and [κ ∷ Θ0 ⊑ Θw] makes every image wf
   at [Θw]. *)
Lemma a_def_chain_wf_or_rigid : forall Θ Θw τ τe,
  a_def_chain Θ τ τe ->
  {{ ⊢ Θ }}a ->
  {{ ⊢ Θw }}a ->
  (forall α τ0, binds α (abind_flex_mono_def τ0) Θ ->
     binds α (abind_flex_mono_def τ0) Θw) ->
  (a_wf_ptyp Θw τ \/ (exists α0, τ = ptyp_var_f α0 /\ binds α0 abind_tvar Θ)) ->
  (a_wf_ptyp Θw τe \/
     (exists α0, τe = ptyp_var_f α0 /\ binds α0 abind_tvar Θ)).
Proof.
  intros Θ Θw τ τe Hc HwfΘ HwfΘw Hdefs [Hw | (α0 & Heq & Hrig)].
  - left. eapply a_def_chain_wf_at;
      [ exact Hc | exact HwfΘw | exact Hdefs | exact Hw ].
  - subst τ. rewrite (a_def_chain_rigid_var_inv Hc HwfΘ Hrig).
    right. exists α0. split; [ reflexivity | exact Hrig ].
Qed.

Lemma a_guess_ty_witness_mono_gen : forall n Θ0 Θ Θw κ Δ Ψi τ Pi,
  size_pskl Pi <= n ->
  {{ ⊢ Θ }}a ->
  {{ ⊢ Θw }}a ->
  (* [Θ] EXTENDS [Θw] and adds no definitions — at every call site [Θ] is
     [Θw] itself or [Θw] under a stack of rigid binders. *)
  (forall x b, binds x b Θw -> binds x b Θ) ->
  (forall α τ0, binds α (abind_flex_mono_def τ0) Θ ->
     binds α (abind_flex_mono_def τ0) Θw) ->
  {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a ->
  mono_ptyp τ ->
  (* ⭐ THE GENERALIZATION: the counterpart need only be well-formed in [Θ],
     with every variable of it that [Θw] does NOT have accounted for as a
     [Δ]-variable.  [ad_ppre__hole] forces the target facing a hole to avoid
     [Δ], so at the ONLY positions that invent a payload the two premises
     collapse back to [a_wf_ptyp Θw]. *)
  a_wf_ptyp Θ τ ->
  ftvar_in_ptyp τ [<=] dom Θw `union` Δ ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (ptyp_to_uskl_syn τ) }}ad ->
  forall L, exists (Ξ : aenv) (A : ptyp) (κ' : metasubst),
    (forall Θg, ftvar_in_aenv Θg [<=] L -> a_guess_mono Θg Pi Ξ A) /\
    all_flex_mono Ξ /\
    uniq Ξ /\
    keys κ' = keys Ξ /\
    (forall α, α `in` dom Ξ -> α `notin` L) /\
    Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κ' /\
    {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κ' ++ κ) (ptyp_to_pskl A))
            ⊑ᵖ[ Ψi ] (ptyp_to_uskl_syn τ) }}ad.
Proof.
  induction n as [ | n IH ];
    intros Θ0 Θ Θw κ Δ Ψi τ Pi Hsz HwfΘ HwfΘw Hmon Hdefs HwfPi Hmτ Hwfτ Hftτ Hpre L.
  { exfalso. pose proof (size_pskl_min Pi) as Hm. clear - Hsz Hm. lia. }
  destruct Pi as [ | nb | α | Pi1 Pi2 | Pib | | Pi' ].
  - (* unit : the guess is the identity *)
    exists nil, ptyp_unit, nil.
    split; [ intros Θg _; apply a_guess_mono__unit | ].
    split; [ apply Forall_nil | ].
    split; [ apply uniq_nil | ].
    split; [ reflexivity | ].
    split; [ intros α0 Hα0; cbn in Hα0; exfalso; clear - Hα0; fsetdec | ].
    split; [ apply Forall_nil | ].
    cbn [app ptyp_to_pskl msubst_pskl] in *. exact Hpre.
  - (* var_b : excluded by well-formedness *) inversion HwfPi.
  - (* var : the guess is the identity *)
    exists nil, (ptyp_var_f α), nil.
    split; [ intros Θg _; apply a_guess_mono__var | ].
    split; [ apply Forall_nil | ].
    split; [ apply uniq_nil | ].
    split; [ reflexivity | ].
    split; [ intros α0 Hα0; cbn in Hα0; exfalso; clear - Hα0; fsetdec | ].
    split; [ apply Forall_nil | ].
    cbn [app ptyp_to_pskl]. exact Hpre.
  - (* ---------------------------- arrow ---------------------------- *)
    cbn in Hsz.
    assert (HwfPi1 : {{ Θ0 ⨟ empty ⊢ₚₛ Pi1 }}a) by (inversion HwfPi; assumption).
    assert (HwfPi2 : {{ Θ0 ⨟ empty ⊢ₚₛ Pi2 }}a) by (inversion HwfPi; assumption).
    cbn [msubst_pskl] in Hpre.
    destruct (ad_ppre_arrow_subject_chain_inv HwfΘ Hpre eq_refl eq_refl Hmτ)
      as (τ1 & τ2 & Ψ1 & Ψ2 & Hc & Hm1 & Hm2 & Hp1 & Hp2 & HΨ).
    assert (Hwfar : a_wf_ptyp Θ (ptyp_arrow τ1 τ2))
      by (eapply a_def_chain_wf;
            [ exact Hc | exact HwfΘ | exact Hwfτ ]).
    assert (Hftar : ftvar_in_ptyp (ptyp_arrow τ1 τ2) [<=] dom Θw `union` Δ)
      by (eapply a_def_chain_ftv_at;
            [ exact Hc | exact HwfΘw | exact Hdefs | exact Hftτ ]).
    cbn [ftvar_in_ptyp] in Hftar.
    assert (Hwf1 : a_wf_ptyp Θ τ1) by (inversion Hwfar; assumption).
    assert (Hwf2 : a_wf_ptyp Θ τ2) by (inversion Hwfar; assumption).
    assert (Hft1 : ftvar_in_ptyp τ1 [<=] dom Θw `union` Δ)
      by (clear - Hftar; fsetdec).
    assert (Hft2 : ftvar_in_ptyp τ2 [<=] dom Θw `union` Δ)
      by (clear - Hftar; fsetdec).
    (* ⚠️ BOTH IHs run at an avoid-set containing BOTH sources, and the
       second additionally avoids the first block.  That is what makes each
       branch's extension invisible to the other's result below. *)
    destruct (IH Θ0 Θ Θw κ Δ Ψ1 τ1 Pi1 ltac:(lia) HwfΘ HwfΘw Hmon Hdefs
                HwfPi1 Hm1 Hwf1 Hft1 Hp1
                (L `union` ftvar_in_pskl Pi1 `union` ftvar_in_pskl Pi2))
      as (Ξ1 & A1 & κa & Hgu1 & Hfm1 & Hu1 & Hk1 & Hfr1 & HF1 & Hpr1).
    destruct (IH Θ0 Θ Θw κ Δ Ψ2 τ2 Pi2 ltac:(lia) HwfΘ HwfΘw Hmon Hdefs
                HwfPi2 Hm2 Hwf2 Hft2 Hp2
                (L `union` ftvar_in_pskl Pi1 `union` ftvar_in_pskl Pi2
                   `union` dom Ξ1))
      as (Ξ2 & A2 & κb & Hgu2 & Hfm2 & Hu2 & Hk2 & Hfr2 & HF2 & Hpr2).
    assert (Hdκa : dom κa [=] dom Ξ1) by (apply keys_eq_dom; exact Hk1).
    assert (Hdκb : dom κb [=] dom Ξ2) by (apply keys_eq_dom; exact Hk2).
    (* the guessed results only mention their own source plus their own
       block, which is what makes each branch's extension invisible to the
       other *)
    assert (HA1 : ftvar_in_pskl (ptyp_to_pskl A1)
                  [<=] ftvar_in_pskl Pi1 `union` dom Ξ1).
    { assert (Hb : ftvar_in_ptyp A1 [<=] ftvar_in_pskl Pi1 `union` dom Ξ1)
        by (eapply a_guess_mono_ftv; apply (Hgu1 nil); simpl; fsetdec).
      pose proof (ptyp_to_pskl_ftv A1) as Hc1. clear - Hb Hc1; fsetdec. }
    assert (HA2 : ftvar_in_pskl (ptyp_to_pskl A2)
                  [<=] ftvar_in_pskl Pi2 `union` dom Ξ2).
    { assert (Hb : ftvar_in_ptyp A2 [<=] ftvar_in_pskl Pi2 `union` dom Ξ2)
        by (eapply a_guess_mono_ftv; apply (Hgu2 nil); simpl; fsetdec).
      pose proof (ptyp_to_pskl_ftv A2) as Hc2. clear - Hb Hc2; fsetdec. }
    assert (Hdisj : disjoint Ξ1 Ξ2).
    { unfold disjoint. intros α0 Hα0.
      assert (Hin2 : α0 `in` dom Ξ2) by (clear - Hα0; fsetdec).
      specialize (Hfr2 α0 Hin2). clear - Hα0 Hfr2; fsetdec. }
    (* ⚠️ the second block's names are fresh for [L ∪ dom Ξ1], so they miss
       the FIRST branch's source and result; and the first block's names are
       fresh for [L], which the second branch's source sits inside *)
    assert (Heq1 : msubst_pskl (κa ++ κb ++ κ) (ptyp_to_pskl A1)
                   = msubst_pskl (κa ++ κ) (ptyp_to_pskl A1)).
    { apply msubst_pskl_mid_skip. intros α0 Hα0.
      assert (Hin2 : α0 `in` dom Ξ2) by (clear - Hα0 Hdκb; fsetdec).
      specialize (Hfr2 α0 Hin2). clear - Hfr2 HA1; fsetdec. }
    assert (Heq2 : msubst_pskl (nil ++ κa ++ (κb ++ κ)) (ptyp_to_pskl A2)
                   = msubst_pskl (nil ++ (κb ++ κ)) (ptyp_to_pskl A2)).
    { apply msubst_pskl_mid_skip. intros α0 Hα0.
      assert (Hin1 : α0 `in` dom Ξ1) by (clear - Hα0 Hdκa; fsetdec).
      specialize (Hfr1 α0 Hin1).
      assert (Hne : α0 `notin` dom Ξ2)
        by (clear - Hin1 Hdisj; unfold disjoint in Hdisj; fsetdec).
      clear - Hfr1 Hne HA2; fsetdec. }
    cbn [app] in Heq2.
    exists (Ξ1 ++ Ξ2), (ptyp_arrow A1 A2), (κa ++ κb).
    split; [ intros Θg Hsub; apply a_guess_mono__arrow;
             [ apply Hgu1 | apply Hgu2 ]; clear - Hsub; fsetdec | ].
    split; [ apply all_flex_mono_app; assumption | ].
    split; [ clear - Hu1 Hu2 Hdisj; solve_uniq | ].
    split; [ rewrite ! keys_app; rewrite Hk1, Hk2; reflexivity | ].
    split; [ intros α0 Hα0; rewrite dom_app in Hα0;
             destruct (union_1 Hα0) as [Hin1 | Hin2];
               [ specialize (Hfr1 α0 Hin1); clear - Hfr1; fsetdec
               | specialize (Hfr2 α0 Hin2); clear - Hfr2; fsetdec ] | ].
    split; [ apply Forall_app; split; assumption | ].
    (* fold the chain back and rebuild the arrow *)
    eapply ad_ppre_chain_fold; [ exact Hc | ].
    rewrite list_app_assoc. cbn [ptyp_to_pskl msubst_pskl ptyp_to_uskl_syn].
    rewrite Heq1, Heq2.
    apply ad_ppre__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
      [ exact Hpr1 | exact Hpr2 | exact HΨ ].
  - (* ∀ subject into a MONO target : absurd *)
    exfalso.
    cbn [msubst_pskl] in Hpre.
    eapply ad_ppre_allsyn_subject_mono_absurd;
      [ exact HwfΘ | exact Hpre | reflexivity | reflexivity | exact Hmτ ].
  - (* ---------------------------- ◇ -------------------------------- *)
    (* the guess invents [α̂1]; [κ'] sends it to the monotype standing here *)
    destruct (atom_fresh L) as [α1 Hα1].
    (* ⭐ the payload's [Θw]-scope, position-wise: this is a HOLE, and
       [ad_ppre__hole]'s own Δ-disjointness closes the gap the statement's
       weakened premise left open. *)
    cbn [msubst_pskl] in Hpre.
    assert (Hwfw : a_wf_ptyp Θw τ)
      by (eapply ppre_hole_payload_wf;
            [ exact HwfΘ | exact HwfΘw | exact Hmon | exact Hdefs
            | exact Hmτ | exact Hwfτ | exact Hftτ | exact Hpre ]).
    assert (HΨi : Ψi [=] empty)
      by (eapply ad_ppre_mono_tags_empty;
            [ exact HwfΘ | exact Hpre | reflexivity | exact Hmτ ]).
    exists ((α1 ~ abind_flex_mono) ++ nil), (ptyp_var_f α1),
           ((α1, τ) :: nil).
    split; [ intros Θg Hsub; apply a_guess_mono__hole;
             clear - Hsub Hα1; fsetdec | ].
    split; [ apply Forall_cons; [ reflexivity | apply Forall_nil ] | ].
    split; [ solve_uniq | ].
    split; [ reflexivity | ].
    split; [ intros α0 Hα0; simpl in Hα0;
             assert (Heq : α0 = α1) by (clear - Hα0; fsetdec);
             subst α0; exact Hα1 | ].
    split; [ apply Forall_cons;
             [ split; [ exact Hwfw | exact Hmτ ] | apply Forall_nil ] | ].
    cbn [app ptyp_to_pskl msubst_pskl msubst_lookup].
    destruct (α1 == α1) as [_ | Hne]; [ | contradiction ].
    eapply ad_partial_precise_psi_cong;
      [ apply ad_ppre_mono_refl; [ exact Hmτ | exact Hwfτ ]
      | clear - HΨi; fsetdec ].
  - (* ---------------------------- ∀◇ ------------------------------- *)
    (* [guess^TY] DROPS the universal ghost; the precision premise peels
       through the chain to the body *)
    cbn in Hsz.
    assert (HwfPi' : {{ Θ0 ⨟ empty ⊢ₚₛ Pi' }}a) by (inversion HwfPi; assumption).
    cbn [msubst_pskl] in Hpre.
    destruct (ad_ppre_tophole_subject_chain_inv HwfΘ Hpre eq_refl eq_refl Hmτ)
      as (τe & Hc & Hme & Hp').
    assert (Hwfe : a_wf_ptyp Θ τe)
      by (eapply a_def_chain_wf;
            [ exact Hc | exact HwfΘ | exact Hwfτ ]).
    assert (Hfte : ftvar_in_ptyp τe [<=] dom Θw `union` Δ)
      by (eapply a_def_chain_ftv_at;
            [ exact Hc | exact HwfΘw | exact Hdefs | exact Hftτ ]).
    destruct (IH Θ0 Θ Θw κ Δ Ψi τe Pi' ltac:(lia) HwfΘ HwfΘw Hmon Hdefs
                HwfPi' Hme Hwfe Hfte Hp' L)
      as (Ξ0 & A0 & κ0 & Hgu & Hfm & Hu & Hk & Hfr & HF & Hpr).
    exists Ξ0, A0, κ0.
    split; [ intros Θg Hsub; apply a_guess_mono__tophole;
             apply Hgu; exact Hsub | ].
    split; [ exact Hfm | ].
    split; [ exact Hu | ].
    split; [ exact Hk | ].
    split; [ exact Hfr | ].
    split; [ exact HF | ].
    eapply ad_ppre_chain_fold; [ exact Hc | exact Hpr ].
Qed.

(** The ORIGINAL interface, as the [ftv τ ⊆ dom Θw] instance: a counterpart
    already scoped inside [Θw] needs no Δ-slack.  Every pre-existing caller
    uses this one; only P6-Cv's SE-FlexR row needs the general form, because
    a ρ-DIRTY guess is [Θw]-scoped only up to [Δρ ⊆ Δ]. *)
Lemma a_guess_ty_witness_mono : forall n Θ0 Θ Θw κ Δ Ψi τ Pi,
  size_pskl Pi <= n ->
  {{ ⊢ Θ }}a ->
  {{ ⊢ Θw }}a ->
  (forall x b, binds x b Θw -> binds x b Θ) ->
  (forall α τ0, binds α (abind_flex_mono_def τ0) Θ ->
     binds α (abind_flex_mono_def τ0) Θw) ->
  {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a ->
  mono_ptyp τ ->
  a_wf_ptyp Θw τ ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (ptyp_to_uskl_syn τ) }}ad ->
  forall L, exists (Ξ : aenv) (A : ptyp) (κ' : metasubst),
    (forall Θg, ftvar_in_aenv Θg [<=] L -> a_guess_mono Θg Pi Ξ A) /\
    all_flex_mono Ξ /\
    uniq Ξ /\
    keys κ' = keys Ξ /\
    (forall α, α `in` dom Ξ -> α `notin` L) /\
    Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κ' /\
    {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κ' ++ κ) (ptyp_to_pskl A))
            ⊑ᵖ[ Ψi ] (ptyp_to_uskl_syn τ) }}ad.
Proof.
  intros n Θ0 Θ Θw κ Δ Ψi τ Pi Hsz HwfΘ HwfΘw Hmon Hdefs HwfPi Hmτ Hwfτ Hpre L.
  eapply a_guess_ty_witness_mono_gen;
    [ exact Hsz | exact HwfΘ | exact HwfΘw | exact Hmon | exact Hdefs
    | exact HwfPi | exact Hmτ
    | eapply a_wf_ptyp_weaken; [ exact Hmon | exact Hwfτ ]
    | (* the scope slack is unused: [τ] already sits inside [dom Θw] *)
      pose proof (a_wf_ptyp_ftv_dom Hwfτ) as Hd; clear - Hd; fsetdec
    | exact Hpre ].
Qed.

(* ⭐ THE CONCLUSION CARRIES THE κ-EXTENSION (2026-08-04).  The repaired
   SE-FlexR fires here — in the [P_i = P_i1 → P_i2], [P_0 = β̂] branch it is
   the ONLY applicable row (SE-Var wants a variable subject, SE-Arrow an
   arrow target) — and [guess^TY] of an arrow subject invents a flexible for
   every ghost inside it.  So the solve emits a block [Ξ] and its output is
   only interpretable under an EXTENDED metasubstitution, built by
   [a_guess_ty_witness_mono].

   ⚠️ UNLIKE the guess, the SOLVE IS NOT CONTEXT-GENERIC: SE-FlexR consults
   [Θ0] to decide HATTEDNESS ([a_flex_tvar]).  So the conclusion pins [Θ0]
   and takes the avoid-set [L] as a parameter with [ftvar_in_aenv Θ0 ⊆ L],
   which is what licenses the guess underneath.

   [a_wf_ptyp Θ τ] is a new premise; it is what the witness needs to close
   its ◇ case (docs/WF-SIDE-CONDITIONS.md — the paper requires the
   counterpart well-formed in prose). *)

(** Exchange of two rigid tvar conses — an [a_solve_sub_eq_ctx_change]
    instance (the judgement reads its context only through the freshness
    avoid-sets and the flex tests, and both are order-blind). *)
Lemma a_solve_sub_ctx_exchange : forall β1 β2 (Θ : aenv) m P Q Ξ P',
  {{ ((β1 ~ abind_tvar) ++ (β2 ~ abind_tvar) ++ Θ) ⊢ₛ P ≼[ m ] Q
     ⤳ Ξ ⨾ P' }}a ->
  {{ ((β2 ~ abind_tvar) ++ (β1 ~ abind_tvar) ++ Θ) ⊢ₛ P ≼[ m ] Q
     ⤳ Ξ ⨾ P' }}a.
Proof.
  intros * H.
  eapply (proj1 a_solve_sub_eq_ctx_change); [ exact H | | | ].
  - simpl. fsetdec.
  - intros α0 Hf. unfold a_flex_tvar, binds in *; simpl in *.
    destruct Hf as [Hb | [τ Hb]]; [ left | right; exists τ ]; tauto.
  - intros P0 Hf. inversion Hf; subst;
      match goal with
      | Hb : binds _ _ _ |- _ =>
          unfold binds in Hb; simpl in Hb;
          destruct Hb as [E | [E | HbIn]];
          [ discriminate E | discriminate E | ]
      end;
      [ apply a_flex__var | eapply a_flex__var_def ];
      unfold binds; simpl; right; right; exact HbIn.
Qed.

Arguments a_solve_sub_ctx_exchange {β1 β2 Θ m P Q Ξ P'}.
