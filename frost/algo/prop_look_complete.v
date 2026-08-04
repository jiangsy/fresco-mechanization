(** P6 — COMPLETENESS OF CONSTRAINT COLLECTION AND SOLVING (the "look"
    cluster [a_looksub]/[a_lookeq]/[a_solve_sub]/[a_solve_eq]/
    [a_solve_cstr]/[a_extract], algo/def_extra.v:287-498).

    Paper lemmas (docs/DESIGN-completeness-subtyping.md §7):
      P6-Cv  [a_solve_eq_complete_var]   consistency-proofs.tex:1180
      P6-Cs  [a_lookeq_solve_complete]   consistency-proofs.tex:920
      P6-Rv  [a_solve_sub_complete_var]  subtyping-proofs.tex:1696
      P6-Rs  [a_looksub_solve_complete]  subtyping-proofs.tex:2202
      P6-L   [a_extract_complete_gen]        subtyping-proofs.tex:2729

    THE ρ REPRESENTATION (design locked in DESIGN §7, 2026-07-24): the
    paper's ρ — a substitution from rigid type variables to decorated
    skeletons, with Ψ the solved tags it introduces — is mechanized as
    the RELATION [uskl_rho] "ψsub ⊒ρ[Δρ;Ψρ] ψa" (ψsub = ρ(ψa), Δρ = the
    replaced variables): same-constructor congruences + a REFL rule
    (identity-ρ call sites) + one replace-leaf [ψ'' ⊒ var α].  A relation
    rather than a function ([list (atom * uskl)] + msubst) NOT because of
    capture-avoidance — locally nameless + cofinite binders give that for
    free, as for κ — but because the main inductions run on the
    derivation over the SUBJECT ψsub, where each case needs, at its own
    position: (i) the copy-vs-replacement-leaf split (the
    [uskl_rho_*_l_inv] inversions); (ii) the image's tags Ψ'' AT THIS
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
    Θ's definition images ([rho_fresh]), and by the subject's ∀◇-shielded
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

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_skeleton.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo_sub.
Require Import src.frost.algo.def_decl_algo_sub_hyg.
Require Import src.frost.def_tags.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_consis_sound.
Require Import src.frost.algo.prop_consis_complete.
Require Import src.frost.algo.prop_mono_bridge.
Require Import src.frost.algo.prop_precise.
Require Import src.frost.algo.prop_decorate.
Require Import src.frost.algo.prop_pat_sub.
Require Import src.frost.algo.prop_consis_precise.
Require Import src.frost.algo.prop_swap.
Require Import src.frost.algo.prop_looksub.
Require Import src.frost.algo.prop_solve_sub.
Require Import src.frost.algo.prop_sub_complete.
Require Import src.frost.algo.prop_metasubst.

Set Implicit Arguments.

(* ===================================================================== *)
(*  The ρ relation  [ψsub ⊒ρ[Δρ;Ψρ] ψa]  (DESIGN §7).                      *)
(* ===================================================================== *)

Inductive uskl_rho (NM : a_sub_mode) (Θ : aenv)
  : atoms -> atoms -> uskl -> uskl -> Prop :=
| urho__refl : forall Δρ Ψρ R,
    lc_uskl R ->
    Ψρ [=] empty ->
    uskl_rho NM Θ Δρ Ψρ R R
| urho__leaf : forall Δρ Ψρ α Ψ'' ψ'',
    α `in` Δρ ->
    a_tags_sort NM Ψ'' ψ'' ->
    Θ ⨟ empty ⊢ₚₛᵃ ⌊ ψ'' ⌋ˢ ->
    Ψρ [=] Ψ'' ->
    uskl_rho NM Θ Δρ Ψρ ψ'' (uskl_var_f α)
| urho__arrow : forall Δρ Ψρ Ψ1 Ψ2 R1' R2' R1 R2,
    uskl_rho NM Θ Δρ Ψ1 R1' R1 ->
    uskl_rho NM Θ Δρ Ψ2 R2' R2 ->
    Ψρ [=] Ψ1 `union` Ψ2 ->
    uskl_rho NM Θ Δρ Ψρ (uskl_arrow R1' R2') (uskl_arrow R1 R2)
| urho__all_syn : forall L Δρ Ψρ R' R,
    (forall α, α `notin` L ->
       uskl_rho NM Θ Δρ Ψρ
         (open_uskl_wrt_uskl R' (uskl_var_f α))
         (open_uskl_wrt_uskl R (uskl_var_f α))) ->
    uskl_rho NM Θ Δρ Ψρ (uskl_all_syn R') (uskl_all_syn R)
| urho__all_etag : forall L Δρ Ψρ ε R' R,
    (forall α, α `notin` L ->
       uskl_rho NM Θ Δρ Ψρ
         (open_uskl_wrt_uskl R' (uskl_var_f α))
         (open_uskl_wrt_uskl R (uskl_var_f α))) ->
    uskl_rho NM Θ Δρ Ψρ (uskl_all_etag ε R') (uskl_all_etag ε R)
| urho__tophole : forall Δρ Ψρ R' R,
    uskl_rho NM Θ Δρ Ψρ R' R ->
    uskl_rho NM Θ Δρ Ψρ (uskl_tophole R') (uskl_tophole R)
| urho__topholeg : forall Δρ Ψρ R' R,
    uskl_rho NM Θ Δρ Ψρ R' R ->
    uskl_rho NM Θ Δρ Ψρ (uskl_topholeg R') (uskl_topholeg R).

(** Re-tag under set equality. *)
Lemma uskl_rho_psi_cong : forall NM Θ Δρ Ψρ R' R,
  uskl_rho NM Θ Δρ Ψρ R' R ->
  forall Ψρ', Ψρ [=] Ψρ' ->
  uskl_rho NM Θ Δρ Ψρ' R' R.
Proof.
  intros NM Θ Δρ Ψρ R' R H; induction H; intros Ψρ' Heq.
  - apply urho__refl; [ assumption | fsetdec ].
  - eapply urho__leaf; [ exact H | exact H0 | exact H1 | fsetdec ].
  - eapply urho__arrow; [ exact H | exact H0 | fsetdec ].
  - eapply urho__all_syn with (L := L); intros α Hα; eauto.
  - eapply urho__all_etag with (L := L); intros α Hα; eauto.
  - apply urho__tophole; eauto.
  - apply urho__topholeg; eauto.
Qed.

(** Widen the replaced-variable bound. *)
Lemma uskl_rho_delta_mono : forall NM Θ Δρ Ψρ R' R,
  uskl_rho NM Θ Δρ Ψρ R' R ->
  forall Δρ', Δρ [<=] Δρ' ->
  uskl_rho NM Θ Δρ' Ψρ R' R.
Proof.
  intros NM Θ Δρ Ψρ R' R H; induction H; intros Δρ' Hsub.
  - apply urho__refl; assumption.
  - eapply urho__leaf; [ | exact H0 | exact H1 | exact H2 ]. fsetdec.
  - eapply urho__arrow; [ apply IHuskl_rho1 | apply IHuskl_rho2 | ];
      assumption.
  - eapply urho__all_syn with (L := L); intros α Hα; eauto.
  - eapply urho__all_etag with (L := L); intros α Hα; eauto.
  - apply urho__tophole; eauto.
  - apply urho__topholeg; eauto.
Qed.

(** The subject's tags are bounded by the replacement tags plus ψa's. *)
Lemma uskl_rho_ftag_sub : forall NM Θ Δρ Ψρ R' R,
  uskl_rho NM Θ Δρ Ψρ R' R ->
  ftag_in_uskl R' [<=] Ψρ `union` ftag_in_uskl R.
Proof.
  intros NM Θ Δρ Ψρ R' R H; induction H; simpl; try fsetdec.
  - (* leaf: tags of the image are exactly Ψ'' *)
    pose proof (d_tags_skl_ftag (a_tags_sort_d_tags H0)) as Ht.
    fsetdec.
  - (* all_syn *)
    pick fresh α for L.
    pose proof (H0 α ltac:(fsetdec)) as Hα.
    pose proof (ftag_in_uskl_open_var R' α).
    pose proof (ftag_in_uskl_open_var R α).
    fsetdec.
  - (* all_etag *)
    pick fresh α for L.
    pose proof (H0 α ltac:(fsetdec)) as Hα.
    pose proof (ftag_in_uskl_open_var R' α).
    pose proof (ftag_in_uskl_open_var R α).
    fsetdec.
Qed.

(* ===================================================================== *)
(*  Inversion of [uskl_rho] BY SUBJECT SHAPE (P6-Cv/Rv consume these: the   *)
(*  induction is on the [ad_pat_consis]/[ad_pat_sub] derivation of the      *)
(*  ρ(ψa)-SUBJECT, so each case fixes the subject shape and reads off ψa's  *)
(*  shape — either a matching structural congruence / reflexive copy, or a  *)
(*  ρ-LEAF [ψa = var α] with the subject as X's image).                     *)
(* ===================================================================== *)

(** [ψa = var α] with the subject as X's ρ-image (the leaf disjunct). *)
Definition rho_leaf (NM : a_sub_mode) (Θ : aenv) (Δρ Ψρ : atoms)
    (R : uskl) (ψa : uskl) : Prop :=
  exists α Ψ'', ψa = uskl_var_f α /\ α `in` Δρ /\
    a_tags_sort NM Ψ'' R /\ Θ ⨟ empty ⊢ₚₛᵃ ⌊ R ⌋ˢ /\ Ψρ [=] Ψ''.

(* [andsplit] splits ONLY [/\] goals — plain [split] would enter the
   single-constructor [a_tags_sort] inside [rho_leaf]. *)
Local Ltac rho_andsplit := repeat match goal with |- _ /\ _ => split end.
Local Ltac rho_refl_tac := left; split; [ reflexivity | assumption ].

Lemma uskl_rho_arrow_l_inv : forall NM Θ Δρ Ψρ R1' R2' ψa,
  uskl_rho NM Θ Δρ Ψρ (uskl_arrow R1' R2') ψa ->
  (ψa = uskl_arrow R1' R2' /\ Ψρ [=] empty)
  \/ rho_leaf NM Θ Δρ Ψρ (uskl_arrow R1' R2') ψa
  \/ (exists R1 R2 Ψ1 Ψ2, ψa = uskl_arrow R1 R2 /\
        uskl_rho NM Θ Δρ Ψ1 R1' R1 /\ uskl_rho NM Θ Δρ Ψ2 R2' R2 /\
        Ψρ [=] Ψ1 `union` Ψ2).
Proof.
  intros NM Θ Δρ Ψρ R1' R2' ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; left; exists α, Ψ''; rho_andsplit; try reflexivity; assumption.
  - right; right; exists R1, R2, Ψ1, Ψ2; rho_andsplit;
      try reflexivity; assumption.
Qed.

Lemma uskl_rho_unit_l_inv : forall NM Θ Δρ Ψρ ψa,
  uskl_rho NM Θ Δρ Ψρ uskl_unit ψa ->
  (ψa = uskl_unit /\ Ψρ [=] empty) \/ rho_leaf NM Θ Δρ Ψρ uskl_unit ψa.
Proof.
  intros NM Θ Δρ Ψρ ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; exists α, Ψ''; rho_andsplit; try reflexivity; assumption.
Qed.

Lemma uskl_rho_var_l_inv : forall NM Θ Δρ Ψρ β ψa,
  uskl_rho NM Θ Δρ Ψρ (uskl_var_f β) ψa ->
  (ψa = uskl_var_f β /\ Ψρ [=] empty) \/ rho_leaf NM Θ Δρ Ψρ (uskl_var_f β) ψa.
Proof.
  intros NM Θ Δρ Ψρ β ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; exists α, Ψ''; rho_andsplit; try reflexivity; assumption.
Qed.

Lemma uskl_rho_hole_l_inv : forall NM Θ Δρ Ψρ ψa,
  uskl_rho NM Θ Δρ Ψρ uskl_hole ψa ->
  (ψa = uskl_hole /\ Ψρ [=] empty) \/ rho_leaf NM Θ Δρ Ψρ uskl_hole ψa.
Proof.
  intros NM Θ Δρ Ψρ ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; exists α, Ψ''; rho_andsplit; try reflexivity; assumption.
Qed.

Lemma uskl_rho_holeg_l_inv : forall NM Θ Δρ Ψρ ψa,
  uskl_rho NM Θ Δρ Ψρ uskl_holeg ψa ->
  (ψa = uskl_holeg /\ Ψρ [=] empty) \/ rho_leaf NM Θ Δρ Ψρ uskl_holeg ψa.
Proof.
  intros NM Θ Δρ Ψρ ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; exists α, Ψ''; rho_andsplit; try reflexivity; assumption.
Qed.

Lemma uskl_rho_tophole_l_inv : forall NM Θ Δρ Ψρ R' ψa,
  uskl_rho NM Θ Δρ Ψρ (uskl_tophole R') ψa ->
  (ψa = uskl_tophole R' /\ Ψρ [=] empty)
  \/ rho_leaf NM Θ Δρ Ψρ (uskl_tophole R') ψa
  \/ (exists R, ψa = uskl_tophole R /\ uskl_rho NM Θ Δρ Ψρ R' R).
Proof.
  intros NM Θ Δρ Ψρ R' ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; left; exists α, Ψ''; rho_andsplit; try reflexivity; assumption.
  - right; right; exists R; split; [ reflexivity | assumption ].
Qed.

Lemma uskl_rho_topholeg_l_inv : forall NM Θ Δρ Ψρ R' ψa,
  uskl_rho NM Θ Δρ Ψρ (uskl_topholeg R') ψa ->
  (ψa = uskl_topholeg R' /\ Ψρ [=] empty)
  \/ rho_leaf NM Θ Δρ Ψρ (uskl_topholeg R') ψa
  \/ (exists R, ψa = uskl_topholeg R /\ uskl_rho NM Θ Δρ Ψρ R' R).
Proof.
  intros NM Θ Δρ Ψρ R' ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; left; exists α, Ψ''; rho_andsplit; try reflexivity; assumption.
  - right; right; exists R; split; [ reflexivity | assumption ].
Qed.

Lemma uskl_rho_all_syn_l_inv : forall NM Θ Δρ Ψρ R' ψa,
  uskl_rho NM Θ Δρ Ψρ (uskl_all_syn R') ψa ->
  (ψa = uskl_all_syn R' /\ Ψρ [=] empty)
  \/ rho_leaf NM Θ Δρ Ψρ (uskl_all_syn R') ψa
  \/ (exists L R, ψa = uskl_all_syn R /\
        forall α, α `notin` L ->
          uskl_rho NM Θ Δρ Ψρ (open_uskl_wrt_uskl R' (uskl_var_f α))
                              (open_uskl_wrt_uskl R (uskl_var_f α))).
Proof.
  intros NM Θ Δρ Ψρ R' ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; left; exists α, Ψ''; rho_andsplit; try reflexivity; assumption.
  - right; right; exists L, R; split; [ reflexivity | eassumption ].
Qed.

Lemma uskl_rho_all_etag_l_inv : forall NM Θ Δρ Ψρ ε R' ψa,
  uskl_rho NM Θ Δρ Ψρ (uskl_all_etag ε R') ψa ->
  (ψa = uskl_all_etag ε R' /\ Ψρ [=] empty)
  \/ rho_leaf NM Θ Δρ Ψρ (uskl_all_etag ε R') ψa
  \/ (exists L R, ψa = uskl_all_etag ε R /\
        forall α, α `notin` L ->
          uskl_rho NM Θ Δρ Ψρ (open_uskl_wrt_uskl R' (uskl_var_f α))
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
Definition rho_fresh (Δρ : atoms) (Θ : aenv) (κ : metasubst) : Prop :=
  forall α0, α0 `in` Δρ ->
    binds α0 abind_tvar Θ /\
    (forall p, In p κ -> α0 `notin` ftvar_in_ptyp (snd p)) /\
    (forall α τ, binds α (abind_flex_mono_def τ) Θ ->
       α0 `notin` ftvar_in_ptyp τ).

(** ρ-freshness survives a RIGID context extension: the ∀ rows of P6-Cs /
    P6-Ss run their IH at [Θ,β], and a rigid entry adds neither a κ-image
    nor a definition, so the only conjunct that moves is the [binds]
    one — monotonically. *)
Lemma rho_fresh_weaken_tvar : forall Δρ Θ κ β,
  rho_fresh Δρ Θ κ ->
  rho_fresh Δρ ((β ~ abind_tvar) ++ Θ) κ.
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
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  forall α', ψ = uskl_var_f α' ->
  a_wf_aenv Θ ->
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
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  forall α', ψ = uskl_var_f α' ->
  a_wf_aenv Θ ->
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
   [a_solve_sub_eq_weaken_mid_flex_size] (prop_look_complete_cstr.v). *)
(* ⭐ THE AVOID-SET IS [ftvar_in_aenv], AND [dom] IS NO LONGER A CONDITION
   (2026-08-04).  SE-FlexR now calls [guess^TY], whose freshness is against
   [ftvar_in_aenv Θ] — a flexible's PAYLOAD may mention a name that is in no
   domain — so the five binder rows were strengthened to the same set
   (algo/def_extra.v).  After that NOTHING in the solve cluster reads [dom Θ],
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

Lemma a_flex_tvar_strip_tvar : forall b Θ α,
  a_flex_tvar ((b ~ abind_tvar) ++ Θ) α -> a_flex_tvar Θ α.
Proof.
  intros b Θ α [Hb | [τ Hb]];
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq Habs] | Hb'];
    solve [ discriminate Habs | left; exact Hb' | right; exists τ; exact Hb' ].
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
  (forall Θ m P P3 Ξ P', Θ ⊢ₛ P ≼[ m ] P3 ⤳ Ξ ⨾ P' ->
     forall Θ',
     ftvar_in_aenv Θ' [<=] ftvar_in_aenv Θ ->
     (forall α, a_flex_tvar Θ α -> a_flex_tvar Θ' α) ->
     (forall P0, a_flex Θ' P0 -> a_flex Θ P0) ->
     Θ' ⊢ₛ P ≼[ m ] P3 ⤳ Ξ ⨾ P') /\
  (forall Θ P P3 Ξ P', Θ ⊢ₑ P ∼ P3 ⤳ Ξ ⨾ P' ->
     forall Θ',
     ftvar_in_aenv Θ' [<=] ftvar_in_aenv Θ ->
     (forall α, a_flex_tvar Θ α -> a_flex_tvar Θ' α) ->
     (forall P0, a_flex Θ' P0 -> a_flex Θ P0) ->
     Θ' ⊢ₑ P ∼ P3 ⤳ Ξ ⨾ P').
Proof.
  apply a_solve_sub_eq_mutind; intros;
    (* binder rows FIRST — [econstructor; eauto] would mis-pick for them *)
    try solve [ solve_ctx_change_binder ];
    (* SS-ForallR: the output passes THROUGH, so [econstructor] leaves the
       witness an evar — name it *)
    try solve
      [ match goal with
        | Hfr : ?b `notin` _ |- _ ⊢ₛ _ ≼[ _ ] pskl_all_syn _ ⤳ _ ⨾ _ =>
            apply a_solve_sub__forall_r with (β := b); [ | ];
            [ match goal with Hf : ftvar_in_aenv _ [<=] _ |- _ =>
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
  ((β ~ abind_tvar) ++ Θ0) ⊢ₑ P ∼ P3 ⤳ Ξ ⨾ P' ->
  Θ0 ⊢ₑ P ∼ P3 ⤳ Ξ ⨾ P'.
Proof.
  intros β Θ0 P P3 Ξ P' H.
  eapply (proj2 a_solve_sub_eq_ctx_change); [ exact H | | | ].
  - simpl. fsetdec.
  - intros α Hft. eapply a_flex_tvar_strip_tvar; exact Hft.
  - intros P0 Hf. apply (a_flex_cons β abind_tvar); exact Hf.
Qed.

Lemma a_solve_sub_strengthen_tvar : forall β Θ0 m P P3 Ξ P',
  ((β ~ abind_tvar) ++ Θ0) ⊢ₛ P ≼[ m ] P3 ⤳ Ξ ⨾ P' ->
  Θ0 ⊢ₛ P ≼[ m ] P3 ⤳ Ξ ⨾ P'.
Proof.
  intros β Θ0 m P P3 Ξ P' H.
  eapply (proj1 a_solve_sub_eq_ctx_change); [ exact H | | | ].
  - simpl. fsetdec.
  - intros α Hft. eapply a_flex_tvar_strip_tvar; exact Hft.
  - intros P0 Hf. apply (a_flex_cons β abind_tvar); exact Hf.
Qed.

(* ===================================================================== *)
(*  RESTART NOTE (2026-08-04) — [a_solve_eq_weaken_tvar{,_size}] DELETED.  *)
(*                                                                        *)
(*  It claimed: a rigid-tvar CONS weakens an eq-solve,                     *)
(*    [Θ0 ⊢ₑ P ∼ P3 ⤳ Ξ ⨾ P'  ⟹  ((β ~ tvar) ++ Θ0) ⊢ₑ … ]              *)
(*  (EQ half only — every eq-∀ rule CLOSES its output, so a colliding      *)
(*  witness can be re-freshened with the output unchanged, whereas         *)
(*  SS-ForallR PINS its leaked witness and the sub twin is FALSE).         *)
(*                                                                        *)
(*  ⭐ IT HAS NO CONSUMERS, and had none at the pre-repair baseline        *)
(*  [d5f9169] either.  What the tree actually calls is the MID-BLOCK       *)
(*  twin [a_solve_sub_eq_weaken_mid_flex_size]                            *)
(*  (prop_look_complete_cstr.v, P6-Cs), which inserts an [all_flex_mono]   *)
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

(** Rename preserves non-flexibility when both names are fresh from Θ. *)
Lemma a_non_flex_rename : forall Θ P α' β,
  α' `notin` dom Θ -> β `notin` dom Θ ->
  a_non_flex Θ P ->
  a_non_flex Θ (subst_pskl_in_pskl (pskl_var_f β) α' P).
Proof.
  intros Θ P α' β Hα Hβ [Hlc Hnf].
  split.
  - apply subst_pskl_in_pskl_lc_pskl; [ exact Hlc | constructor ].
  - intros Hf.
    destruct P; simpl in Hf; try solve [ inversion Hf ].
    match type of Hf with context [ if ?e then _ else _ ] =>
      destruct e end.
    + inversion Hf; subst;
        match goal with Hb : binds _ _ Θ |- _ =>
          apply binds_In in Hb; contradiction end.
    + apply Hnf; exact Hf.
Qed.

(** Rename preserves guardedness ([var β] is guarded). *)
Lemma guarded_pskl_rename : forall P α β,
  guarded_pskl P ->
  guarded_pskl (subst_pskl_in_pskl (pskl_var_f β) α P).
Proof.
  intros P α β Hg; inversion Hg; subst; simpl.
  - constructor.
  - destruct_if;
      constructor.
  - constructor;
      (apply subst_pskl_in_pskl_lc_pskl;
        [ assumption | apply lc_pskl_var_f ]).
Qed.

(* [a_solve_sub_eq_rename] REPLACED by [a_solve_sub_rename_var] /
   [a_solve_eq_rename_var] (prop_solve_sub.v, freshness campaign): the
   asymmetric statement — target-fresh incl. the OUTPUT (SS-ForallR's leak
   pins its witness), source only dodging [dom Θ]. *)

(* ===================================================================== *)
(*  Shape/tags helpers for the special cases (P0 = □; synthesized Q).      *)
(* ===================================================================== *)

(** Syn-paintings are synthesized skeletons. *)
Lemma is_sskl_pskl_to_bskl_syn : forall P,
  lc_pskl P -> is_sskl (pskl_to_bskl_syn P).
Proof.
  intros P Hlc; induction Hlc; simpl; try solve [ constructor; auto ].
  apply is_sskl__all with (L := {}).
  intros α _. rewrite <- pskl_to_bskl_syn_open. auto.
Qed.

(** Refining the hole yields a synthesized skeleton (paper: "by inversion
    on the refinement premise, Q is a synthesised skeleton"). *)
Lemma ad_refine_syn_hole_sskl : forall Θ Δ Qh Q,
  Θ ⨟ Δ ⊢ᵣᵃ Qh ⊳ Q ->
  Qh = bskl_hole ->
  is_sskl Q.
Proof.
  intros Θ Δ Qh Q H; induction H; intros Heq; try discriminate Heq.
  - (* hole *)
    apply is_sskl_pskl_to_bskl_syn.
    eapply a_wf_pskl_lc; eassumption.
  - (* flex_r *)
    auto with frost.
Qed.

(** Consistency against a synthesized target solves no tags (the only
    tag-consuming rule targets [all_inh]). *)
Lemma ad_pat_consis_sskl_tags : forall Ψ Θ R Q,
  Ψ ⨟ Θ ⊢ₛᵃ R ∼ Q ->
  a_wf_aenv Θ ->
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
      apply (H0 α ltac:(fsetdec));
      [ apply a_wf_aenv__tvar; [ fsetdec | exact Hwf ]
      | apply HskB; fsetdec ]
    end.
  - (* forall_syn *)
    inversion Hsk; subst.
    match goal with HskB : forall α, α `notin` ?L0 -> is_sskl _ |- _ =>
      pick fresh α for (L `union` L0 `union` dom Θ);
      apply (H0 α ltac:(fsetdec));
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
    apply lc_ptyp_to_pskl.
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
    pose proof (ftvar_in_ptyp_to_pskl (msubst_lookup κ β)) as Hp.
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
  { pose proof (ftvar_in_ptyp_to_pskl (msubst_lookup κ β)) as Hp.
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

Lemma p6_leaf_var : forall NM Θ κ Pi Δ α' Ψ' Ψi Ψna,
  a_wf_aenv Θ ->
  a_tags_sort NM Ψ' (uskl_var_f α') ->
  Ψi [<=] Ψ' ->
  Ψna [<=] Ψ' ->
  α' `in` Δ ->
  binds α' abind_tvar Θ ->
  (forall p, In p κ -> α' `notin` ftvar_in_ptyp (snd p)) ->
  (forall α τ, binds α (abind_flex_mono_def τ) Θ ->
     α' `notin` ftvar_in_ptyp τ) ->
  α' `notin` pskl_shielded_ftv Pi ->
  Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (uskl_var_f α') ->
  Pi = pskl_var_f α' /\
  Ψi [=] empty /\
  Ψna [=] empty /\
  Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi `union` Ψna ] (uskl_var_f α').
Proof.
  intros NM Θ κ Pi Δ α' Ψ' Ψi Ψna
    Hwf Htag HΨi HΨna HαΔ HXb Hκav Hdef Hsh Hpre.
  assert (Hshκ : α' `notin` pskl_shielded_ftv (msubst_pskl κ Pi))
    by (apply msubst_pskl_shielded_avoid; assumption).
  destruct (ad_ppre_delta_var_inv Hpre eq_refl Hwf HαΔ HXb Hdef Hshκ)
    as [Heqm HΨie].
  assert (HeqPi : Pi = pskl_var_f α')
    by (eapply msubst_pskl_var_inv; eassumption).
  assert (HΨ'e : Ψ' [=] empty)
    by (exact (d_tags_skl_var_inv (a_tags_sort_d_tags Htag))).
  split; [ exact HeqPi | ].
  split; [ exact HΨie | ].
  split; [ clear - HΨna HΨ'e; fsetdec | ].
  rewrite Heqm.
  apply ad_ppre__var; [ clear - HΨie HΨna HΨ'e; fsetdec | left; exact HαΔ ].
Qed.

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
    carries [nonghost_pskl] (algo/def_extra.v): under the repaired row
    [guess^TY(◇)] invents a FRESH flexible, so [◇ ∼ α̂] would ALSO derive
    [⤳ (α̂1 ~ flex) ⨾ α̂1].  The reference implementation never takes that
    branch — its match puts SolE-GhostL first — and neither does this. *)
Lemma a_solve_eq_hole_subject_inv : forall Θ P Ξ P',
  Θ ⊢ₑ pskl_hole ∼ P ⤳ Ξ ⨾ P' ->
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
(*  Inversion of [uskl_rho] BY TARGET SHAPE — the mirror family            *)
(*                                                                        *)
(*  P6-Cs (and P6-Ss's Arrow / ∀ rows) dispatch on the IDEAL subject       *)
(*  [R'], not on the derivation, so what they need is the opposite         *)
(*  reading: the TARGET's shape is known and the ρ-IMAGE's has to be read  *)
(*  off.  That direction is strictly simpler than [_l_inv] — for every     *)
(*  NON-VARIABLE target only [urho__refl] and the matching congruence      *)
(*  apply ([urho__leaf] demands a variable target) — and the two collapse: *)
(*  [urho__refl] carries [lc_uskl], so its components are themselves       *)
(*  reflexive ρ-images at [Ψρ = ∅].  Hence a SINGLE congruence conclusion, *)
(*  with no [rho_leaf] disjunct to dispatch.                              *)
(* ===================================================================== *)

Lemma uskl_rho_unit_r_inv : forall NM Θ Δρ Ψρ R',
  uskl_rho NM Θ Δρ Ψρ R' uskl_unit ->
  R' = uskl_unit /\ Ψρ [=] empty.
Proof.
  intros NM Θ Δρ Ψρ R' H; inversion H; subst;
    split; [ reflexivity | assumption ].
Qed.

Lemma uskl_rho_hole_r_inv : forall NM Θ Δρ Ψρ R',
  uskl_rho NM Θ Δρ Ψρ R' uskl_hole ->
  R' = uskl_hole /\ Ψρ [=] empty.
Proof.
  intros NM Θ Δρ Ψρ R' H; inversion H; subst;
    split; [ reflexivity | assumption ].
Qed.

Lemma uskl_rho_holeg_r_inv : forall NM Θ Δρ Ψρ R',
  uskl_rho NM Θ Δρ Ψρ R' uskl_holeg ->
  R' = uskl_holeg /\ Ψρ [=] empty.
Proof.
  intros NM Θ Δρ Ψρ R' H; inversion H; subst;
    split; [ reflexivity | assumption ].
Qed.

Lemma uskl_rho_arrow_r_inv : forall NM Θ Δρ Ψρ R' ψ1 ψ2,
  uskl_rho NM Θ Δρ Ψρ R' (uskl_arrow ψ1 ψ2) ->
  exists R1' R2' Ψ1 Ψ2,
    R' = uskl_arrow R1' R2' /\
    uskl_rho NM Θ Δρ Ψ1 R1' ψ1 /\ uskl_rho NM Θ Δρ Ψ2 R2' ψ2 /\
    Ψρ [=] Ψ1 `union` Ψ2.
Proof.
  intros NM Θ Δρ Ψρ R' ψ1 ψ2 H; inversion H; subst.
  - (* refl : lc splits, so each component is reflexive at ∅ *)
    match goal with Hlc : lc_uskl (uskl_arrow _ _) |- _ =>
      inversion Hlc; subst end.
    exists ψ1, ψ2, empty, empty; rho_andsplit;
      [ reflexivity
      | apply urho__refl; [ assumption | clear; fsetdec ]
      | apply urho__refl; [ assumption | clear; fsetdec ]
      | clear - H1; fsetdec ].
  - exists R1', R2', Ψ1, Ψ2; rho_andsplit;
      try reflexivity; assumption.
Qed.

Lemma uskl_rho_tophole_r_inv : forall NM Θ Δρ Ψρ R' ψ,
  uskl_rho NM Θ Δρ Ψρ R' (uskl_tophole ψ) ->
  exists R0, R' = uskl_tophole R0 /\ uskl_rho NM Θ Δρ Ψρ R0 ψ.
Proof.
  intros NM Θ Δρ Ψρ R' ψ H; inversion H; subst.
  - match goal with Hlc : lc_uskl (uskl_tophole _) |- _ =>
      inversion Hlc; subst end.
    exists ψ; split;
      [ reflexivity | apply urho__refl; assumption ].
  - exists R'0; split; [ reflexivity | assumption ].
Qed.

Lemma uskl_rho_topholeg_r_inv : forall NM Θ Δρ Ψρ R' ψ,
  uskl_rho NM Θ Δρ Ψρ R' (uskl_topholeg ψ) ->
  exists R0, R' = uskl_topholeg R0 /\ uskl_rho NM Θ Δρ Ψρ R0 ψ.
Proof.
  intros NM Θ Δρ Ψρ R' ψ H; inversion H; subst.
  - match goal with Hlc : lc_uskl (uskl_topholeg _) |- _ =>
      inversion Hlc; subst end.
    exists ψ; split;
      [ reflexivity | apply urho__refl; assumption ].
  - exists R'0; split; [ reflexivity | assumption ].
Qed.

Lemma uskl_rho_all_syn_r_inv : forall NM Θ Δρ Ψρ R' ψ,
  uskl_rho NM Θ Δρ Ψρ R' (uskl_all_syn ψ) ->
  exists L R0, R' = uskl_all_syn R0 /\
    forall α, α `notin` L ->
      uskl_rho NM Θ Δρ Ψρ (open_uskl_wrt_uskl R0 (uskl_var_f α))
                          (open_uskl_wrt_uskl ψ (uskl_var_f α)).
Proof.
  intros NM Θ Δρ Ψρ R' ψ H; inversion H; subst.
  - match goal with Hlc : lc_uskl (uskl_all_syn _) |- _ =>
      inversion Hlc; subst end.
    exists empty, ψ; split; [ reflexivity | ].
    intros α Hα; apply urho__refl; [ auto | assumption ].
  - exists L, R'0; split; [ reflexivity | eassumption ].
Qed.

Lemma uskl_rho_all_etag_r_inv : forall NM Θ Δρ Ψρ R' ε ψ,
  uskl_rho NM Θ Δρ Ψρ R' (uskl_all_etag ε ψ) ->
  exists L R0, R' = uskl_all_etag ε R0 /\
    forall α, α `notin` L ->
      uskl_rho NM Θ Δρ Ψρ (open_uskl_wrt_uskl R0 (uskl_var_f α))
                          (open_uskl_wrt_uskl ψ (uskl_var_f α)).
Proof.
  intros NM Θ Δρ Ψρ R' ε ψ H; inversion H; subst.
  - match goal with Hlc : lc_uskl (uskl_all_etag _ _) |- _ =>
      inversion Hlc; subst end.
    exists empty, ψ; split; [ reflexivity | ].
    intros α Hα; apply urho__refl; [ auto | assumption ].
  - exists L, R'0; split; [ reflexivity | eassumption ].
Qed.

(** The VARIABLE target is the one shape that keeps the leaf disjunct — it
    is the only place ρ actually does anything. *)
Lemma uskl_rho_var_r_inv : forall NM Θ Δρ Ψρ R' β,
  uskl_rho NM Θ Δρ Ψρ R' (uskl_var_f β) ->
  (R' = uskl_var_f β /\ Ψρ [=] empty)
  \/ (β `in` Δρ /\ a_tags_sort NM Ψρ R' /\ Θ ⨟ empty ⊢ₚₛᵃ ⌊ R' ⌋ˢ).
Proof.
  intros NM Θ Δρ Ψρ R' β H; inversion H; subst.
  - left; split; [ reflexivity | assumption ].
  - right; rho_andsplit;
      [ assumption
      | eapply a_tags_sort_psi_cong; [ eassumption | fsetdec ]
      | assumption ].
Qed.

Lemma uskl_rho_is_tskl : forall NM Θ Δρ Ψρ R' R,
  uskl_rho NM Θ Δρ Ψρ R' R ->
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
      apply is_tskl__all_etag with (L := L `union` L1); intros α Hα;
      apply H0; [ clear - Hα; solve_notin | apply Hb; clear - Hα; solve_notin ]
    end.
  - (* ∀◇ : not a decorated shape *) inversion Ht.
  - inversion Ht; subst; apply is_tskl__topholeg; auto.
Qed.

Lemma uskl_rho_ftv_subject_bound : forall NM Θ Δρ Ψρ R' R,
  uskl_rho NM Θ Δρ Ψρ R' R ->
  ftvar_in_uskl R' [<=] ftvar_in_uskl R `union` dom Θ.
Proof.
  intros NM Θ Δρ Ψρ R' R H; induction H; cbn [ftvar_in_uskl];
    try solve [ clear; fsetdec | clear - IHuskl_rho; fsetdec
              | clear - IHuskl_rho1 IHuskl_rho2; fsetdec ].
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
    ever acts at a [Δρ]-variable ([urho__leaf] is the only non-congruence
    rule), so an ideal that mentions no [Δρ]-variable is its own image.

    This is what P6-Ss Phase B needs: the ftv-𝒞 conclusion must survive a
    Sub-ForallR, whose fresh binder β enters the DERIVATION's context — so a
    bound naming [dom Θ] (or P6-Cs's [dom Θs], the ρ-images' scope, which a
    nested Sub-ForallL's guess drags β into) readmits exactly the binder being
    stripped.  Under the apartness premise no context appears at all.
    P6-Cs keeps Δρ constant and never moves ψa, and P6-Ss's main induction
    picks every Sub-ForallL binder fresh for ψa, so both preserve it.
    See docs/DESIGN-completeness-subtyping.md §8 (h). *)
Lemma uskl_rho_ftv_apart : forall NM Θ Δρ Ψρ R' R,
  uskl_rho NM Θ Δρ Ψρ R' R ->
  (ftvar_in_uskl R) ∩ Δρ [=] empty ->
  ftvar_in_uskl R' [<=] ftvar_in_uskl R.
Proof.
  intros NM Θ Δρ Ψρ R' R H; induction H; intros Hap; cbn [ftvar_in_uskl] in *;
    try solve [ clear; fsetdec
              | apply IHuskl_rho; clear - Hap; fsetdec
              | (* arrow *)
                pose proof (IHuskl_rho1 ltac:(clear - Hap; fsetdec));
                pose proof (IHuskl_rho2 ltac:(clear - Hap; fsetdec));
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
                  ltac:(clear - Hap Hup Fr; fsetdec)) as Hα.
    clear - Hα Hlo Hup Fr; fsetdec.
  - (* ∀^ε *)
    pick fresh α for (L `union` Δρ `union` ftvar_in_uskl R'
                        `union` ftvar_in_uskl R).
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R' (uskl_var_f α)) as Hlo.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R (uskl_var_f α)) as Hup.
    cbn [ftvar_in_uskl] in Hup.
    pose proof (H0 α ltac:(clear - Fr; solve_notin)
                  ltac:(clear - Hap Hup Fr; fsetdec)) as Hα.
    clear - Hα Hlo Hup Fr; fsetdec.
Qed.

Lemma uskl_rho_weaken : forall NM Θ Δρ Ψρ R' R,
  uskl_rho NM Θ Δρ Ψρ R' R ->
  forall Θ', (forall x b, binds x b Θ -> binds x b Θ') ->
  uskl_rho NM Θ' Δρ Ψρ R' R.
Proof.
  intros NM Θ Δρ Ψρ R' R H; induction H; intros Θ' Hmon.
  - apply urho__refl; assumption.
  - eapply urho__leaf; [ exact H | exact H0 | | exact H2 ].
    eapply a_wf_pskl_weaken; eassumption.
  - eapply urho__arrow; eauto.
  - eapply urho__all_syn with (L := L); eauto.
  - eapply urho__all_etag with (L := L); eauto.
  - apply urho__tophole; eauto.
  - apply urho__topholeg; eauto.
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
  Θfull ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  forall α1 Θ1 Θ0,
  Θfull = Θ1 ++ (α1 ~ abind_tvar) ++ Θ0 ->
  α1 `in` Δ ->
  (Θ1 ++ Θ0) ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ.
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
  ((α1 ~ abind_tvar) ++ Θ0) ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  α1 `in` Δ ->
  Θ0 ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ.
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
  Θs ⨟ Δ ⊢ₚₛᵃ P ->
  forall Ξ β Θ, Θs = Ξ ++ (β ~ abind_tvar) ++ Θ ->
  β `notin` ftvar_in_pskl P ->
  (Ξ ++ Θ) ⨟ Δ ⊢ₚₛᵃ P.
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
  Θs ⨟ Δ ⊢ₚₛᵃ P ->
  forall Ξ β Θ, Θs = Ξ ++ (β ~ abind_tvar) ++ Θ ->
  β `in` Δ ->
  β `notin` pskl_shielded_ftv P ->
  (Ξ ++ Θ) ⨟ Δ ⊢ₚₛᵃ P.
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
  Θ ⨟ Δ ⊢ₚₛᵃ P -> pskl_shielded_ftv P [<=] dom Θ.
Proof.
  intros Θ Δ P H; induction H; cbn [pskl_shielded_ftv];
    try solve [ clear; fsetdec | clear - IHa_wf_pskl1 IHa_wf_pskl2; fsetdec ].
  - (* ∀ : the body's shielded set only GROWS when opened, so the cofinite
       premise's bound already covers it *)
    pick fresh α for (L `union` dom Θ `union` ftvar_in_pskl P `union` Δ).
    pose proof (H0 α ltac:(clear - Fr; fsetdec)) as Hb.
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
  Θ ⨟ Δ ⊢ₚₛᵃ P -> (Ξ ++ Θ) ⨟ Δ ⊢ₚₛᵃ P.
Proof.
  intros Ξ Θ Δ P H.
  eapply a_wf_pskl_weaken; [ | exact H ].
  intros x b Hb. apply binds_app_3; exact Hb.
Qed.

Lemma a_guess_mono_wf : forall Θ P Ξ A,
  a_guess_mono Θ P Ξ A ->
  forall Δ, Θ ⨟ Δ ⊢ₚₛᵃ P -> (Ξ ++ Θ) ⨟ Δ ⊢ₚₛᵃ (ptyp_to_pskl A).
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
    + pose proof (ftvar_in_ptyp_to_pskl (close_ptyp_wrt_ptyp β A)) as Hco.
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
  Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' ->
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
           | Hd : _ ⊢ₑ _ ∼ _ ⤳ _ ⨾ _ |- _ =>
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
  Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' ->
  forall Δ,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  Θ ⨟ Δ ⊢ₚₛᵃ P0 ->
  (Ξ ++ Θ) ⨟ Δ ⊢ₚₛᵃ P'.
Proof.
  intros Θ P P0 Ξ P' H; induction H; intros Δ HwfP HwfQ;
    (* the rows that generate nothing: [nil ++ Θ] IS [Θ] *)
    try solve [ cbn [app]; apply a_wf_pskl__unit
              | cbn [app]; exact HwfP
              | cbn [app]; exact HwfQ ].
  - (* SE-FlexR — the one generating row *)
    eapply a_guess_mono_wf; eassumption.
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
                       ltac:(clear - H; fsetdec))) as HsP.
      pose proof (a_wf_pskl_shielded_dom
                    (a_wf_pskl_all_inv_at HwfQ (β := β)
                       ltac:(clear - H; fsetdec))) as HsQ.
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
                       ltac:(clear - H; fsetdec))) as HsQ.
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
                       ltac:(clear - H; fsetdec))) as HsP.
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

(** Closer for the [rho_leaf] disjunct of every consistency case: the
    target [ψa] is a replaced rigid variable [var α], the freshness pack
    forces [Pi = var α], and SE-Var solves with [Pa := Pi].  Uniform across
    all 15 cases of the main induction. *)
Lemma p6cv_close_leaf :
  forall NM Θ0 Θ κ Δ Δρ Ψρ Ψ' Ψi Ψa ψsub ψa Pi P0,
  a_wf_aenv Θ ->
  a_tags_sort NM Ψ' ψa ->
  Ψi `union` Ψa [<=] Ψ' ->
  rho_fresh Δρ Θ κ ->
  Δρ [<=] Δ ->
  (forall α, α `in` Δρ -> α `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
  Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa ->
  rho_leaf NM Θ Δρ Ψρ ψsub ψa ->
  exists Pa, Θ0 ⊢ₑ Pi ∼ P0 ⤳ nil ⨾ Pa /\
             Θ ⨟ Δ ⊢ (msubst_pskl κ Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa.
Proof.
  intros NM Θ0 Θ κ Δ Δρ Ψρ Ψ' Ψi Ψa ψsub ψa Pi P0
    HwfΘ Htags Hsub Hfresh Hdelta Hshield Hpre Hleaf.
  destruct Hleaf as (α & Ψ'' & Heqψa & HαΔρ & Htagsub & Hwfsub & HΨρ).
  subst ψa.
  pose proof (Hfresh α HαΔρ) as (HXb & Hκav & Hdef).
  assert (HαΔ : α `in` Δ) by (clear - Hdelta HαΔρ; fsetdec).
  pose proof (Hshield α HαΔρ) as Hsh.
  destruct (ad_ppre_delta_var_inv Hpre eq_refl HwfΘ HαΔ HXb Hdef Hsh)
    as (Heqm & HΨie).
  assert (HeqPi : Pi = pskl_var_f α)
    by (eapply msubst_pskl_var_inv; eassumption).
  assert (HΨ'e : Ψ' [=] empty)
    by (exact (d_tags_skl_var_inv (a_tags_sort_d_tags Htags))).
  assert (HΨae : Ψa [=] empty) by (clear - Hsub HΨ'e; fsetdec).
  exists Pi. split.
  - rewrite HeqPi. apply a_solve_eq__var.
  - rewrite Heqm.
    apply ad_ppre__var; [ clear - HΨie HΨae; fsetdec | left; exact HαΔ ].
Qed.

(** Painting inversions.  An inherited painting equals a compound [bskl]
    only for the matching [pskl] source; since [κ] maps flexibles to
    MONOTYPES, [pskl_to_bskl_inh_all_inh_inv] is what excludes a flexible
    [P0] in the ForallInh/ForallSyn cases (a genuine [∀]-source is forced). *)
Lemma pskl_to_bskl_inh_all_inh_inv : forall P Q0,
  pskl_to_bskl_inh P = bskl_all_inh Q0 ->
  exists P0, P = pskl_all_syn P0 /\ pskl_to_bskl_inh P0 = Q0.
Proof.
  intros P Q0 H; destruct P; simpl in H; try discriminate.
  inversion H; subst. exists P; split; reflexivity.
Qed.

Lemma pskl_to_bskl_inh_arrow_inv : forall P Q1 Q2,
  pskl_to_bskl_inh P = bskl_arrow Q1 Q2 ->
  exists P1 P2, P = pskl_arrow P1 P2 /\
    pskl_to_bskl_inh P1 = Q1 /\ pskl_to_bskl_inh P2 = Q2.
Proof.
  intros P Q1 Q2 H; destruct P; simpl in H; try discriminate.
  inversion H; subst. exists P1, P2; repeat split; reflexivity.
Qed.

Lemma pskl_to_bskl_inh_tophole_inv : forall P Q0,
  pskl_to_bskl_inh P = bskl_tophole Q0 ->
  exists P0, P = pskl_tophole P0 /\ pskl_to_bskl_inh P0 = Q0.
Proof.
  intros P Q0 H; destruct P; simpl in H; try discriminate.
  inversion H; subst. exists P; split; reflexivity.
Qed.

(** Refinement→precision bridge for the [unit] target.  An inherited
    painting that refines to [bskl_unit] is precise to [uskl_unit]; the
    induction follows [flex_l] definition chains and strips ∀◇ via
    [tophole_remove].  Discharges the [Pi = □] and ∀◇-[P0] subcases of the
    Unit consistency case (conclusion: [msubst κ P0 ⊑ᵖ[∅] unit]). *)
Lemma ad_refine_inh_unit_ppre : forall Θ Δr Qlhs Qrhs,
  a_wf_aenv Θ ->
  Θ ⨟ Δr ⊢ᵣᵃ Qlhs ⊳ Qrhs ->
  Qrhs = bskl_unit ->
  forall P' Δ, Qlhs = pskl_to_bskl_inh P' ->
  Θ ⨟ Δ ⊢ P' ⊑ᵖ[ empty ] uskl_unit.
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

(** The metasubstitution's domain is exactly the source's flexibles, so a
    variable outside it looks up to itself, and a RIGID source variable is
    fixed by [msubst]. *)
Lemma msubst_lookup_notin_dom : forall κ α,
  α `notin` dom κ ->
  msubst_lookup κ α = ptyp_var_f α.
Proof.
  induction κ as [ | [β τ] κ' IH ]; intros α Hni; simpl in *; auto.
  destruct (α == β) as [->|Hne]; [ exfalso; auto | ].
  apply IH. auto.
Qed.

Lemma a_inc_dom_flex : forall Θ0 κ Θ α',
  κ ∷ Θ0 ⊑ Θ ->
  α' `in` dom κ ->
  a_flex_tvar Θ0 α'.
Proof.
  intros Θ0 κ Θ α' Hinc; induction Hinc; intros Hin; simpl in Hin.
  - fsetdec.
  - destruct (α' == α) as [->|Hne].
    + left. simpl_env. auto.
    + assert (Ht : α' `in` dom κ) by (clear - Hin Hne; fsetdec).
      destruct (IHHinc Ht) as [Hb | [τ0 Hb]].
      * left. apply binds_cons_3; assumption.
      * right; exists τ0. apply binds_cons_3; assumption.
  - destruct (α' == α) as [->|Hne].
    + right; exists τ. simpl_env. auto.
    + assert (Ht : α' `in` dom κ) by (clear - Hin Hne; fsetdec).
      destruct (IHHinc Ht) as [Hb | [τ0 Hb]].
      * left. apply binds_cons_3; assumption.
      * right; exists τ0. apply binds_cons_3; assumption.
  - destruct (IHHinc Hin) as [Hb | [τ0 Hb]].
    + left. apply binds_cons_3; assumption.
    + right; exists τ0. apply binds_cons_3; assumption.
  - destruct (IHHinc Hin) as [Hb | [τ0 Hb]].
    + left. apply binds_cons_3; assumption.
    + right; exists τ0. apply binds_cons_3; assumption.
  - destruct (IHHinc Hin) as [Hb | [τ0 Hb]].
    + left. apply binds_cons_3; assumption.
    + right; exists τ0. apply binds_cons_3; assumption.
Qed.

Lemma msubst_pskl_tvar_id : forall Θ0 κ Θ α,
  a_wf_aenv Θ0 ->
  κ ∷ Θ0 ⊑ Θ ->
  binds α abind_tvar Θ0 ->
  msubst_pskl κ (pskl_var_f α) = pskl_var_f α.
Proof.
  intros Θ0 κ Θ α Hwf Hinc Hb.
  simpl. rewrite msubst_lookup_notin_dom; [ reflexivity | ].
  intros Hin. pose proof (a_inc_dom_flex Hinc Hin) as Hfl.
  pose proof (a_wf_aenv_uniq Hwf) as Huniq.
  destruct Hfl as [Hbf | [τ Hbf]];
    pose proof (binds_unique _ _ _ _ _ Hb Hbf Huniq) as Hc; discriminate Hc.
Qed.

(** A rigid variable cannot refine into [unit] (only [flex_l] could fire,
    but its [α] would be a defined flexible, clashing with rigidity).  Used
    to discharge the P0 = rigid-variable subcase of the Unit case. *)
Lemma ad_refine_syn_rigid_var_unit_absurd : forall Θ Δ α,
  a_wf_aenv Θ ->
  binds α abind_tvar Θ ->
  Θ ⨟ Δ ⊢ᵣᵃ (bskl_var_f α) ⊳ bskl_unit ->
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
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] uskl_unit -> Ψ [=] empty.
Proof.
  intros Θ Δ P Ψ H; remember uskl_unit as u eqn:Hu.
  induction H; try discriminate Hu; subst; auto.
Qed.

(* ==== the Unit consistency case, as a standalone lemma ==== *)
(* P0 is well-formed at empty Δ (the paper's [Θ0 ⊢ P0]); Pi carries the
   binder context Δ.  Strong induction on [size Pi + size P0] so the ∀◇
   stripping (Pi and P0 sides) recurses. *)
Lemma a_solve_eq_cv_unit : forall n Θ0 Θ κ Δ Ψi Pi P0,
  size_pskl Pi + size_pskl P0 <= n ->
  a_wf_aenv Θ -> a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ Pi -> Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] uskl_unit ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ bskl_unit ->
  exists Pa, Θ0 ⊢ₑ Pi ∼ P0 ⤳ nil ⨾ Pa /\
             Θ ⨟ Δ ⊢ (msubst_pskl κ Pa) ⊑ᵖ[ Ψi ] uskl_unit.
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
      | Href' : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl κ P0') ⊳ bskl_unit,
        HwfP0' : _ ⨟ _ ⊢ₚₛᵃ P0' |- _ =>
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
      | Hpre' : _ ⨟ _ ⊢ msubst_pskl κ Pi' ⊑ᵖ[ _ ] uskl_unit,
        HwfPi' : _ ⨟ _ ⊢ₚₛᵃ Pi' |- _ =>
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
      | Hpre' : _ ⨟ _ ⊢ msubst_pskl κ Pi' ⊑ᵖ[ _ ] uskl_unit,
        HwfPi' : _ ⨟ _ ⊢ₚₛᵃ Pi' |- _ =>
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
      | Hpre' : _ ⨟ _ ⊢ msubst_pskl κ Pi' ⊑ᵖ[ _ ] uskl_unit,
        Href' : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl κ P0') ⊳ bskl_unit,
        HwfPi' : _ ⨟ _ ⊢ₚₛᵃ Pi',
        HwfP0' : _ ⨟ _ ⊢ₚₛᵃ P0' |- _ =>
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

Lemma ptyp_to_uskl_syn_all_etag_absurd : forall τ ε ψ,
  ptyp_to_uskl_syn τ = uskl_all_etag ε ψ -> False.
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

Lemma a_inc_lookup_mono : forall Θ0 κ Θ α',
  κ ∷ Θ0 ⊑ Θ ->
  mono_ptyp (msubst_lookup κ α').
Proof.
  intros Θ0 κ Θ α' Hinc; induction Hinc; simpl; auto.
  - auto with frost.
  - destruct (α' == α); subst; auto.
  - destruct (α' == α); subst; auto.
Qed.

(* ---- pointwise disjointness to set-level inter emptiness ---- *)

Lemma atoms_inter_empty_pointwise : forall s1 s2,
  (forall y, y `in` s1 -> y `notin` s2) ->
  s1 ∩ s2 [=] empty.
Proof.
  intros s1 s2 H y; split; intro Hy.
  - apply inter_iff in Hy as [H1 H2].
    exfalso. exact (H y H1 H2).
  - apply empty_iff in Hy; contradiction.
Qed.

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

Lemma a_def_chain_mono : forall Θ τ τe,
  a_def_chain Θ τ τe ->
  a_wf_aenv Θ ->
  mono_ptyp τ ->
  mono_ptyp τe.
Proof.
  intros Θ τ τe Hc; induction Hc; intros Hwf Hm; auto.
  apply IHHc; auto.
  eapply a_wf_aenv_binds_def_mono; eauto.
Qed.

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
  forall Δ, Θ ⨟ Δ ⊢ₚₛᵃ (ptyp_to_pskl τ).
Proof.
  intros τ Θ Hwf Hm; revert Hwf; induction Hm; intros Hwf Δ; simpl.
  - apply a_wf_pskl__unit.
  - inversion Hwf; subst. apply a_wf_pskl__var; auto.
  - inversion Hwf; subst. apply a_wf_pskl__arrow; auto.
Qed.

Lemma ad_ppre_mono_paint_refl : forall τ Θ Δ,
  a_wf_ptyp Θ τ -> mono_ptyp τ ->
  Θ ⨟ Δ ⊢ (ptyp_to_pskl τ) ⊑ᵖ[ empty ] (ptyp_to_uskl_syn τ).
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
  Θ ⨟ Δr ⊢ᵣᵃ (ptyp_to_bskl_syn τ) ⊳ (ptyp_to_bskl_syn τ).
Proof.
  intros τ Θ Δr Hwf Hm; revert Hwf; induction Hm; intros Hwf; simpl.
  - apply ad_refine_syn__unit.
  - inversion Hwf; subst. apply ad_refine_syn__var; auto.
  - inversion Hwf; subst. apply ad_refine_syn__arrow; auto.
Qed.

(* ---- precision into a mono paint carries no tags ---- *)

Lemma ad_ppre_mono_tags_empty : forall Θ Δ P ψ Ψ,
  a_wf_aenv Θ ->
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
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
  - (* forall: target all_etag, never a mono paint *)
    exfalso; eapply ptyp_to_uskl_syn_all_etag_absurd; symmetry; exact Hequ.
  - (* hole *) assumption.
  - (* tophole_remove *)
    eapply IHad_partial_precise; eauto.
  - (* tophole_fill: target all_etag *)
    exfalso; eapply ptyp_to_uskl_syn_all_etag_absurd; symmetry; exact Hequ.
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
  a_wf_aenv Θ ->
  delta_def_fresh Δ Θ ->
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  forall α τd, ψ = uskl_var_f α ->
  binds α (abind_flex_mono_def τd) Θ ->
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τd).
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
    rewrite ftvar_in_uskl_ptyp_to_uskl_syn.
    apply atoms_inter_empty_pointwise.
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
  a_wf_aenv Θ ->
  Θ ⨟ Δr ⊢ᵣᵃ Q' ⊳ Q ->
  forall α τd, Q = bskl_var_f α ->
  binds α (abind_flex_mono_def τd) Θ ->
  Θ ⨟ Δr ⊢ᵣᵃ Q' ⊳ (ptyp_to_bskl_syn τd).
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
  a_wf_aenv Θ ->
  forall Δ Ψ P,
  delta_def_fresh Δ Θ ->
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τ) ->
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τe).
Proof.
  intros Θ τ τe Hc; induction Hc; intros HwfΘ Δ Ψ P Hdf Hpre; auto.
  apply IHHc; auto.
  eapply ad_ppre_flexdef_target_unfold;
    [ exact HwfΘ | exact Hdf | exact Hpre | reflexivity | exact H ].
Qed.

Lemma ad_ppre_chain_fold : forall Θ τ τe,
  a_def_chain Θ τ τe ->
  forall Δ Ψ P,
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τe) ->
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τ).
Proof.
  intros Θ τ τe Hc; induction Hc; intros Δ Ψ P Hpre; auto.
  simpl. eapply ad_ppre__flex_r; eauto.
Qed.

Lemma ad_refine_chain_unfold : forall Θ τ τe,
  a_def_chain Θ τ τe ->
  a_wf_aenv Θ ->
  forall Δr Q,
  Θ ⨟ Δr ⊢ᵣᵃ Q ⊳ (ptyp_to_bskl_syn τ) ->
  Θ ⨟ Δr ⊢ᵣᵃ Q ⊳ (ptyp_to_bskl_syn τe).
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
  a_wf_aenv Θ ->
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
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
  a_wf_aenv Θ ->
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  forall P1 P2, P = pskl_arrow P1 P2 ->
  forall τ, ψ = ptyp_to_uskl_syn τ -> mono_ptyp τ ->
  exists τ1 τ2 Ψ1 Ψ2,
    a_def_chain Θ τ (ptyp_arrow τ1 τ2) /\
    mono_ptyp τ1 /\ mono_ptyp τ2 /\
    Θ ⨟ Δ ⊢ P1 ⊑ᵖ[ Ψ1 ] (ptyp_to_uskl_syn τ1) /\
    Θ ⨟ Δ ⊢ P2 ⊑ᵖ[ Ψ2 ] (ptyp_to_uskl_syn τ2) /\
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
  a_wf_aenv Θ ->
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  forall P0, P = pskl_tophole P0 ->
  forall τ, ψ = ptyp_to_uskl_syn τ -> mono_ptyp τ ->
  exists τe,
    a_def_chain Θ τ τe /\ mono_ptyp τe /\
    Θ ⨟ Δ ⊢ P0 ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τe).
Proof.
  intros Θ Δ Ψ P ψ HwfΘ H; induction H; intros S0' HeqS τu Hequ Hmu;
    try discriminate HeqS.
  - (* tophole_remove *)
    inversion HeqS; subst.
    exists τu. split; [ apply a_def_chain_refl | split; assumption ].
  - (* tophole_fill: target all_etag, never a mono paint *)
    exfalso; eapply ptyp_to_uskl_syn_all_etag_absurd; symmetry; exact Hequ.
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
  a_wf_aenv Θ ->
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  forall P0, P = pskl_all_syn P0 ->
  forall τ, ψ = ptyp_to_uskl_syn τ -> mono_ptyp τ ->
  False.
Proof.
  intros Θ Δ Ψ P ψ HwfΘ H; induction H; intros S0' HeqS τu Hequ Hmu;
    try discriminate HeqS.
  - (* forall: target all_etag, never a mono paint *)
    eapply ptyp_to_uskl_syn_all_etag_absurd; symmetry; exact Hequ.
  - (* flex_r *)
    symmetry in Hequ. apply ptyp_to_uskl_syn_var_inv in Hequ; subst.
    eapply IHad_partial_precise;
      [ exact HwfΘ | reflexivity | reflexivity
      | eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

Lemma ad_refine_tophole_lhs_chain_inv : forall Θ Δr Q' Q,
  a_wf_aenv Θ ->
  Θ ⨟ Δr ⊢ᵣᵃ Q' ⊳ Q ->
  forall Qb, Q' = bskl_tophole Qb ->
  forall τ, Q = ptyp_to_bskl_syn τ -> mono_ptyp τ ->
  exists τe,
    a_def_chain Θ τ τe /\ mono_ptyp τe /\
    Θ ⨟ Δr ⊢ᵣᵃ Qb ⊳ (ptyp_to_bskl_syn τe).
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
  a_wf_aenv Θ ->
  Θ ⨟ Δr ⊢ᵣᵃ Q' ⊳ Q ->
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
  a_wf_aenv Θ ->
  Δr [=] empty ->
  Θ ⨟ Δr ⊢ᵣᵃ Q' ⊳ Q ->
  forall τb τ, Q' = ptyp_to_bskl_syn τb -> Q = ptyp_to_bskl_syn τ ->
  mono_ptyp τb -> mono_ptyp τ ->
  forall Δ, Θ ⨟ Δ ⊢ (ptyp_to_pskl τb) ⊑ᵖ[ empty ] (ptyp_to_uskl_syn τ).
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
  a_wf_aenv Θ ->
  Δr [=] empty ->
  Θ ⨟ Δr ⊢ᵣᵃ Q' ⊳ Q ->
  forall P' τ, Q' = pskl_to_bskl_inh P' -> Q = ptyp_to_bskl_syn τ ->
  mono_ptyp τ ->
  forall Δ Ψ, delta_def_fresh Δ Θ ->
  Θ ⨟ Δ ⊢ pskl_hole ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τ) ->
  Θ ⨟ Δ ⊢ P' ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τ).
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
      rewrite ftvar_in_uskl_ptyp_to_uskl_syn in HInt.
      simpl in HInt.
      assert (Hhp1 : Θ ⨟ Δo ⊢ pskl_hole ⊑ᵖ[ empty ] (ptyp_to_uskl_syn τ1))
        by (apply ad_ppre__hole;
              [ clear; fsetdec
              | rewrite ftvar_in_uskl_ptyp_to_uskl_syn;
                clear - HInt; fsetdec ]).
      assert (Hhp2 : Θ ⨟ Δo ⊢ pskl_hole ⊑ᵖ[ empty ] (ptyp_to_uskl_syn τ2))
        by (apply ad_ppre__hole;
              [ clear; fsetdec
              | rewrite ftvar_in_uskl_ptyp_to_uskl_syn;
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
    assert (Hhp' : Θ ⨟ Δo ⊢ pskl_hole ⊑ᵖ[ Ψo ] (ptyp_to_uskl_syn τ)).
    { inversion Hhp; subst.
      - (* hole rule at the variable target: rebuild at the definition *)
        apply ad_ppre__hole; [ assumption | ].
        rewrite ftvar_in_uskl_ptyp_to_uskl_syn.
        apply atoms_inter_empty_pointwise.
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
  a_wf_aenv Θ ->
  binds α abind_tvar Θ ->
  Θ ⨟ Δr ⊢ᵣᵃ (bskl_var_f α) ⊳ Q ->
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
(*  Same shape as [a_guess_ty_witness] (prop_look_complete_extract.v §9),  *)
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
  Θ ⨟ Δ ⊢ (ptyp_to_pskl τ) ⊑ᵖ[ empty ] (ptyp_to_uskl_syn τ).
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
  a_def_chain Θ τ τe -> a_wf_aenv Θ -> a_wf_ptyp Θ τ -> a_wf_ptyp Θ τe.
Proof.
  intros Θ τ τe Hc; induction Hc; intros Hwf Hp; auto.
  apply IHHc; [ exact Hwf | ].
  eapply a_wf_aenv_binds_def_wf; eauto.
Qed.

Lemma a_guess_ty_witness_mono : forall n Θ0 Θ κ Δ Ψi τ Pi,
  size_pskl Pi <= n ->
  a_wf_aenv Θ ->
  Θ0 ⨟ empty ⊢ₚₛᵃ Pi ->
  mono_ptyp τ ->
  a_wf_ptyp Θ τ ->
  Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (ptyp_to_uskl_syn τ) ->
  forall L, exists (Ξ : aenv) (A : ptyp) (κ' : metasubst),
    (forall Θg, ftvar_in_aenv Θg [<=] L -> a_guess_mono Θg Pi Ξ A) /\
    all_flex_mono Ξ /\
    uniq Ξ /\
    keys κ' = keys Ξ /\
    (forall α, α `in` dom Ξ -> α `notin` L) /\
    Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κ' /\
    Θ ⨟ Δ ⊢ (msubst_pskl (κ' ++ κ) (ptyp_to_pskl A))
            ⊑ᵖ[ Ψi ] (ptyp_to_uskl_syn τ).
Proof.
  induction n as [ | n IH ];
    intros Θ0 Θ κ Δ Ψi τ Pi Hsz HwfΘ HwfPi Hmτ Hwfτ Hpre L.
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
    assert (HwfPi1 : Θ0 ⨟ empty ⊢ₚₛᵃ Pi1) by (inversion HwfPi; assumption).
    assert (HwfPi2 : Θ0 ⨟ empty ⊢ₚₛᵃ Pi2) by (inversion HwfPi; assumption).
    cbn [msubst_pskl] in Hpre.
    destruct (ad_ppre_arrow_subject_chain_inv HwfΘ Hpre eq_refl eq_refl Hmτ)
      as (τ1 & τ2 & Ψ1 & Ψ2 & Hc & Hm1 & Hm2 & Hp1 & Hp2 & HΨ).
    assert (Hwfar : a_wf_ptyp Θ (ptyp_arrow τ1 τ2))
      by (eapply a_def_chain_wf; eassumption).
    assert (Hwf1 : a_wf_ptyp Θ τ1) by (inversion Hwfar; assumption).
    assert (Hwf2 : a_wf_ptyp Θ τ2) by (inversion Hwfar; assumption).
    (* ⚠️ BOTH IHs run at an avoid-set containing BOTH sources, and the
       second additionally avoids the first block.  That is what makes each
       branch's extension invisible to the other's result below. *)
    destruct (IH Θ0 Θ κ Δ Ψ1 τ1 Pi1 ltac:(lia) HwfΘ HwfPi1 Hm1 Hwf1 Hp1
                (L `union` ftvar_in_pskl Pi1 `union` ftvar_in_pskl Pi2))
      as (Ξ1 & A1 & κa & Hgu1 & Hfm1 & Hu1 & Hk1 & Hfr1 & HF1 & Hpr1).
    destruct (IH Θ0 Θ κ Δ Ψ2 τ2 Pi2 ltac:(lia) HwfΘ HwfPi2 Hm2 Hwf2 Hp2
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
    split; [ apply Forall_cons; [ split; assumption | apply Forall_nil ] | ].
    cbn [app ptyp_to_pskl msubst_pskl msubst_lookup].
    destruct (α1 == α1) as [_ | Hne]; [ | contradiction ].
    eapply ad_partial_precise_psi_cong;
      [ apply ad_ppre_mono_refl; assumption | clear - HΨi; fsetdec ].
  - (* ---------------------------- ∀◇ ------------------------------- *)
    (* [guess^TY] DROPS the universal ghost; the precision premise peels
       through the chain to the body *)
    cbn in Hsz.
    assert (HwfPi' : Θ0 ⨟ empty ⊢ₚₛᵃ Pi') by (inversion HwfPi; assumption).
    cbn [msubst_pskl] in Hpre.
    destruct (ad_ppre_tophole_subject_chain_inv HwfΘ Hpre eq_refl eq_refl Hmτ)
      as (τe & Hc & Hme & Hp').
    assert (Hwfe : a_wf_ptyp Θ τe) by (eapply a_def_chain_wf; eassumption).
    destruct (IH Θ0 Θ κ Δ Ψi τe Pi' ltac:(lia) HwfΘ HwfPi' Hme Hwfe Hp' L)
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

(* ===================================================================== *)
(*  THE FLEX-BLOCK EXTENSION KIT — moved up from                          *)
(*  prop_look_complete_cstr.v (2026-08-04).                               *)
(*                                                                        *)
(*  Nothing in it is specific to the collection layer: it is the algebra   *)
(*  of prepending an ALIGNED, wf-mono flexible block to a metasubstitution *)
(*  and to its source context.  Before the repair the only blocks around   *)
(*  were the collection's and the final guess's, both below this file;     *)
(*  the repaired [SolE-FlexR] makes the SOLVE emit one, and [SE-Arrow]     *)
(*  THREADS — its second premise runs at [Ξ1 ++ Θ] — so the arrow case of  *)
(*  [a_solve_eq_cv_mono] right below is now the FIRST consumer.           *)
(* ===================================================================== *)

(** Split off an all-flex_mono prefix from an [a_inc]: the aligned images are
    wf monotypes in the target, and the remaining substitution increments Θ0. *)
Lemma a_inc_flex_prefix_split : forall Ξ κa Θ0 κb Θ,
  all_flex_mono Ξ ->
  keys κa = keys Ξ ->
  (κa ++ κb) ∷ (Ξ ++ Θ0) ⊑ Θ ->
  Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κa /\ κb ∷ Θ0 ⊑ Θ.
Proof.
  induction Ξ as [ | [x b] Ξ' IH ]; intros κa Θ0 κb Θ Hfm Hmap Hinc.
  - destruct κa as [ | ? ? ]; simpl in Hmap; [ | discriminate ].
    simpl in Hinc. split; [ constructor | exact Hinc ].
  - inversion Hfm as [ | ph pt Hb Hfm' ]; subst; simpl in Hb; subst b.
    destruct κa as [ | [y τ] κa' ]; simpl in Hmap; [ discriminate | ].
    injection Hmap as Hxy Hmap'; subst y.
    simpl in Hinc.
    inversion Hinc as [ | Θ2 κ2 Θ3 x2 τ2 Hinc2 Hwf2 Hmono2 | | | | ]; subst.
    destruct (IH κa' Θ0 κb Θ Hfm' Hmap' Hinc2) as [Hfa Hrest].
    split; [ constructor; [ split; assumption | exact Hfa ] | exact Hrest ].
Qed.

(** Prepend an aligned, wf-mono flex_mono prefix onto an [a_inc]. *)
Lemma a_inc_flex_prefix_build : forall Ξ κa Θ0 κb Θ,
  all_flex_mono Ξ ->
  keys κa = keys Ξ ->
  Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κa ->
  κb ∷ Θ0 ⊑ Θ ->
  (κa ++ κb) ∷ (Ξ ++ Θ0) ⊑ Θ.
Proof.
  induction Ξ as [ | [x b] Ξ' IH ]; intros κa Θ0 κb Θ Hfm Hmap Hwm Hinc.
  - destruct κa as [ | ? ? ]; simpl in Hmap; [ | discriminate ].
    simpl. exact Hinc.
  - inversion Hfm as [ | ph pt Hb Hfm' ]; subst; simpl in Hb; subst b.
    destruct κa as [ | [y τ] κa' ]; simpl in Hmap; [ discriminate | ].
    injection Hmap as Hxy Hmap'; subst y.
    inversion Hwm as [ | ph2 pt2 Hwmh Hwm' ]; subst; destruct Hwmh as [Hwfτ Hmτ].
    simpl. apply a_inc__flex; [ apply IH; assumption | exact Hwfτ | exact Hmτ ].
Qed.

(** A block of undefined flexibles is a declaration-only suffix — so it can
    never be ill-scoped, only mis-named (the [Ξ] scoping kit's (K3),
    prop_solve_sub.v).  Stated over [all_flex_mono] because that is the form
    the completeness packages carry. *)
Lemma all_flex_mono_decls : forall Ξ, all_flex_mono Ξ -> a_decls Ξ.
Proof.
  intros Ξ H; induction H as [ | [α b] Ξ' Hb Hall IH ]; [ constructor | ].
  simpl in Hb; subst b. apply (a_decls__cons α). exact IH.
Qed.

Lemma all_flex_mono_ftvar_in_aenv : forall Ξ,
  all_flex_mono Ξ -> ftvar_in_aenv Ξ [<=] dom Ξ.
Proof.
  intros Ξ H; induction H as [ | [α b] Ξ' Hb Hall IH ]; simpl in *.
  - fsetdec.
  - subst b. simpl. clear - IH; fsetdec.
Qed.

(** The extended context is well-formed as soon as the block is uniq and
    apart from the old domain.  (A local copy of [a_wf_aenv_prepend_decls],
    which lives in prop_sub_sound.v — a file this one does not import.) *)
Lemma a_wf_aenv_prepend_flex_block : forall Ξ Θ,
  all_flex_mono Ξ ->
  uniq Ξ ->
  (forall α, α `in` dom Ξ -> α `notin` dom Θ) ->
  a_wf_aenv Θ ->
  a_wf_aenv (Ξ ++ Θ).
Proof.
  intros Ξ; induction Ξ as [ | [α b] Ξ' IH ]; intros Θ Hfm Hu Hfr Hwf;
    [ exact Hwf | ].
  pose proof (Forall_inv Hfm) as Hb; simpl in Hb; subst b.
  pose proof (Forall_inv_tail Hfm) as Hfm'.
  assert (HαΘ : α `notin` dom Θ) by (apply Hfr; simpl; fsetdec).
  assert (HαΞ : α `notin` dom Ξ') by (clear - Hu; solve_uniq).
  simpl_env. apply a_wf_aenv__flex.
  - rewrite dom_app. clear - HαΘ HαΞ; fsetdec.
  - apply IH; [ exact Hfm' | clear - Hu; solve_uniq | | exact Hwf ].
    intros α0 Hα0. apply Hfr. simpl. clear - Hα0; fsetdec.
Qed.

(* ===================================================================== *)
(*  ⭐ [guess^TY] READS ITS CONTEXT ONLY AS AN AVOID-SET.                  *)
(*                                                                        *)
(*  [a_guess_mono_ctx_shrink] (prop_solve_sub.v) already says the guess    *)
(*  transports to a context that MENTIONS LESS.  What the SolE-FlexR       *)
(*  repair needs is the GROWING direction: SE-FlexR now calls the guess,   *)
(*  and the solve's flex-block weakening — a threading row's second        *)
(*  premise runs at [Ξ1 ++ Θ] — enlarges the avoid-set.  The only thing    *)
(*  that can go wrong is a name COLLISION, so that is exactly the premise: *)
(*  the block already generated must dodge whatever the new context        *)
(*  mentions.  (Not an artefact — it says you may not retroactively add a  *)
(*  context entry colliding with a name the algorithm invented, which the  *)
(*  implementation's global counter enforces.)                             *)
(* ===================================================================== *)

(** The [ptyp] twin of [swap_pskl_as_subst] (prop_swap.v §7). *)
Lemma swap_ptyp_as_subst : forall a b A,
  b `notin` ftvar_in_ptyp A ->
  swap_ptyp a b A = subst_ptyp_in_ptyp (ptyp_var_f b) a A.
Proof.
  induction A; simpl; intros Hb; f_equal;
    try solve [ reflexivity | apply IHA; fsetdec
              | apply IHA1; fsetdec | apply IHA2; fsetdec ].
  destruct (α == a) as [-> | Hne].
  - rewrite swap_atom_l. destruct (a == a); [ reflexivity | contradiction ].
  - rewrite swap_atom_other; [ | fsetdec | simpl in Hb; fsetdec ].
    destruct (α == a); [ contradiction | reflexivity ].
Qed.

(** The [pskl] twin of [close_ptyp_subst_var] (prop_flex.v).  It used to live
    in prop_solve_sub.v, alongside the double-RENAME witness-move the repair
    retired (§4a); the move is a SWAP now, but the CLOSE-after-rename step
    survives — it is what keeps a ∀ row's output untouched when its recorded
    binder has to be re-picked. *)
Lemma close_pskl_subst_var : forall P α β,
  β `notin` ftvar_in_pskl P ->
  close_pskl_wrt_pskl β (subst_pskl_in_pskl (pskl_var_f β) α P)
  = close_pskl_wrt_pskl α P.
Proof.
  intros P α β Hβ.
  rewrite subst_pskl_in_pskl_spec.
  apply close_pskl_wrt_pskl_open_pskl_wrt_pskl.
  assert (Hcl : ftvar_in_pskl (close_pskl_wrt_pskl α P)
                  [=] AtomSetImpl.remove α (ftvar_in_pskl P))
    by (apply ftvar_in_pskl_close_pskl_wrt_pskl).
  clear - Hβ Hcl. fsetdec.
Qed.

Lemma a_guess_mono_ctx_change_size : forall n Θ Θ' P Ξ A,
  size_pskl P <= n ->
  a_guess_mono Θ P Ξ A ->
  (forall α, α `in` dom Ξ -> α `notin` ftvar_in_aenv Θ') ->
  a_guess_mono Θ' P Ξ A.
Proof.
  induction n as [ | n IH ]; intros Θ Θ' P Ξ A Hsz H Hfr;
    [ exfalso; pose proof (size_pskl_min P); lia | ].
  destruct H as [ Θ0 α Hα | Θ0 Pb Ξb Ab Hg | Θ0 α | Θ0
                | Θ0 Pa Pb Ξa Ξb Aa Ab Hga Hgb
                | Θ0 Pb Ξb Ab b0 Hfrb Hg ]; cbn in Hsz.
  - (* ◇: the invented name IS the block, so the premise is the rule's own *)
    apply a_guess_mono__hole. apply Hfr. simpl; clear; fsetdec.
  - (* ∀◇ *) apply a_guess_mono__tophole.
    eapply IH; [ lia | exact Hg | exact Hfr ].
  - (* var *) apply a_guess_mono__var.
  - (* unit *) apply a_guess_mono__unit.
  - (* arrow: both halves run at the SAME context, so both inherit [Hfr] *)
    apply a_guess_mono__arrow.
    + eapply IH; [ lia | exact Hga | ].
      intros α Hα; apply Hfr; rewrite dom_app; clear - Hα; fsetdec.
    + eapply IH; [ lia | exact Hgb | ].
      intros α Hα; apply Hfr; rewrite dom_app; clear - Hα; fsetdec.
  - (* ∀: the recorded witness may collide with the NEW context, so RE-PICK
       it.  The move is a SWAP, not a rename — [b0] sits IN the premise's
       own context, so "the source dodges the context" cannot hold (§4a of
       the hand-off).  It is harmless because the IH's target context is
       arbitrary: [swap_aenv b0 δ Θ0] never has to collapse to anything. *)
    destruct (atom_fresh (ftvar_in_aenv Θ' `union` ftvar_in_pskl Pb
                `union` dom Ξb `union` ftvar_in_ptyp Ab
                `union` singleton b0)) as [δ Hδ].
    assert (Hb0Ξ : b0 `notin` dom Ξb)
      by (eapply a_guess_mono_generated_fresh_binder; exact Hg).
    assert (HΞftv : ftvar_in_aenv Ξb [<=] dom Ξb)
      by (eapply a_guess_mono_generated_ftvar; exact Hg).
    pose proof (@a_guess_mono_swap b0 δ _ _ _ _ Hg) as Hsw.
    rewrite swap_aenv_app, swap_aenv_one_tvar in Hsw.
    rewrite swap_pskl_open_var, swap_atom_l in Hsw.
    rewrite (swap_pskl_fresh_id b0 δ Pb) in Hsw
      by (clear - Hfrb Hδ; fsetdec).
    rewrite (swap_aenv_fresh_id b0 δ Ξb) in Hsw
      by (clear - Hb0Ξ Hδ HΞftv; fsetdec).
    rewrite (@swap_ptyp_as_subst b0 δ Ab) in Hsw
      by (clear - Hδ; fsetdec).
    assert (Hgδ : a_guess_mono ((δ ~ abind_tvar) ++ Θ')
                    (open_pskl_wrt_pskl Pb (pskl_var_f δ)) Ξb
                    (subst_ptyp_in_ptyp (ptyp_var_f δ) b0 Ab)).
    { eapply IH;
        [ rewrite size_pskl_open_pskl_wrt_pskl_var; lia
        | exact Hsw
        | intros α Hα; specialize (Hfr α Hα); simpl;
          assert (Hne : α `notin` singleton δ) by (clear - Hα Hδ; fsetdec);
          clear - Hfr Hne; fsetdec ]. }
    rewrite <- (@close_ptyp_subst_var Ab b0 δ ltac:(clear - Hδ; fsetdec)).
    apply a_guess_mono__forall with (β := δ);
      [ clear - Hδ; fsetdec | exact Hgδ ].
Qed.

Lemma a_guess_mono_ctx_change : forall Θ Θ' P Ξ A,
  a_guess_mono Θ P Ξ A ->
  (forall α, α `in` dom Ξ -> α `notin` ftvar_in_aenv Θ') ->
  a_guess_mono Θ' P Ξ A.
Proof.
  intros Θ Θ' P Ξ A H Hfr.
  eapply a_guess_mono_ctx_change_size; [ reflexivity | exact H | exact Hfr ].
Qed.

(* ===================================================================== *)
(*  ⭐ WEAKENING A SOLVE BY A FRESH FLEXIBLE BLOCK IN THE MIDDLE.          *)
(*                                                                        *)
(*  MOVED UP from prop_look_complete_cstr.v (P6-Cs) and REPAIRED for the   *)
(*  SolE-FlexR threading, 2026-08-04.  Why it moved: every completeness    *)
(*  file's ARROW case now has to put its two branches at DIFFERENT         *)
(*  contexts, because [SS-Arrow] / [SE-Arrow] / [a_solve_cstr__eq] thread  *)
(*  — the second premise runs at [Ξ1 ++ Θ].  The branches themselves are   *)
(*  produced by induction hypotheses stated at [Θ0], so each file needs    *)
(*  exactly this: push the first branch's block underneath the second      *)
(*  branch's derivation.                                                   *)
(*                                                                        *)
(*  THREE THINGS THE REPAIR CHANGED.                                       *)
(*  · The generated block [Ξ] threads through untouched — a solve does not *)
(*    read the context to decide WHAT to invent, only to decide what NOT   *)
(*    to invent.                                                           *)
(*  · ⭐ A NEW PREMISE [dom Ξm ∩ dom Ξ = ∅].  SE-FlexR calls [guess^TY],   *)
(*    whose invented names avoid [ftvar_in_aenv Θ]; inserting [Ξm]         *)
(*    ENLARGES that set, so a run that happened to generate an atom of     *)
(*    [Ξm] cannot be replayed.  Discharged at every call site out of the   *)
(*    package's own freshness component.  ([a_guess_mono_ctx_change]       *)
(*    above is what makes it sufficient.)                                  *)
(*  · ⚠️ The ∀ rows re-freshen by SWAP, not by the double RENAME the        *)
(*    pre-repair proof used: the witness now sits IN the premise's own     *)
(*    context, so [a_solve_*_rename_var]'s "the source dodges the context" *)
(*    can never hold.  [a_solve_*_move_binder*] (prop_solve_sub.v §4a) is  *)
(*    the replacement, and the two [swap_aenv … = …] collapses it leaves   *)
(*    are exactly [swap_aenv_fresh_id] at the rule's own freshness.        *)
(* ===================================================================== *)

Lemma binds_weaken_mid : forall (x : atom) (b : abind) Ξl Ξm Θ0,
  binds x b (Ξl ++ Θ0) -> binds x b (Ξl ++ Ξm ++ Θ0).
Proof.
  intros x b Ξl Ξm Θ0 H. apply binds_app_1 in H as [H | H].
  - apply binds_app_2; exact H.
  - apply binds_app_3; apply binds_app_3; exact H.
Qed.

Lemma binds_strengthen_mid : forall (x : atom) (b : abind) Ξl Ξm Θ0,
  binds x b (Ξl ++ Ξm ++ Θ0) -> x `notin` dom Ξm -> binds x b (Ξl ++ Θ0).
Proof.
  intros x b Ξl Ξm Θ0 H Hx. apply binds_app_1 in H as [H | H].
  - apply binds_app_2; exact H.
  - apply binds_app_1 in H as [H | H].
    + exfalso. apply Hx. eapply binds_In; exact H.
    + apply binds_app_3; exact H.
Qed.

Lemma a_flex_tvar_weaken_mid : forall Ξl Ξm Θ0 α,
  a_flex_tvar (Ξl ++ Θ0) α -> a_flex_tvar (Ξl ++ Ξm ++ Θ0) α.
Proof.
  intros Ξl Ξm Θ0 α [Hb | [τ Hb]];
    [ left | right; exists τ ]; apply binds_weaken_mid; exact Hb.
Qed.

Lemma a_non_flex_weaken_mid : forall Ξl Ξm Θ0 P,
  (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P) ->
  a_non_flex (Ξl ++ Θ0) P -> a_non_flex (Ξl ++ Ξm ++ Θ0) P.
Proof.
  intros Ξl Ξm Θ0 P Hftv [Hlc Hnf]. split; [ exact Hlc | ].
  intro Hf. apply Hnf. inversion Hf as [ Θx αx Hb | Θx αx τ Hb ]; subst.
  - assert (Hin : αx `notin` dom Ξm)
      by (intro Hc; apply (Hftv _ Hc); simpl; fsetdec).
    apply a_flex__var with (α := αx).
    eapply binds_strengthen_mid; [ exact Hb | exact Hin ].
  - assert (Hin : αx `notin` dom Ξm)
      by (intro Hc; apply (Hftv _ Hc); simpl; fsetdec).
    apply a_flex__var_def with (α := αx) (τ := τ).
    eapply binds_strengthen_mid; [ exact Hb | exact Hin ].
Qed.

(** The mid-insertion enlarges [ftvar_in_aenv] by exactly [dom Ξm] — which
    is what the guess and the ∀ rows' freshness conditions read. *)
Lemma ftvar_in_aenv_weaken_mid : forall Ξl Ξm Θ0,
  all_flex_mono Ξm ->
  ftvar_in_aenv (Ξl ++ Ξm ++ Θ0)
    [<=] ftvar_in_aenv (Ξl ++ Θ0) `union` dom Ξm.
Proof.
  intros Ξl Ξm Θ0 Hfm.
  rewrite ! ftvar_in_aenv_app.
  pose proof (all_flex_mono_ftvar_in_aenv Hfm) as Hm.
  clear - Hm; fsetdec.
Qed.

(* The mutual subject-solve weakening, by SIZE INDUCTION (freshness
   campaign, DESIGN.md §4.3).  The binder rules are exists-fresh: each PINS
   one witness, and an inserted block can CAPTURE it, so every ∀ case first
   re-freshens the recorded binder away from [Ξm] — and a re-freshened
   premise is no sub-derivation, which is what forces the size measure (the
   sub half's [+1] tag absorbs SS-Check's sub ⤳ eq move at unchanged sizes).

   The OUTPUT-freshness premise is load-bearing: [SS-ForallR] LEAKS its
   binder, so THAT binder cannot be moved without changing the output, and
   the only way to keep it out of [Ξm] is to say so.  This is the paper's
   Barendregt convention made explicit, not a weakening of the statement. *)
Lemma a_solve_sub_eq_weaken_mid_flex_size : forall n,
  (forall Θ m P P0 Ξ P',
     2 * (size_pskl P + size_pskl P0) + 1 <= n ->
     Θ ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' ->
     forall Ξl Ξm Θ0, Θ = Ξl ++ Θ0 -> all_flex_mono Ξm ->
     (forall x, x `in` dom Ξm -> x `notin` dom (Ξl ++ Θ0)) ->
     (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P) ->
     (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P') ->
     (forall x, x `in` dom Ξm -> x `notin` dom Ξ) ->
     (Ξl ++ Ξm ++ Θ0) ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P') /\
  (forall Θ P P0 Ξ P',
     2 * (size_pskl P + size_pskl P0) <= n ->
     Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' ->
     forall Ξl Ξm Θ0, Θ = Ξl ++ Θ0 -> all_flex_mono Ξm ->
     (forall x, x `in` dom Ξm -> x `notin` dom (Ξl ++ Θ0)) ->
     (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P) ->
     (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P') ->
     (forall x, x `in` dom Ξm -> x `notin` dom Ξ) ->
     (Ξl ++ Ξm ++ Θ0) ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P').
Proof.
  induction n as [| n IHall];
    [ split; intros * Hsz Hd; inversion Hd; subst; cbn in Hsz; lia | ].
  destruct IHall as [IHs IHe].
  split.
  (* ================= the [a_solve_sub] half ================= *)
  { intros Θ m P P0 Ξ P' Hsz Hd.
    destruct Hd as
      [ Θ m α Q                                     (* SS-Var *)
      | Θ m P Q Ξ P' b Hfr Hp                       (* SS-ForallL *)
      | Θ m P Q Ξ P' Hp                             (* SS-UnivGhostL *)
      | Θ m P                                       (* SS-Vacuous *)
      | Θ P Q Ξ P' Hg1 Hg2 Hp                       (* SS-Check *)
      | Θ A B Ξ P' b Hfr Hp                         (* SS-ForallR *)
      | Θ m P1 P2 Q1 Q2 Ξ1 Ξ2 P1' P2' Hp1 Hp2       (* SS-Arrow *)
      | Θ m Q1 Q2 Ξ1 Ξ2 P1' P2' Hp1 Hp2             (* SS-GhostLF *)
      | Θ B Hg ];                                   (* SS-GhostL *)
      intros Ξl Ξm Θ0 Heq Hfm Hdisj Hftv Hout Hblk; subst; cbn in Hsz.
    - (* SS-Var *) apply a_solve_sub__var.
    - (* SS-ForallL — CLOSE: move the witness to a δ outside Ξm, which
         leaves the closed output untouched ([close_pskl_subst_var]) *)
      assert (HbΞ : b `notin` dom Ξ)
        by (eapply a_solve_sub_generated_apart_binder; exact Hp).
      assert (HΞf : ftvar_in_aenv Ξ [<=] dom Ξ)
        by (eapply (proj1 a_solve_sub_eq_generated_ftvar); exact Hp).
      pick fresh δ for
        (ftvar_in_aenv (Ξl ++ Θ0) `union` dom Ξm `union` dom Ξ
           `union` ftvar_in_pskl P `union` ftvar_in_pskl Q
           `union` ftvar_in_pskl P' `union` singleton b).
      pose proof (@a_solve_sub_move_binder_l _ _ _ _ _ _ _ δ Hp
                    ltac:(clear - Hfr; fsetdec)
                    ltac:(clear - Fr; fsetdec)) as Hr.
      rewrite (swap_aenv_fresh_id b δ (Ξl ++ Θ0)) in Hr
        by (clear - Hfr Fr; fsetdec).
      rewrite (swap_aenv_fresh_id b δ Ξ) in Hr
        by (clear - HbΞ Fr HΞf; fsetdec).
      rewrite <- (@close_pskl_subst_var P' b δ ltac:(clear - Fr; fsetdec)).
      apply a_solve_sub__forall_l with (β := δ);
        [ rewrite ftvar_in_aenv_weaken_mid by exact Hfm;
          clear - Fr; fsetdec | ].
      eapply IHs with (Ξl := ((δ ~ abind_tvar) ++ Ξl)) (Ξm := Ξm) (Θ0 := Θ0);
        [ rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia
        | exact Hr | reflexivity | exact Hfm
        | intros x Hx; specialize (Hdisj x Hx);
          assert (Hxδ : x `notin` singleton δ)
            by (clear - Fr Hx; fsetdec);
          simpl_env in Hdisj; simpl_env;
          clear - Hdisj Hxδ; fsetdec
        | intros x Hx; specialize (Hftv x Hx);
          pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f δ))
            as Hup2;
          assert (Hxδ : x `notin` singleton δ) by (clear - Fr Hx; fsetdec);
          cbn in Hftv, Hup2; clear - Hftv Hup2 Hxδ; fsetdec
        | intros x Hx; specialize (Hout x Hx);
          pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                        P' (pskl_var_f δ) b) as Hsu;
          pose proof (ftvar_in_pskl_close_pskl_wrt_pskl P' b) as Hcl;
          assert (Hxδ : x `notin` singleton δ) by (clear - Fr Hx; fsetdec);
          cbn in Hout, Hsu; clear - Hout Hsu Hcl Hxδ; fsetdec
        | exact Hblk ].
    - (* SS-UnivGhostL *)
      apply a_solve_sub__univ_ghost_l.
      eapply IHs with (Ξl := Ξl) (Ξm := Ξm) (Θ0 := Θ0);
        [ cbn; lia | exact Hp | reflexivity | exact Hfm | exact Hdisj
        | intros x Hx; specialize (Hftv x Hx); cbn in Hftv; exact Hftv
        | intros x Hx; specialize (Hout x Hx); cbn in Hout; exact Hout
        | exact Hblk ].
    - (* SS-Vacuous *) apply a_solve_sub__vacuous.
    - (* SS-Check *)
      apply a_solve_sub__check; [ exact Hg1 | exact Hg2 | ].
      eapply IHe with (Ξl := Ξl) (Ξm := Ξm) (Θ0 := Θ0);
        [ cbn; lia | exact Hp | reflexivity | exact Hfm | exact Hdisj
        | exact Hftv | exact Hout | exact Hblk ].
    - (* SS-ForallR — the LEAK.  If the witness sits inside Ξm it did NOT
         leak (the output premise), so it can be moved; otherwise it stays. *)
      assert (HbΞ : b `notin` dom Ξ)
        by (eapply a_solve_sub_generated_apart_binder; exact Hp).
      assert (HΞf : ftvar_in_aenv Ξ [<=] dom Ξ)
        by (eapply (proj1 a_solve_sub_eq_generated_ftvar); exact Hp).
      destruct (AtomSetProperties.In_dec b (dom Ξm)) as [Hin | Hnin].
      + pose proof (Hout b Hin) as HbP'.
        pick fresh δ for
          (ftvar_in_aenv (Ξl ++ Θ0) `union` dom Ξm `union` dom Ξ
             `union` ftvar_in_pskl A `union` ftvar_in_pskl B
             `union` ftvar_in_pskl P' `union` singleton b).
        pose proof (@a_solve_sub_move_binder_r _ _ _ _ _ _ δ Hp
                      ltac:(clear - Hfr; fsetdec)
                      ltac:(clear - Fr; fsetdec)) as Hr.
        rewrite (swap_aenv_fresh_id b δ (Ξl ++ Θ0)) in Hr
          by (clear - Hfr Fr; fsetdec).
        rewrite (swap_aenv_fresh_id b δ Ξ) in Hr
          by (clear - HbΞ Fr HΞf; fsetdec).
        rewrite (subst_pskl_in_pskl_fresh_eq P') in Hr
          by (clear - HbP'; fsetdec).
        apply a_solve_sub__forall_r with (β := δ);
          [ rewrite ftvar_in_aenv_weaken_mid by exact Hfm;
            clear - Fr; fsetdec | ].
        eapply IHs with (Ξl := ((δ ~ abind_tvar) ++ Ξl)) (Ξm := Ξm) (Θ0 := Θ0);
          [ rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia
          | exact Hr | reflexivity | exact Hfm
          | intros x Hx; specialize (Hdisj x Hx);
            assert (Hxδ : x `notin` singleton δ) by (clear - Fr Hx; fsetdec);
            simpl_env in Hdisj; simpl_env;
            clear - Hdisj Hxδ; fsetdec
          | intros x Hx; specialize (Hftv x Hx); cbn in Hftv; exact Hftv
          | exact Hout | exact Hblk ].
      + apply a_solve_sub__forall_r with (β := b);
          [ rewrite ftvar_in_aenv_weaken_mid by exact Hfm;
            clear - Hfr Hnin; fsetdec | ].
        eapply IHs with (Ξl := ((b ~ abind_tvar) ++ Ξl)) (Ξm := Ξm) (Θ0 := Θ0);
          [ rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia
          | exact Hp | reflexivity | exact Hfm
          | intros x Hx; specialize (Hdisj x Hx);
            assert (Hxb : x `notin` singleton b)
              by (clear - Hnin Hx; fsetdec);
            simpl_env in Hdisj; simpl_env;
            clear - Hdisj Hxb; fsetdec
          | intros x Hx; specialize (Hftv x Hx); cbn in Hftv; exact Hftv
          | exact Hout | exact Hblk ].
    - (* SS-Arrow — THREADS: the tail runs at [Ξ1 ++ Θ], so the insertion
         goes UNDER [Ξ1] for the second premise *)
      apply a_solve_sub__arrow with (Ξ1 := Ξ1).
      + eapply IHe with (Ξl := Ξl) (Ξm := Ξm) (Θ0 := Θ0);
          [ cbn; lia | exact Hp1 | reflexivity | exact Hfm | exact Hdisj
          | intros x Hx; specialize (Hftv x Hx); cbn in Hftv;
            clear - Hftv; fsetdec
          | intros x Hx; specialize (Hout x Hx); cbn in Hout;
            clear - Hout; fsetdec
          | intros x Hx; specialize (Hblk x Hx); rewrite dom_app in Hblk;
            clear - Hblk; fsetdec ].
      + rewrite <- (list_app_assoc Ξ1 Ξl (Ξm ++ Θ0)).
        eapply IHs with (Ξl := (Ξ1 ++ Ξl)) (Ξm := Ξm) (Θ0 := Θ0);
          [ cbn; lia | exact Hp2 | rewrite list_app_assoc; reflexivity | exact Hfm
          | intros x Hx; specialize (Hdisj x Hx); specialize (Hblk x Hx);
            rewrite dom_app in Hblk; rewrite ! dom_app;
            clear - Hdisj Hblk; rewrite dom_app in Hdisj; fsetdec
          | intros x Hx; specialize (Hftv x Hx); cbn in Hftv;
            clear - Hftv; fsetdec
          | intros x Hx; specialize (Hout x Hx); cbn in Hout;
            clear - Hout; fsetdec
          | intros x Hx; specialize (Hblk x Hx); rewrite dom_app in Hblk;
            clear - Hblk; fsetdec ].
    - (* SS-GhostLF — same threading *)
      apply a_solve_sub__ghost_l_fn with (Ξ1 := Ξ1).
      + eapply IHe with (Ξl := Ξl) (Ξm := Ξm) (Θ0 := Θ0);
          [ cbn; lia | exact Hp1 | reflexivity | exact Hfm | exact Hdisj
          | intros x Hx; cbn; clear; fsetdec
          | intros x Hx; specialize (Hout x Hx); cbn in Hout;
            clear - Hout; fsetdec
          | intros x Hx; specialize (Hblk x Hx); rewrite dom_app in Hblk;
            clear - Hblk; fsetdec ].
      + rewrite <- (list_app_assoc Ξ1 Ξl (Ξm ++ Θ0)).
        eapply IHs with (Ξl := (Ξ1 ++ Ξl)) (Ξm := Ξm) (Θ0 := Θ0);
          [ cbn; lia | exact Hp2 | rewrite list_app_assoc; reflexivity | exact Hfm
          | intros x Hx; specialize (Hdisj x Hx); specialize (Hblk x Hx);
            rewrite dom_app in Hblk; rewrite ! dom_app;
            clear - Hdisj Hblk; rewrite dom_app in Hdisj; fsetdec
          | intros x Hx; cbn; clear; fsetdec
          | intros x Hx; specialize (Hout x Hx); cbn in Hout;
            clear - Hout; fsetdec
          | intros x Hx; specialize (Hblk x Hx); rewrite dom_app in Hblk;
            clear - Hblk; fsetdec ].
    - (* SS-GhostL *) apply a_solve_sub__ghost_l; exact Hg. }
  (* ================= the [a_solve_eq] half ================= *)
  { intros Θ P P0 Ξ P' Hsz Hd.
    destruct Hd as
      [ Θ                                           (* SE-Unit *)
      | Θ α Q                                       (* SE-Var *)
      | Θ α P Ξ A Hflex Hnf Hng Hgu                 (* SE-FlexR *)
      | Θ Q                                         (* SE-GhostL *)
      | Θ P                                         (* SE-VacuousR *)
      | Θ P1 P2 Q1 Q2 Ξ1 Ξ2 P1' P2' Hp1 Hp2         (* SE-Arrow *)
      | Θ P Q Ξ P' b Hfr Hp                         (* SE-Forall *)
      | Θ P Q Ξ P' Hp                               (* SE-UnivGhost *)
      | Θ P Q Ξ P' b Hfr Hp                         (* SE-GhostForall *)
      | Θ P Q Ξ P' Hg Hp                            (* SE-GhostGuarded *)
      | Θ P Q Ξ P' b Hfr Hp                         (* SE-ForallGhost *)
      | Θ P Q Ξ P' Hg Hp ];                         (* SE-GuardedGhost *)
      intros Ξl Ξm Θ0 Heq Hfm Hdisj Hftv Hout Hblk; subst; cbn in Hsz.
    - (* SE-Unit *) apply a_solve_eq__unit.
    - (* SE-Var *) apply a_solve_eq__var.
    - (* ⭐ SE-FlexR: [guess^TY] reads the context as an AVOID-SET, so the
         insertion is legal exactly when the block it generated dodges the
         inserted names — which is [Hblk]. *)
      apply a_solve_eq__flex_r;
        [ apply a_flex_tvar_weaken_mid; exact Hflex
        | apply a_non_flex_weaken_mid; [ exact Hftv | exact Hnf ]
        | exact Hng
        | eapply a_guess_mono_ctx_change; [ exact Hgu | ] ].
      intros α0 Hα0.
      pose proof (a_guess_mono_generated_fresh Hgu Hα0) as Hf0.
      rewrite ftvar_in_aenv_weaken_mid by exact Hfm.
      assert (Hne : α0 `notin` dom Ξm)
        by (intro Hc; exact (Hblk α0 Hc Hα0)).
      clear - Hf0 Hne; fsetdec.
    - (* SE-GhostL *) apply a_solve_eq__hole_l.
    - (* SE-VacuousR *) apply a_solve_eq__hole_r.
    - (* SE-Arrow — THREADS *)
      apply a_solve_eq__arrow with (Ξ1 := Ξ1).
      + eapply IHe with (Ξl := Ξl) (Ξm := Ξm) (Θ0 := Θ0);
          [ cbn; lia | exact Hp1 | reflexivity | exact Hfm | exact Hdisj
          | intros x Hx; specialize (Hftv x Hx); cbn in Hftv;
            clear - Hftv; fsetdec
          | intros x Hx; specialize (Hout x Hx); cbn in Hout;
            clear - Hout; fsetdec
          | intros x Hx; specialize (Hblk x Hx); rewrite dom_app in Hblk;
            clear - Hblk; fsetdec ].
      + rewrite <- (list_app_assoc Ξ1 Ξl (Ξm ++ Θ0)).
        eapply IHe with (Ξl := (Ξ1 ++ Ξl)) (Ξm := Ξm) (Θ0 := Θ0);
          [ cbn; lia | exact Hp2 | rewrite list_app_assoc; reflexivity | exact Hfm
          | intros x Hx; specialize (Hdisj x Hx); specialize (Hblk x Hx);
            rewrite dom_app in Hblk; rewrite ! dom_app;
            clear - Hdisj Hblk; rewrite dom_app in Hdisj; fsetdec
          | intros x Hx; specialize (Hftv x Hx); cbn in Hftv;
            clear - Hftv; fsetdec
          | intros x Hx; specialize (Hout x Hx); cbn in Hout;
            clear - Hout; fsetdec
          | intros x Hx; specialize (Hblk x Hx); rewrite dom_app in Hblk;
            clear - Hblk; fsetdec ].
    - (* SE-Forall — CLOSE; re-freshen by SWAP *)
      assert (HbΞ : b `notin` dom Ξ)
        by (eapply a_solve_eq_generated_apart_binder; exact Hp).
      assert (HΞf : ftvar_in_aenv Ξ [<=] dom Ξ)
        by (eapply (proj2 a_solve_sub_eq_generated_ftvar); exact Hp).
      pick fresh δ for
        (ftvar_in_aenv (Ξl ++ Θ0) `union` dom Ξm `union` dom Ξ
           `union` ftvar_in_pskl P `union` ftvar_in_pskl Q
           `union` ftvar_in_pskl P' `union` singleton b).
      pose proof (@a_solve_eq_move_binder _ _ _ _ _ _ δ Hp
                    ltac:(clear - Hfr; fsetdec)
                    ltac:(clear - Fr; fsetdec)) as Hr.
      rewrite (swap_aenv_fresh_id b δ (Ξl ++ Θ0)) in Hr
        by (clear - Hfr Fr; fsetdec).
      rewrite (swap_aenv_fresh_id b δ Ξ) in Hr
        by (clear - HbΞ Fr HΞf; fsetdec).
      rewrite <- (@close_pskl_subst_var P' b δ ltac:(clear - Fr; fsetdec)).
      apply a_solve_eq__forall with (β := δ);
        [ rewrite ftvar_in_aenv_weaken_mid by exact Hfm;
          clear - Fr; fsetdec | ].
      eapply IHe with (Ξl := ((δ ~ abind_tvar) ++ Ξl)) (Ξm := Ξm) (Θ0 := Θ0);
        [ rewrite ! size_pskl_open_pskl_wrt_pskl_var; cbn; lia
        | exact Hr | reflexivity | exact Hfm
        | intros x Hx; specialize (Hdisj x Hx);
          assert (Hxδ : x `notin` singleton δ) by (clear - Fr Hx; fsetdec);
          simpl_env in Hdisj; simpl_env;
          clear - Hdisj Hxδ; fsetdec
        | intros x Hx; specialize (Hftv x Hx);
          pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f δ))
            as Hup2;
          assert (Hxδ : x `notin` singleton δ) by (clear - Fr Hx; fsetdec);
          cbn in Hftv, Hup2; clear - Hftv Hup2 Hxδ; fsetdec
        | intros x Hx; specialize (Hout x Hx);
          pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                        P' (pskl_var_f δ) b) as Hsu;
          pose proof (ftvar_in_pskl_close_pskl_wrt_pskl P' b) as Hcl;
          assert (Hxδ : x `notin` singleton δ) by (clear - Fr Hx; fsetdec);
          cbn in Hout, Hsu; clear - Hout Hsu Hcl Hxδ; fsetdec
        | exact Hblk ].
    - (* SE-UnivGhost *)
      apply a_solve_eq__tophole_both.
      eapply IHe with (Ξl := Ξl) (Ξm := Ξm) (Θ0 := Θ0);
        [ cbn; lia | exact Hp | reflexivity | exact Hfm | exact Hdisj
        | intros x Hx; specialize (Hftv x Hx); cbn in Hftv; exact Hftv
        | intros x Hx; specialize (Hout x Hx); cbn in Hout; exact Hout
        | exact Hblk ].
    - (* SE-GhostForall — CLOSE; the ∀◇ subject rides along unopened *)
      assert (HbΞ : b `notin` dom Ξ)
        by (eapply a_solve_eq_generated_apart_binder; exact Hp).
      assert (HΞf : ftvar_in_aenv Ξ [<=] dom Ξ)
        by (eapply (proj2 a_solve_sub_eq_generated_ftvar); exact Hp).
      pick fresh δ for
        (ftvar_in_aenv (Ξl ++ Θ0) `union` dom Ξm `union` dom Ξ
           `union` ftvar_in_pskl P `union` ftvar_in_pskl Q
           `union` ftvar_in_pskl P' `union` singleton b).
      pose proof (@a_solve_eq_move_binder_tophole_l _ _ _ _ _ _ δ Hp
                    ltac:(clear - Hfr; cbn in Hfr; fsetdec)
                    ltac:(clear - Fr; fsetdec)) as Hr.
      rewrite (swap_aenv_fresh_id b δ (Ξl ++ Θ0)) in Hr
        by (clear - Hfr Fr; fsetdec).
      rewrite (swap_aenv_fresh_id b δ Ξ) in Hr
        by (clear - HbΞ Fr HΞf; fsetdec).
      rewrite <- (@close_pskl_subst_var P' b δ ltac:(clear - Fr; fsetdec)).
      apply a_solve_eq__tophole_l_all with (β := δ);
        [ rewrite ftvar_in_aenv_weaken_mid by exact Hfm;
          clear - Fr; fsetdec | ].
      eapply IHe with (Ξl := ((δ ~ abind_tvar) ++ Ξl)) (Ξm := Ξm) (Θ0 := Θ0);
        [ rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia
        | exact Hr | reflexivity | exact Hfm
        | intros x Hx; specialize (Hdisj x Hx);
          assert (Hxδ : x `notin` singleton δ) by (clear - Fr Hx; fsetdec);
          simpl_env in Hdisj; simpl_env;
          clear - Hdisj Hxδ; fsetdec
        | intros x Hx; specialize (Hftv x Hx); cbn in Hftv |- *; exact Hftv
        | intros x Hx; specialize (Hout x Hx);
          pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                        P' (pskl_var_f δ) b) as Hsu;
          pose proof (ftvar_in_pskl_close_pskl_wrt_pskl P' b) as Hcl;
          assert (Hxδ : x `notin` singleton δ) by (clear - Fr Hx; fsetdec);
          cbn in Hout, Hsu; clear - Hout Hsu Hcl Hxδ; fsetdec
        | exact Hblk ].
    - (* SE-GhostGuarded *)
      apply a_solve_eq__tophole_l_guarded; [ exact Hg | ].
      eapply IHe with (Ξl := Ξl) (Ξm := Ξm) (Θ0 := Θ0);
        [ cbn; lia | exact Hp | reflexivity | exact Hfm | exact Hdisj
        | intros x Hx; specialize (Hftv x Hx); cbn in Hftv; exact Hftv
        | exact Hout | exact Hblk ].
    - (* SE-ForallGhost — CLOSE; the ∀◇ target rides along unopened *)
      assert (HbΞ : b `notin` dom Ξ)
        by (eapply a_solve_eq_generated_apart_binder; exact Hp).
      assert (HΞf : ftvar_in_aenv Ξ [<=] dom Ξ)
        by (eapply (proj2 a_solve_sub_eq_generated_ftvar); exact Hp).
      pick fresh δ for
        (ftvar_in_aenv (Ξl ++ Θ0) `union` dom Ξm `union` dom Ξ
           `union` ftvar_in_pskl P `union` ftvar_in_pskl Q
           `union` ftvar_in_pskl P' `union` singleton b).
      pose proof (@a_solve_eq_move_binder_tophole_r _ _ _ _ _ _ δ Hp
                    ltac:(clear - Hfr; cbn in Hfr; fsetdec)
                    ltac:(clear - Fr; fsetdec)) as Hr.
      rewrite (swap_aenv_fresh_id b δ (Ξl ++ Θ0)) in Hr
        by (clear - Hfr Fr; fsetdec).
      rewrite (swap_aenv_fresh_id b δ Ξ) in Hr
        by (clear - HbΞ Fr HΞf; fsetdec).
      rewrite <- (@close_pskl_subst_var P' b δ ltac:(clear - Fr; fsetdec)).
      apply a_solve_eq__all_l_tophole with (β := δ);
        [ rewrite ftvar_in_aenv_weaken_mid by exact Hfm;
          clear - Fr; fsetdec | ].
      eapply IHe with (Ξl := ((δ ~ abind_tvar) ++ Ξl)) (Ξm := Ξm) (Θ0 := Θ0);
        [ rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia
        | exact Hr | reflexivity | exact Hfm
        | intros x Hx; specialize (Hdisj x Hx);
          assert (Hxδ : x `notin` singleton δ) by (clear - Fr Hx; fsetdec);
          simpl_env in Hdisj; simpl_env;
          clear - Hdisj Hxδ; fsetdec
        | intros x Hx; specialize (Hftv x Hx);
          pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f δ))
            as Hup2;
          assert (Hxδ : x `notin` singleton δ) by (clear - Fr Hx; fsetdec);
          cbn in Hftv, Hup2; clear - Hftv Hup2 Hxδ; fsetdec
        | intros x Hx; specialize (Hout x Hx);
          pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                        P' (pskl_var_f δ) b) as Hsu;
          pose proof (ftvar_in_pskl_close_pskl_wrt_pskl P' b) as Hcl;
          assert (Hxδ : x `notin` singleton δ) by (clear - Fr Hx; fsetdec);
          cbn in Hout, Hsu; clear - Hout Hsu Hcl Hxδ; fsetdec
        | exact Hblk ].
    - (* SE-GuardedGhost *)
      apply a_solve_eq__tophole_r_guarded; [ exact Hg | ].
      eapply IHe with (Ξl := Ξl) (Ξm := Ξm) (Θ0 := Θ0);
        [ cbn; lia | exact Hp | reflexivity | exact Hfm | exact Hdisj
        | exact Hftv | exact Hout | exact Hblk ]. }
Qed.

Lemma a_solve_sub_weaken_mid_flex : forall Θ m P P0 Ξ P' Ξl Ξm Θ0,
  Θ ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' ->
  Θ = Ξl ++ Θ0 -> all_flex_mono Ξm ->
  (forall x, x `in` dom Ξm -> x `notin` dom (Ξl ++ Θ0)) ->
  (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P) ->
  (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P') ->
  (forall x, x `in` dom Ξm -> x `notin` dom Ξ) ->
  (Ξl ++ Ξm ++ Θ0) ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P'.
Proof.
  intros. eapply (proj1 (a_solve_sub_eq_weaken_mid_flex_size
                           (2 * (size_pskl P + size_pskl P0) + 1)));
    eauto.
Qed.

Lemma a_solve_eq_weaken_mid_flex : forall Θ P P0 Ξ P' Ξl Ξm Θ0,
  Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' ->
  Θ = Ξl ++ Θ0 -> all_flex_mono Ξm ->
  (forall x, x `in` dom Ξm -> x `notin` dom (Ξl ++ Θ0)) ->
  (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P) ->
  (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P') ->
  (forall x, x `in` dom Ξm -> x `notin` dom Ξ) ->
  (Ξl ++ Ξm ++ Θ0) ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P'.
Proof.
  intros. eapply (proj2 (a_solve_sub_eq_weaken_mid_flex_size
                           (2 * (size_pskl P + size_pskl P0))));
    eauto.
Qed.

(** The shape the completeness ARROW cases want: prepend a block, no [Ξl]. *)
Lemma a_solve_eq_weaken_flex_block : forall Θ0 P P0 Ξ P' Ξm,
  Θ0 ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' ->
  all_flex_mono Ξm ->
  (forall x, x `in` dom Ξm -> x `notin` dom Θ0) ->
  (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P) ->
  (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P') ->
  (forall x, x `in` dom Ξm -> x `notin` dom Ξ) ->
  (Ξm ++ Θ0) ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P'.
Proof.
  intros Θ0 P P0 Ξ P' Ξm H Hfm Hd HP HP' Hblk.
  exact (@a_solve_eq_weaken_mid_flex Θ0 P P0 Ξ P' nil Ξm Θ0
           H eq_refl Hfm Hd HP HP' Hblk).
Qed.

(* ===================================================================== *)
(*  ⭐ THE κ-EXTENSION PACKAGE, ONCE.                                      *)
(*                                                                        *)
(*  Every P6 conclusion from here down has the SAME first six components   *)
(*  — the solve, its generated block, and the aligned extension of the     *)
(*  metasubstitution over that block — and differs only in the seventh,    *)
(*  its own precision/refinement post-condition.  Naming the shape lets    *)
(*  the four downstream files state their conclusions in one line and,     *)
(*  more importantly, share the two glue lemmas below: [solve_ext_nil]     *)
(*  for a row that generates nothing and [solve_ext_step] for a row that   *)
(*  passes its premise through.  Between them they cover every case that   *)
(*  is not the arrow merge or SE-FlexR itself.                            *)
(*                                                                        *)
(*  [L] is an avoid-set PARAMETER, not an output: at a binder row the      *)
(*  witness must be fixed BEFORE the block is picked (that is what makes   *)
(*  [a_guess_ty_witness_mono]'s ∀ case provable), and at the arrow row the *)
(*  second branch is run at an [L] widened by the first branch's block.   *)
(* ===================================================================== *)
Definition solve_ext (Θ0 Θ : aenv) (Pi P0 : pskl) (L : atoms)
    (Post : metasubst -> pskl -> Prop) : Prop :=
  exists (Ξ : aenv) (Pa : pskl) (κ' : metasubst),
    Θ0 ⊢ₑ Pi ∼ P0 ⤳ Ξ ⨾ Pa /\
    all_flex_mono Ξ /\
    uniq Ξ /\
    keys κ' = keys Ξ /\
    (forall α, α `in` dom Ξ -> α `notin` L) /\
    Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κ' /\
    Post κ' Pa.

(** A row that GENERATES NOTHING needs no extension. *)
Lemma solve_ext_nil : forall Θ0 Θ Pi P0 L Post Pa,
  Θ0 ⊢ₑ Pi ∼ P0 ⤳ nil ⨾ Pa ->
  Post nil Pa ->
  solve_ext Θ0 Θ Pi P0 L Post.
Proof.
  intros Θ0 Θ Pi P0 L Post Pa Hs Hq.
  exists nil, Pa, nil.
  split; [ exact Hs | ].
  split; [ apply Forall_nil | ].
  split; [ apply uniq_nil | ].
  split; [ reflexivity | ].
  split; [ intros α0 Hα0; cbn in Hα0; exfalso; clear - Hα0; fsetdec | ].
  split; [ apply Forall_nil | ].
  exact Hq.
Qed.

(** A row that PASSES ITS PREMISE THROUGH keeps the whole package: the block,
    the extension and the freshness are the premise's, and only the solve
    step and the post-condition change.  This is the shape of every ∀◇ row
    and of every "peel one constructor" row. *)
Lemma solve_ext_step : forall Θ0 Θ Pi P0 Pi' P0' L Post Post',
  (forall Ξ Pa, Θ0 ⊢ₑ Pi' ∼ P0' ⤳ Ξ ⨾ Pa -> Θ0 ⊢ₑ Pi ∼ P0 ⤳ Ξ ⨾ Pa) ->
  (forall κ' Pa, Post' κ' Pa -> Post κ' Pa) ->
  solve_ext Θ0 Θ Pi' P0' L Post' ->
  solve_ext Θ0 Θ Pi P0 L Post.
Proof.
  intros Θ0 Θ Pi P0 Pi' P0' L Post Post' Hstep Hpost
         (Ξ & Pa & κ' & Hs & Hfm & Hu & Hk & Hfr & HF & Hq).
  exists Ξ, Pa, κ'.
  repeat (split; [ solve [ apply Hstep; exact Hs | exact Hfm | exact Hu
                         | exact Hk | exact Hfr | exact HF ] | ]).
  apply Hpost; exact Hq.
Qed.

(** The post-condition alone weakens (the solve and the block are untouched).
    [solve_ext_step] with the identity step. *)
Lemma solve_ext_post : forall Θ0 Θ Pi P0 L Post Post',
  (forall κ' Pa, Post' κ' Pa -> Post κ' Pa) ->
  solve_ext Θ0 Θ Pi P0 L Post' ->
  solve_ext Θ0 Θ Pi P0 L Post.
Proof.
  intros Θ0 Θ Pi P0 L Post Post' Hpost H.
  eapply solve_ext_step; [ intros Ξ Pa Hs; exact Hs | exact Hpost | exact H ].
Qed.

(** The same, with the SOLVE DERIVATION still in hand — several rows read a
    structural fact off it (hole-freedom, the ftv bound) while strengthening
    the post-condition. *)
Lemma solve_ext_post_solve : forall Θ0 Θ Pi P0 L Post Post',
  (forall Ξ κ' Pa, Θ0 ⊢ₑ Pi ∼ P0 ⤳ Ξ ⨾ Pa -> Post' κ' Pa -> Post κ' Pa) ->
  solve_ext Θ0 Θ Pi P0 L Post' ->
  solve_ext Θ0 Θ Pi P0 L Post.
Proof.
  intros Θ0 Θ Pi P0 L Post Post' Hpost
         (Ξ & Pa & κ' & Hs & Hfm & Hu & Hk & Hfr & HF & Hq).
  exists Ξ, Pa, κ'.
  repeat (split; [ solve [ exact Hs | exact Hfm | exact Hu
                         | exact Hk | exact Hfr | exact HF ] | ]).
  eapply Hpost; [ exact Hs | exact Hq ].
Qed.

(** The conclusion, named — it recurs at every site below. *)
Definition cv_mono_concl (Θ0 Θ : aenv) (κ : metasubst) (Δ Ψi : atoms)
    (τ : ptyp) (Pi P0 : pskl) (L : atoms) : Prop :=
  solve_ext Θ0 Θ Pi P0 L
    (fun κ' Pa =>
       Θ ⨟ Δ ⊢ (msubst_pskl (κ' ++ κ) Pa) ⊑ᵖ[ Ψi ] (ptyp_to_uskl_syn τ)).

Lemma cv_mono_nil : forall Θ0 Θ κ Δ Ψi τ Pi P0 L Pa,
  Θ0 ⊢ₑ Pi ∼ P0 ⤳ nil ⨾ Pa ->
  Θ ⨟ Δ ⊢ (msubst_pskl κ Pa) ⊑ᵖ[ Ψi ] (ptyp_to_uskl_syn τ) ->
  cv_mono_concl Θ0 Θ κ Δ Ψi τ Pi P0 L.
Proof.
  intros Θ0 Θ κ Δ Ψi τ Pi P0 L Pa Hs Hq.
  eapply solve_ext_nil; [ exact Hs | cbn [app]; exact Hq ].
Qed.

(** The ∀◇ rows: the solve peels a constructor and the target hops one
    definition chain. *)
Lemma cv_mono_wrap : forall Θ0 Θ κ Δ Ψi τ τe Pi P0 Pi' P0' L,
  a_def_chain Θ τ τe ->
  (forall Ξ Pa, Θ0 ⊢ₑ Pi' ∼ P0' ⤳ Ξ ⨾ Pa -> Θ0 ⊢ₑ Pi ∼ P0 ⤳ Ξ ⨾ Pa) ->
  cv_mono_concl Θ0 Θ κ Δ Ψi τe Pi' P0' L ->
  cv_mono_concl Θ0 Θ κ Δ Ψi τ Pi P0 L.
Proof.
  intros Θ0 Θ κ Δ Ψi τ τe Pi P0 Pi' P0' L Hc Hstep H.
  eapply solve_ext_step;
    [ exact Hstep
    | intros κ' Pa Hq; eapply ad_ppre_chain_fold; [ exact Hc | exact Hq ]
    | exact H ].
Qed.

Lemma a_solve_eq_cv_mono : forall n Θ0 Θ κ Δ Ψi τ Pi P0,
  size_pskl Pi + size_pskl P0 <= n ->
  a_wf_aenv Θ -> a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ Pi -> Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  mono_ptyp τ ->
  a_wf_ptyp Θ τ ->
  delta_def_fresh Δ Θ ->
  Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (ptyp_to_uskl_syn τ) ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (ptyp_to_bskl_syn τ) ->
  forall L, ftvar_in_aenv Θ0 [<=] L ->
  cv_mono_concl Θ0 Θ κ Δ Ψi τ Pi P0 L.
Proof.
  induction n; intros Θ0 Θ κ Δ Ψi τ Pi P0 Hn
    HwfΘ HwfΘ0 HwfPi HwfP0 Hκ Hmτ Hwfτ Hdf Hpre Hrefine L HL.
  { pose proof (size_pskl_min Pi); pose proof (size_pskl_min P0); lia. }
  destruct Pi as [ | nb | α | Pi1 Pi2 | Pib | | Pi' ].
  - (* Pi = unit: resolve the chain to 1, delegate to the Unit case lemma *)
    simpl in Hpre.
    destruct (ad_ppre_unit_subject_chain_inv HwfΘ Hpre eq_refl eq_refl Hmτ)
      as [Hc HΨi].
    pose proof (ad_refine_chain_unfold Hc HwfΘ Hrefine) as Href'.
    simpl in Href'.
    assert (Hpre_u : Θ ⨟ Δ ⊢ (msubst_pskl κ pskl_unit) ⊑ᵖ[ Ψi ] uskl_unit)
      by (simpl; apply ad_ppre__unit; exact HΨi).
    destruct (a_solve_eq_cv_unit (n := S n) (Θ := Θ) (Δ := Δ)
                Hn HwfΘ HwfΘ0 HwfPi HwfP0 Hκ Hpre_u Href')
      as (Pa & Hsolve & Hprec).
    eapply cv_mono_nil;
      [ exact Hsolve | eapply ad_ppre_chain_fold; [ exact Hc | exact Hprec ] ].
  - (* Pi = var_b: not wf *) inversion HwfPi.
  - (* Pi = var_f α: SE-Var / SE-FlexL *)
    eapply cv_mono_nil; [ apply a_solve_eq__var | exact Hpre ].
  - (* Pi = arrow Pi1 Pi2 *)
    assert (HwfPi1 : Θ0 ⨟ empty ⊢ₚₛᵃ Pi1) by (inversion HwfPi; assumption).
    assert (HwfPi2 : Θ0 ⨟ empty ⊢ₚₛᵃ Pi2) by (inversion HwfPi; assumption).
    simpl in Hpre.
    destruct (ad_ppre_arrow_subject_chain_inv HwfΘ Hpre eq_refl eq_refl Hmτ)
      as (τ1 & τ2 & Ψ1 & Ψ2 & Hc & Hm1 & Hm2 & Hp1 & Hp2 & HΨ).
    pose proof (ad_refine_chain_unfold Hc HwfΘ Hrefine) as Href'.
    destruct P0 as [ | nb0 | β | P01 P02 | P0b | | P0' ].
    + (* P0 = unit: refinement absurd *)
      simpl in Href'. inversion Href'.
    + (* P0 = var_b: not wf *) inversion HwfP0.
    + (* P0 = var β: rigid absurd / flexible SE-FlexR + Bridge A *)
      inversion HwfP0; subst;
      match goal with H : _ \/ a_binds_tvar β _ |- _ =>
        destruct H as [Hemp | Habt] end; [ clear - Hemp; fsetdec | ].
      destruct Habt as [Hrig | Hflx].
      * (* rigid: no refinement into an arrow *)
        exfalso.
        assert (Hmid : msubst_pskl κ (pskl_var_f β) = pskl_var_f β)
          by (eapply msubst_pskl_tvar_id; eauto).
        rewrite Hmid in Href'. simpl in Href'.
        eapply ad_refine_syn_rigid_var_nonvar_absurd;
          [ exact HwfΘ | eapply a_inc_binds_tvar; eauto | exact Href'
          | intros β0 Hcc; discriminate Hcc ].
      * (* flexible: SE-FlexR, precision via Bridge A *)
        assert (HΨi : Ψi [=] empty)
          by (eapply ad_ppre_mono_tags_empty;
                [ exact HwfΘ | exact Hpre | reflexivity | exact Hmτ ]).
        (* ⭐ SE-FlexR, REPAIRED.  The output is [guess^TY(P_i)] — the
           accumulated pattern — not the flexible, so the witness is the
           guess and the extension is the one [a_guess_ty_witness_mono]
           builds alongside it.  The old proof went the other way: its
           witness was [β̂] and the obligation needed the whole
           [ad_refine_mono_paint_lhs_ppre] bridge through the refinement.
           Here the precision obligation IS the witness's own output. *)
        assert (Hszg : size_pskl (pskl_arrow Pi1 Pi2) <= S n)
          by (cbn in Hn |- *; lia).
        destruct (@a_guess_ty_witness_mono (S n) Θ0 Θ κ Δ Ψi τ
                    (pskl_arrow Pi1 Pi2) Hszg HwfΘ HwfPi Hmτ Hwfτ Hpre L)
          as (Ξg & Ag & κg & Hgu & Hfmg & Hug & Hkg & Hfrg & HFg & Hqg).
        exists Ξg, (ptyp_to_pskl Ag), κg.
        split; [ apply a_solve_eq__flex_r;
                   [ exact Hflx
                   | split; [ eapply a_wf_pskl_lc; exact HwfPi
                            | intros Hf; inversion Hf ]
                   | apply nonghost_pskl__arrow
                   | apply Hgu; exact HL ] | ].
        split; [ exact Hfmg | ].
        split; [ exact Hug | ].
        split; [ exact Hkg | ].
        split; [ exact Hfrg | ].
        split; [ exact HFg | ].
        exact Hqg.
    + (* ⭐ P0 = arrow P01 P02: SE-Arrow, and THE TWO IHs' EXTENSIONS MERGE.
         This is the one case in the file with real content.

         SE-Arrow THREADS (def_extra.v, §2(2) of the hand-off): its second
         premise runs at [Ξ1 ++ Θ0] and its output block is [Ξ2 ++ Ξ1].  So
         the second IH is invoked AT THAT CONTEXT, under the metasubstitution
         the first branch has ALREADY extended — which is exactly what the
         first branch's package licenses ([a_inc_flex_prefix_build]).  Running
         both at [Θ0] instead is not merely inconvenient, it is unsound
         bookkeeping: the two blocks could pick the same atom and conflate two
         independently-invented flexibles.

         The avoid-sets are the witness lemma's ([a_guess_ty_witness_mono]'s
         arrow case): BOTH IHs avoid BOTH branches' sources, and the second
         additionally avoids [dom Ξ1].  That is what makes each branch's
         extension invisible to the other's result below — [Heq1] here, and
         [Heqi2]/[Heqp2] for the second IH's own premises. *)
      assert (HwfP01 : Θ0 ⨟ empty ⊢ₚₛᵃ P01) by (inversion HwfP0; assumption).
      assert (HwfP02 : Θ0 ⨟ empty ⊢ₚₛᵃ P02) by (inversion HwfP0; assumption).
      assert (Hwfar : a_wf_ptyp Θ (ptyp_arrow τ1 τ2))
        by (eapply a_def_chain_wf; eassumption).
      assert (Hwf1 : a_wf_ptyp Θ τ1) by (inversion Hwfar; assumption).
      assert (Hwf2 : a_wf_ptyp Θ τ2) by (inversion Hwfar; assumption).
      simpl in Href'.
      inversion Href'; subst.
      match goal with
      | Hr1 : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl κ P01) ⊳ _,
        Hr2 : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl κ P02) ⊳ _ |- _ =>
        rename Hr1 into Href1; rename Hr2 into Href2
      end.
      (* ---- branch 1, at [Θ0], avoiding both sources ---- *)
      assert (HL1 : ftvar_in_aenv Θ0
                    [<=] L `union` ftvar_in_pskl Pi1 `union` ftvar_in_pskl Pi2
                           `union` ftvar_in_pskl P01 `union` ftvar_in_pskl P02)
        by (clear - HL; fsetdec).
      destruct (IHn Θ0 Θ κ Δ Ψ1 τ1 Pi1 P01
                  ltac:(simpl in Hn; lia)
                  HwfΘ HwfΘ0 HwfPi1 HwfP01 Hκ Hm1 Hwf1 Hdf Hp1 Href1
                  (L `union` ftvar_in_pskl Pi1 `union` ftvar_in_pskl Pi2
                     `union` ftvar_in_pskl P01 `union` ftvar_in_pskl P02)
                  HL1)
        as (Ξ1 & Pa1 & κa & Hs1 & Hfm1 & Hu1 & Hk1 & Hfr1 & HF1 & Hq1).
      assert (Hdκa : dom κa [=] dom Ξ1) by (apply keys_eq_dom; exact Hk1).
      (* ---- move everything the second IH needs to [Ξ1 ++ Θ0] ---- *)
      assert (HΞ1Θ0 : forall α0, α0 `in` dom Ξ1 -> α0 `notin` dom Θ0).
      { intros α0 Hα0. specialize (Hfr1 α0 Hα0).
        pose proof (dom_subset_ftvar_in_aenv Θ0) as Hd.
        clear - Hfr1 Hd HL; fsetdec. }
      assert (Hwfblk : a_wf_aenv (Ξ1 ++ Θ0))
        by (apply a_wf_aenv_prepend_flex_block; assumption).
      assert (Hκ1 : (κa ++ κ) ∷ (Ξ1 ++ Θ0) ⊑ Θ)
        by (apply a_inc_flex_prefix_build; assumption).
      assert (HwfPi2' : (Ξ1 ++ Θ0) ⨟ empty ⊢ₚₛᵃ Pi2)
        by (apply a_wf_pskl_app_weaken; exact HwfPi2).
      assert (HwfP02' : (Ξ1 ++ Θ0) ⨟ empty ⊢ₚₛᵃ P02)
        by (apply a_wf_pskl_app_weaken; exact HwfP02).
      assert (Heqi2 : msubst_pskl (nil ++ κa ++ κ) Pi2
                      = msubst_pskl (nil ++ κ) Pi2).
      { apply msubst_pskl_mid_skip. intros α0 Hα0.
        assert (Hin : α0 `in` dom Ξ1) by (clear - Hα0 Hdκa; fsetdec).
        specialize (Hfr1 α0 Hin). clear - Hfr1; fsetdec. }
      assert (Heqp2 : msubst_pskl (nil ++ κa ++ κ) P02
                      = msubst_pskl (nil ++ κ) P02).
      { apply msubst_pskl_mid_skip. intros α0 Hα0.
        assert (Hin : α0 `in` dom Ξ1) by (clear - Hα0 Hdκa; fsetdec).
        specialize (Hfr1 α0 Hin). clear - Hfr1; fsetdec. }
      cbn [app] in Heqi2, Heqp2.
      assert (Hp2' : Θ ⨟ Δ ⊢ (msubst_pskl (κa ++ κ) Pi2)
                             ⊑ᵖ[ Ψ2 ] (ptyp_to_uskl_syn τ2))
        by (rewrite Heqi2; exact Hp2).
      assert (Href2' : Θ ⨟ empty ⊢ᵣᵃ
                (pskl_to_bskl_inh (msubst_pskl (κa ++ κ) P02))
                ⊳ (ptyp_to_bskl_syn τ2))
        by (rewrite Heqp2; exact Href2).
      assert (HL2 : ftvar_in_aenv (Ξ1 ++ Θ0)
                    [<=] L `union` ftvar_in_pskl Pi1 `union` ftvar_in_pskl Pi2
                           `union` ftvar_in_pskl P01 `union` ftvar_in_pskl P02
                           `union` dom Ξ1).
      { rewrite ftvar_in_aenv_app.
        pose proof (all_flex_mono_ftvar_in_aenv Hfm1) as Hf1.
        clear - HL Hf1; fsetdec. }
      (* ---- branch 2, at [Ξ1 ++ Θ0], additionally avoiding [dom Ξ1] ---- *)
      destruct (IHn (Ξ1 ++ Θ0) Θ (κa ++ κ) Δ Ψ2 τ2 Pi2 P02
                  ltac:(simpl in Hn; lia)
                  HwfΘ Hwfblk HwfPi2' HwfP02' Hκ1 Hm2 Hwf2 Hdf Hp2' Href2'
                  (L `union` ftvar_in_pskl Pi1 `union` ftvar_in_pskl Pi2
                     `union` ftvar_in_pskl P01 `union` ftvar_in_pskl P02
                     `union` dom Ξ1)
                  HL2)
        as (Ξ2 & Pa2 & κb & Hs2 & Hfm2 & Hu2 & Hk2 & Hfr2 & HF2 & Hq2).
      assert (Hdκb : dom κb [=] dom Ξ2) by (apply keys_eq_dom; exact Hk2).
      assert (Hdisj : disjoint Ξ2 Ξ1).
      { unfold disjoint. intros α0 Hα0.
        assert (Hin2 : α0 `in` dom Ξ2) by (clear - Hα0; fsetdec).
        specialize (Hfr2 α0 Hin2). clear - Hα0 Hfr2; fsetdec. }
      (* the FIRST branch's result is bounded by its own inputs plus its own
         block, all three of which the second block was told to dodge *)
      assert (HPa1 : ftvar_in_pskl Pa1
                     [<=] ftvar_in_pskl Pi1 `union` ftvar_in_pskl P01
                            `union` dom Ξ1)
        by (eapply a_solve_eq_ftv; exact Hs1).
      assert (Heq1 : msubst_pskl (nil ++ κb ++ (κa ++ κ)) Pa1
                     = msubst_pskl (nil ++ (κa ++ κ)) Pa1).
      { apply msubst_pskl_mid_skip. intros α0 Hα0.
        assert (Hin2 : α0 `in` dom Ξ2) by (clear - Hα0 Hdκb; fsetdec).
        specialize (Hfr2 α0 Hin2). clear - Hfr2 HPa1; fsetdec. }
      cbn [app] in Heq1.
      exists (Ξ2 ++ Ξ1), (pskl_arrow Pa1 Pa2), (κb ++ κa).
      split; [ apply a_solve_eq__arrow; [ exact Hs1 | exact Hs2 ] | ].
      split; [ apply all_flex_mono_app; assumption | ].
      split; [ clear - Hu1 Hu2 Hdisj; solve_uniq | ].
      split; [ rewrite ! keys_app; rewrite Hk1, Hk2; reflexivity | ].
      split; [ intros α0 Hα0; rewrite dom_app in Hα0;
               destruct (union_1 Hα0) as [Hin2 | Hin1];
                 [ specialize (Hfr2 α0 Hin2); clear - Hfr2; fsetdec
                 | specialize (Hfr1 α0 Hin1); clear - Hfr1; fsetdec ] | ].
      split; [ apply Forall_app; split; assumption | ].
      eapply ad_ppre_chain_fold; [ exact Hc | ].
      rewrite list_app_assoc. cbn [msubst_pskl ptyp_to_uskl_syn].
      rewrite Heq1.
      apply ad_ppre__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
        [ exact Hq1 | exact Hq2 | exact HΨ ].
    + (* P0 = all_syn: refinement absurd *)
      simpl in Href'.
      exfalso.
      eapply ad_refine_allinh_lhs_mono_absurd;
        [ exact HwfΘ | exact Href' | reflexivity | reflexivity
        | apply mono_ptyp__arrow; assumption ].
    + (* P0 = hole: SE-VacuousR *)
      eapply cv_mono_nil; [ apply a_solve_eq__hole_r | exact Hpre ].
    + (* P0 = tophole P0': GuardedGhost-right, recurse at the resolved arrow *)
      assert (HwfP0' : Θ0 ⨟ empty ⊢ₚₛᵃ P0') by (inversion HwfP0; assumption).
      assert (Hwfar : a_wf_ptyp Θ (ptyp_arrow τ1 τ2))
        by (eapply a_def_chain_wf; eassumption).
      simpl in Href'.
      inversion Href'; subst.
      assert (Hpre' : Θ ⨟ Δ ⊢ msubst_pskl κ (pskl_arrow Pi1 Pi2) ⊑ᵖ[ Ψi ]
                        (ptyp_to_uskl_syn (ptyp_arrow τ1 τ2)))
        by (simpl; eapply ad_ppre__arrow;
              [ exact Hp1 | exact Hp2 | exact HΨ ]).
      assert (Hcv : cv_mono_concl Θ0 Θ κ Δ Ψi (ptyp_arrow τ1 τ2)
                      (pskl_arrow Pi1 Pi2) P0' L).
      { match goal with
        | Hin : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl κ P0') ⊳ _ |- _ =>
          apply (IHn Θ0 Θ κ Δ Ψi (ptyp_arrow τ1 τ2) (pskl_arrow Pi1 Pi2) P0'
                   ltac:(simpl in Hn; simpl; lia)
                   HwfΘ HwfΘ0 HwfPi HwfP0' Hκ
                   ltac:(apply mono_ptyp__arrow; assumption)
                   Hwfar Hdf Hpre' Hin L HL)
        end. }
      eapply cv_mono_wrap; [ exact Hc | | exact Hcv ].
      intros Ξ0 Pa Hs. apply a_solve_eq__tophole_r_guarded;
        [ apply guarded_pskl__arrow;
            [ eapply a_wf_pskl_lc; exact HwfPi1
            | eapply a_wf_pskl_lc; exact HwfPi2 ]
        | exact Hs ].
  - (* Pi = all_syn: precision absurd *)
    simpl in Hpre.
    exfalso.
    eapply ad_ppre_allsyn_subject_mono_absurd;
      [ exact HwfΘ | exact Hpre | reflexivity | reflexivity | exact Hmτ ].
  - (* Pi = □: SE-GhostL, precision via Bridge B *)
    simpl in Hpre.
    eapply cv_mono_nil; [ apply a_solve_eq__hole_l | ].
    eapply ad_refine_inh_hole_ppre with (Δr := empty);
      [ exact HwfΘ | clear; fsetdec | exact Hrefine | reflexivity | reflexivity
      | exact Hmτ | exact Hdf | exact Hpre ].
  - (* Pi = ∀◇.Pi' — every row here is a PASS-THROUGH, which is what
       [cv_mono_wrap] is for: the block, the extension and the freshness are
       the premise's, and only the solve step and the target move. *)
    assert (HgPi' : guarded_pskl Pi') by (inversion HwfPi; assumption).
    assert (HwfPi' : Θ0 ⨟ empty ⊢ₚₛᵃ Pi') by (inversion HwfPi; assumption).
    simpl in Hpre.
    destruct (ad_ppre_tophole_subject_chain_inv HwfΘ Hpre eq_refl eq_refl Hmτ)
      as (τe & Hc & Hme & Hp').
    assert (Hwfe : a_wf_ptyp Θ τe) by (eapply a_def_chain_wf; eassumption).
    pose proof (ad_refine_chain_unfold Hc HwfΘ Hrefine) as Href'.
    destruct P0 as [ | nb0 | β | P01 P02 | P0b | | P0' ].
    + (* P0 = unit: GhostGuarded *)
      assert (Hcv : cv_mono_concl Θ0 Θ κ Δ Ψi τe Pi' pskl_unit L)
        by (apply (IHn Θ0 Θ κ Δ Ψi τe Pi' pskl_unit
                     ltac:(simpl in Hn; simpl; lia)
                     HwfΘ HwfΘ0 HwfPi' HwfP0 Hκ Hme Hwfe Hdf Hp' Href' L HL)).
      eapply cv_mono_wrap; [ exact Hc | | exact Hcv ].
      intros Ξ0 Pa Hs. apply a_solve_eq__tophole_l_guarded;
        [ apply guarded_pskl__unit | exact Hs ].
    + (* P0 = var_b: not wf *) inversion HwfP0.
    + (* P0 = var β: GhostGuarded (var is guarded) *)
      assert (Hcv : cv_mono_concl Θ0 Θ κ Δ Ψi τe Pi' (pskl_var_f β) L)
        by (apply (IHn Θ0 Θ κ Δ Ψi τe Pi' (pskl_var_f β)
                     ltac:(simpl in Hn; simpl; lia)
                     HwfΘ HwfΘ0 HwfPi' HwfP0 Hκ Hme Hwfe Hdf Hp' Href' L HL)).
      eapply cv_mono_wrap; [ exact Hc | | exact Hcv ].
      intros Ξ0 Pa Hs. apply a_solve_eq__tophole_l_guarded;
        [ apply guarded_pskl__var | exact Hs ].
    + (* P0 = arrow: GhostGuarded *)
      assert (HwfP01 : Θ0 ⨟ empty ⊢ₚₛᵃ P01) by (inversion HwfP0; assumption).
      assert (HwfP02 : Θ0 ⨟ empty ⊢ₚₛᵃ P02) by (inversion HwfP0; assumption).
      assert (Hcv : cv_mono_concl Θ0 Θ κ Δ Ψi τe Pi' (pskl_arrow P01 P02) L)
        by (apply (IHn Θ0 Θ κ Δ Ψi τe Pi' (pskl_arrow P01 P02)
                     ltac:(simpl in Hn; simpl; lia)
                     HwfΘ HwfΘ0 HwfPi' HwfP0 Hκ Hme Hwfe Hdf Hp' Href' L HL)).
      eapply cv_mono_wrap; [ exact Hc | | exact Hcv ].
      intros Ξ0 Pa Hs. apply a_solve_eq__tophole_l_guarded;
        [ apply guarded_pskl__arrow;
            [ eapply a_wf_pskl_lc; exact HwfP01
            | eapply a_wf_pskl_lc; exact HwfP02 ]
        | exact Hs ].
    + (* P0 = all_syn: refinement absurd *)
      simpl in Href'.
      exfalso.
      eapply ad_refine_allinh_lhs_mono_absurd;
        [ exact HwfΘ | exact Href' | reflexivity | reflexivity | exact Hme ].
    + (* P0 = hole: SE-VacuousR *)
      eapply cv_mono_nil; [ apply a_solve_eq__hole_r | exact Hpre ].
    + (* P0 = ∀◇.P0': SE-UnivGhost, second chain hop off the ∀◇ counterpart.
         NOT a [cv_mono_wrap]: this row RE-WRAPS its premise's output in a
         [∀◇], so the package has to be rebuilt by hand — but the block and
         the extension still pass through untouched. *)
      assert (HwfP0' : Θ0 ⨟ empty ⊢ₚₛᵃ P0') by (inversion HwfP0; assumption).
      simpl in Href'.
      destruct (ad_refine_tophole_lhs_chain_inv HwfΘ Href' eq_refl eq_refl Hme)
        as (τf & Hc2 & Hmf & Hin).
      assert (Hwff : a_wf_ptyp Θ τf) by (eapply a_def_chain_wf; eassumption).
      pose proof (ad_ppre_chain_unfold Hc2 HwfΘ Hdf Hp') as Hp''.
      destruct (IHn Θ0 Θ κ Δ Ψi τf Pi' P0'
                  ltac:(simpl in Hn; simpl; lia)
                  HwfΘ HwfΘ0 HwfPi' HwfP0' Hκ Hmf Hwff Hdf Hp'' Hin L HL)
        as (Ξ0 & Pa & κ' & Hs & Hfm & Hu & Hk & Hfr & HF & Hq).
      exists Ξ0, (pskl_tophole Pa), κ'.
      split; [ apply a_solve_eq__tophole_both; exact Hs | ].
      split; [ exact Hfm | ].
      split; [ exact Hu | ].
      split; [ exact Hk | ].
      split; [ exact Hfr | ].
      split; [ exact HF | ].
      eapply ad_ppre_chain_fold;
        [ eapply a_def_chain_trans; [ exact Hc | exact Hc2 ] | ].
      simpl. apply ad_ppre__tophole_remove. exact Hq.
Qed.

(* ==== the Var consistency case: the τ = α instance ====

   ⚠️ [a_binds_tvar α Θ] is a NEW premise (2026-08-04).  It is the [τ = α]
   reading of [a_solve_eq_cv_mono]'s own [a_wf_ptyp Θ τ], which the repaired
   SE-FlexR forces: [guess^TY]'s κ-extension sends the flexible it invents at
   a [◇] to the monotype standing at that position, and [a_inc__flex] admits
   only a monotype WELL-FORMED IN THE TARGET.  It is the paper's usual
   external wf side condition (docs/WF-SIDE-CONDITIONS.md), not a weakening:
   the counterpart of a completeness statement is always assumed well-formed
   in prose. *)
Lemma a_solve_eq_cv_var : forall n Θ0 Θ κ Δ Ψi α Pi P0,
  size_pskl Pi + size_pskl P0 <= n ->
  a_wf_aenv Θ -> a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ Pi -> Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  a_binds_tvar α Θ ->
  delta_def_fresh Δ Θ ->
  Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (uskl_var_f α) ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (bskl_var_f α) ->
  forall L, ftvar_in_aenv Θ0 [<=] L ->
  cv_mono_concl Θ0 Θ κ Δ Ψi (ptyp_var_f α) Pi P0 L.
Proof.
  intros n Θ0 Θ κ Δ Ψi α Pi P0 Hn HwfΘ HwfΘ0 HwfPi HwfP0 Hκ Hbα Hdf Hpre
         Hrefine L HL.
  eapply a_solve_eq_cv_mono with (τ := ptyp_var_f α); eauto.
  - auto with frost.
  - apply a_wf_ptyp__var; exact Hbα.
Qed.

(* ===================================================================== *)
(*  GhostG case kit: a dotted-ghost target [holeg] / refinement into a    *)
(*  bare [□] admit ONLY a [□] on the other side — mono paints and         *)
(*  guarded shapes have no rule into them.                                 *)
(* ===================================================================== *)

Lemma d_tags_skl_holeg_inv : forall Ψ,
  d_tags_skl Ψ uskl_holeg -> Ψ [=] empty.
Proof. intros Ψ H; inversion H; subst; auto. Qed.

Lemma ad_ppre_mono_paint_holeg_absurd : forall Θ Δ Ψ P ψ,
  a_wf_aenv Θ ->
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  ψ = uskl_holeg ->
  forall τb, P = ptyp_to_pskl τb -> mono_ptyp τb ->
  False.
Proof.
  intros Θ Δ Ψ P ψ HwfΘ H; induction H; intros Heqψ τb HeqS Hmb;
    try discriminate Heqψ.
  - (* hole: subject □ is never a paint *)
    destruct τb; simpl in HeqS; discriminate HeqS.
  - (* tophole_remove: subject ∀◇ is never a paint *)
    destruct τb; simpl in HeqS; discriminate HeqS.
  - (* flex_l: unfold the definition, still a mono paint *)
    destruct τb; simpl in HeqS; try discriminate HeqS.
    inversion HeqS; subst.
    eapply IHad_partial_precise;
      [ exact HwfΘ | reflexivity | reflexivity
      | eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

Lemma ad_refine_mono_paint_hole_rhs_absurd : forall Θ Δr Q' Q,
  a_wf_aenv Θ ->
  Θ ⨟ Δr ⊢ᵣᵃ Q' ⊳ Q ->
  Q = bskl_hole ->
  forall τb, Q' = ptyp_to_bskl_syn τb -> mono_ptyp τb ->
  False.
Proof.
  intros Θ Δr Q' Q HwfΘ H; induction H; intros HeqQ τb HeqL Hmb;
    try discriminate HeqQ.
  - (* hole: LHS □ is never a paint *)
    destruct τb; simpl in HeqL; discriminate HeqL.
  - (* tophole_remove: LHS ∀◇ is never a paint *)
    destruct τb; simpl in HeqL; discriminate HeqL.
  - (* flex_l *)
    destruct τb; simpl in HeqL; try discriminate HeqL.
    inversion HeqL; subst.
    eapply IHad_refine_syn;
      [ exact HwfΘ | reflexivity | reflexivity
      | eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

(* ==== the GhostG consistency case, as a standalone lemma ==== *)
(* No size induction: both sides are forced to [□]; every other shape is
   premise-absurd (a ∀◇'s guarded body dies one level down). *)
Lemma a_solve_eq_cv_ghostg : forall Θ0 Θ κ Δ Ψi Pi P0,
  a_wf_aenv Θ -> a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ Pi -> Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] uskl_holeg ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ bskl_hole ->
  (* the block is pinned to [nil]: the only non-absurd row is SE-GhostL,
     which generates nothing, so no κ-extension is needed here *)
  exists Pa, Θ0 ⊢ₑ Pi ∼ P0 ⤳ nil ⨾ Pa /\
             Θ ⨟ Δ ⊢ (msubst_pskl κ Pa) ⊑ᵖ[ Ψi ] uskl_holeg.
Proof.
  intros Θ0 Θ κ Δ Ψi Pi P0 HwfΘ HwfΘ0 HwfPi HwfP0 Hκ Hpre Hrefine.
  assert (Habs_pre_var : forall v Ψ',
            Θ ⨟ Δ ⊢ (msubst_pskl κ (pskl_var_f v)) ⊑ᵖ[ Ψ' ] uskl_holeg ->
            False).
  { intros v Ψ' Hp. simpl in Hp.
    eapply ad_ppre_mono_paint_holeg_absurd;
      [ exact HwfΘ | exact Hp | reflexivity | reflexivity
      | eapply a_inc_lookup_mono; eauto ]. }
  assert (Habs_ref_var : forall v,
            Θ ⨟ empty ⊢ᵣᵃ
              (pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f v))) ⊳ bskl_hole ->
            False).
  { intros v Hr. simpl in Hr.
    assert (Hml : mono_ptyp (msubst_lookup κ v))
      by (eapply a_inc_lookup_mono; eauto).
    rewrite (ptyp_to_bskl_inh_syn_eq Hml) in Hr.
    eapply ad_refine_mono_paint_hole_rhs_absurd;
      [ exact HwfΘ | exact Hr | reflexivity | reflexivity | exact Hml ]. }
  destruct Pi as [ | nb | α | Pi1 Pi2 | Pib | | Pi' ].
  - (* Pi = unit: no precision rule into holeg *)
    simpl in Hpre. inversion Hpre.
  - (* Pi = var_b: not wf *) inversion HwfPi.
  - (* Pi = var: a mono paint, absurd *)
    exfalso. eapply Habs_pre_var. exact Hpre.
  - (* Pi = arrow: absurd *) simpl in Hpre. inversion Hpre.
  - (* Pi = all_syn: absurd *) simpl in Hpre. inversion Hpre.
  - (* Pi = □: the live column *)
    destruct P0 as [ | nb0 | β | P01 P02 | P0b | | P0' ].
    + (* P0 = unit: no refinement into □ *)
      simpl in Hrefine. inversion Hrefine.
    + (* P0 = var_b: not wf *) inversion HwfP0.
    + (* P0 = var: a mono paint, absurd *)
      exfalso. eapply Habs_ref_var. exact Hrefine.
    + (* P0 = arrow: absurd *) simpl in Hrefine. inversion Hrefine.
    + (* P0 = all_syn: absurd *) simpl in Hrefine. inversion Hrefine.
    + (* P0 = □: SE-GhostL, Pa := □ *)
      exists pskl_hole; split; [ apply a_solve_eq__hole_l | exact Hpre ].
    + (* P0 = ∀◇.P0': strip; the guarded body dies *)
      simpl in Hrefine. inversion Hrefine; subst.
      exfalso.
      assert (HgP0' : guarded_pskl P0') by (inversion HwfP0; assumption).
      inversion HgP0'; subst.
      * (* unit *)
        match goal with
        | Hin : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl κ pskl_unit) ⊳ _
          |- _ => simpl in Hin; inversion Hin
        end.
      * (* var *)
        match goal with
        | Hin : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f _)) ⊳ _
          |- _ => eapply Habs_ref_var; exact Hin
        end.
      * (* arrow *)
        match goal with
        | Hin : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl κ (pskl_arrow _ _)) ⊳ _
          |- _ => simpl in Hin; inversion Hin
        end.
  - (* Pi = ∀◇.Pi': strip; the guarded body dies *)
    simpl in Hpre. inversion Hpre; subst.
    exfalso.
    assert (HgPi' : guarded_pskl Pi') by (inversion HwfPi; assumption).
    inversion HgPi'; subst.
    + (* unit *)
      match goal with
      | Hp' : _ ⨟ _ ⊢ msubst_pskl κ pskl_unit ⊑ᵖ[ _ ] _ |- _ =>
          simpl in Hp'; inversion Hp'
      end.
    + (* var *)
      match goal with
      | Hp' : _ ⨟ _ ⊢ msubst_pskl κ (pskl_var_f _) ⊑ᵖ[ _ ] _ |- _ =>
          eapply Habs_pre_var; exact Hp'
      end.
    + (* arrow *)
      match goal with
      | Hp' : _ ⨟ _ ⊢ msubst_pskl κ (pskl_arrow _ _) ⊑ᵖ[ _ ] _ |- _ =>
          simpl in Hp'; inversion Hp'
      end.
Qed.

(* ===================================================================== *)
(*  Flex-case kit: a mono paint is a tag-sorted (empty-tag) decorated     *)
(*  skeleton — the ψa-side payload for the flex_l target switch.          *)
(* ===================================================================== *)

Lemma is_tskl_mono_paint : forall τ,
  mono_ptyp τ -> is_tskl (ptyp_to_uskl_syn τ).
Proof. intros τ Hm; induction Hm; simpl; constructor; auto. Qed.

Lemma d_tags_skl_mono_paint : forall τ,
  mono_ptyp τ -> d_tags_skl empty (ptyp_to_uskl_syn τ).
Proof.
  intros τ Hm; induction Hm; simpl.
  - apply d_tags_skl__unit; fsetdec.
  - apply d_tags_skl__var; fsetdec.
  - apply d_tags_skl__arrow with (Ψ1 := empty) (Ψ2 := empty);
      [ assumption | assumption | fsetdec | fsetdec ].
Qed.

Lemma uskl_ghost_free_mono_paint : forall τ,
  mono_ptyp τ -> uskl_ghost_free (ptyp_to_uskl_syn τ).
Proof. intros τ Hm; induction Hm; simpl; constructor; auto. Qed.

Lemma a_tags_sort_mono_paint : forall NM τ,
  mono_ptyp τ -> a_tags_sort NM empty (ptyp_to_uskl_syn τ).
Proof.
  intros NM τ Hm; destruct NM; constructor;
    auto using is_tskl_mono_paint, d_tags_skl_mono_paint,
               uskl_ghost_free_mono_paint.
Qed.

(* ===================================================================== *)
(*  Topholeg case kit: component tags-sort, and the two mono-paint         *)
(*  absurdities against dotted-∀◇ targets / plain-∀◇ refinement RHS.       *)
(* ===================================================================== *)

Lemma a_tags_sort_topholeg_inv : forall NM Ψ ψ,
  a_tags_sort NM Ψ (uskl_topholeg ψ) -> a_tags_sort NM Ψ ψ.
Proof.
  intros NM Ψ ψ H; inversion H; subst.
  - apply a_tags_sort__sk;
      [ match goal with Ht : is_tskl (uskl_topholeg _) |- _ =>
          inversion Ht; subst; assumption end
      | match goal with Hd : d_tags_skl _ (uskl_topholeg _) |- _ =>
          inversion Hd; subst; assumption end ].
  - match goal with Hg : uskl_ghost_free (uskl_topholeg _) |- _ =>
      inversion Hg end.
Qed.

Lemma ad_ppre_mono_paint_topholeg_absurd : forall Θ Δ Ψ P ψ,
  a_wf_aenv Θ ->
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  forall ψ0, ψ = uskl_topholeg ψ0 ->
  forall τb, P = ptyp_to_pskl τb -> mono_ptyp τb ->
  False.
Proof.
  intros Θ Δ Ψ P ψ HwfΘ H; induction H; intros ψ0' Heqψ τb HeqS Hmb;
    try discriminate Heqψ.
  - (* hole *) destruct τb; simpl in HeqS; discriminate HeqS.
  - (* tophole_remove *) destruct τb; simpl in HeqS; discriminate HeqS.
  - (* tophole_keep *) destruct τb; simpl in HeqS; discriminate HeqS.
  - (* flex_l *)
    destruct τb; simpl in HeqS; try discriminate HeqS.
    inversion HeqS; subst.
    eapply IHad_partial_precise;
      [ exact HwfΘ | reflexivity | reflexivity
      | eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

Lemma ad_refine_mono_paint_tophole_rhs_absurd : forall Θ Δr Q' Q,
  a_wf_aenv Θ ->
  Θ ⨟ Δr ⊢ᵣᵃ Q' ⊳ Q ->
  forall Q0, Q = bskl_tophole Q0 ->
  forall τb, Q' = ptyp_to_bskl_syn τb -> mono_ptyp τb ->
  False.
Proof.
  intros Θ Δr Q' Q HwfΘ H; induction H; intros Q0' HeqQ τb HeqL Hmb;
    try discriminate HeqQ.
  - (* hole *) destruct τb; simpl in HeqL; discriminate HeqL.
  - (* tophole_remove *) destruct τb; simpl in HeqL; discriminate HeqL.
  - (* tophole_keep *) destruct τb; simpl in HeqL; discriminate HeqL.
  - (* flex_l *)
    destruct τb; simpl in HeqL; try discriminate HeqL.
    inversion HeqL; subst.
    eapply IHad_refine_syn;
      [ exact HwfΘ | reflexivity | reflexivity
      | eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

(* ===================================================================== *)
(*  The flexible-apartness premise (Arrow-case repair, option (i)).        *)
(*  [flex_apart Θ0 Δρ P0 ψa]: every FLEXIBLE-variable position of the      *)
(*  solve counterpart P0 faces a Δρ-CLEAN part of ψa (no ρ-replaced leaf   *)
(*  below it).  This is the reachability fact the LE-FlexR freshening      *)
(*  guarantees (cex_p6_flex_freshened.v): a raw Θ0-flex payload never      *)
(*  sits opposite a compound covering a ρ-substituted position.  It is     *)
(*  VACUOUS at every ρ = id call site (fa_clean with Δρ = ∅) and is        *)
(*  maintained internally by the P6 lemma cluster only.                    *)
(* ===================================================================== *)

(** Adding a RIGID entry creates no flexible variable — the side condition the
    [fa_flexfree] row makes every context weakening carry.  ⚙️ The lemma itself
    now sits at the top of the file ([a_flex_tvar_strip_tvar], §"solve context
    change"), where [a_solve_eq_strengthen_tvar] needs it; this duplicate was
    removed 2026-08-04. *)

(* ===================================================================== *)
(*  Raw-flexible-freedom of a payload                                     *)
(* ===================================================================== *)

(** [pskl_flex_free Θ0 P]: no free variable of [P] is a FLEXIBLE of [Θ0]
    (declared or defined).  Stated over [ftvar_in_pskl] rather than
    structurally, so the opening / weakening facts below are set algebra
    instead of inductions. *)
Definition pskl_flex_free (Θ0 : aenv) (P : pskl) : Prop :=
  forall α, α `in` ftvar_in_pskl P -> ~ a_flex_tvar Θ0 α.

Lemma pskl_flex_free_arrow_inv : forall Θ0 P1 P2,
  pskl_flex_free Θ0 (pskl_arrow P1 P2) ->
  pskl_flex_free Θ0 P1 /\ pskl_flex_free Θ0 P2.
Proof.
  intros Θ0 P1 P2 H; split; intros α Hα; apply H; simpl; clear - Hα; fsetdec.
Qed.

Lemma pskl_flex_free_tophole_inv : forall Θ0 P,
  pskl_flex_free Θ0 (pskl_tophole P) -> pskl_flex_free Θ0 P.
Proof. intros Θ0 P H α Hα; apply H; simpl; exact Hα. Qed.

(** Substituting a NON-flexible variable preserves flex-freedom. *)
Lemma pskl_flex_free_subst : forall Θ0 P α1 α2,
  pskl_flex_free Θ0 P ->
  ~ a_flex_tvar Θ0 α2 ->
  pskl_flex_free Θ0 (subst_pskl_in_pskl (pskl_var_f α2) α1 P).
Proof.
  intros Θ0 P α1 α2 H H2 α Hα.
  pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P (pskl_var_f α2) α1)
    as Hup.
  simpl in Hup.
  destruct (α == α2) as [-> | Hne]; [ exact H2 | ].
  apply H. clear - Hα Hup Hne; fsetdec.
Qed.

(** Opening a ∀-body with a fresh RIGID binder, in the context extended by
    that binder. *)
Lemma pskl_flex_free_open_tvar : forall Θ0 P γ,
  pskl_flex_free Θ0 (pskl_all_syn P) ->
  γ `notin` dom Θ0 ->
  pskl_flex_free ((γ ~ abind_tvar) ++ Θ0)
    (open_pskl_wrt_pskl P (pskl_var_f γ)).
Proof.
  intros Θ0 P γ H Hγ α Hα Hflex.
  pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f γ)) as Hup.
  simpl in Hup.
  destruct (α == γ) as [-> | Hne].
  - (* the fresh binder is RIGID in the extended context *)
    destruct Hflex as [Hb | [τ Hb]];
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
      solve [ discriminate Habs
            | exfalso; apply Hγ; eapply binds_In; exact Hb' ].
  - apply (H α); [ simpl; clear - Hα Hup Hne; fsetdec | ].
    destruct Hflex as [Hb | [τ Hb]];
      [ left | right; exists τ ];
      (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq _] | Hb'];
       [ contradiction | exact Hb' ]).
Qed.

Lemma pskl_flex_free_weaken_tvar : forall Θ0 P γ,
  pskl_flex_free Θ0 P ->
  pskl_flex_free ((γ ~ abind_tvar) ++ Θ0) P.
Proof.
  intros Θ0 P γ H α Hα Hflex.
  apply (H α Hα).
  destruct Hflex as [Hb | [τ Hb]];
    [ left | right; exists τ ];
    (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
     [ discriminate Habs | exact Hb' ]).
Qed.

Inductive flex_apart (Θ0 : aenv) (Δρ : atoms) : pskl -> uskl -> Prop :=
| fa_clean : forall P0 ψa,
    (ftvar_in_uskl ψa) ∩ Δρ [=] empty ->
    flex_apart Θ0 Δρ P0 ψa
| fa_unit : forall ψa, flex_apart Θ0 Δρ pskl_unit ψa
| fa_var_rigid : forall α ψa,
    binds α abind_tvar Θ0 ->
    flex_apart Θ0 Δρ (pskl_var_f α) ψa
| fa_hole : forall ψa, flex_apart Θ0 Δρ pskl_hole ψa
| fa_tophole : forall P0 ψa,
    flex_apart Θ0 Δρ P0 ψa ->
    flex_apart Θ0 Δρ (pskl_tophole P0) ψa
(* ⚠️ NO [fa_topholeg_t] ROW (DESIGN §10.5).  Letting a ∀◈ target inherit the
   guard from its body is the ONLY way a guard can hold at a ∀◈ that is neither
   [fa_clean] nor [fa_flexfree], and with [fa_rho_var] present that produces a
   "∀◈-STACK over a Δρ-variable" — a shape the flexible-P0 read-off then has to
   report and no consumer can use (it is not a mono paint, and there is no
   [var ⊑ᵖ topholeg] precision rule).  Dropping the row costs NOTHING: every
   producer was a transport re-applying it while rebuilding a derivation, never
   a consumer building one, and [flex_apart_topholeg_target_inv] — the direction
   that IS used, stripping a ∀◈ off the target — still holds, since [fa_clean]
   and [fa_flexfree] both survive the strip. *)
| fa_arrow : forall P1 P2 ψ1 ψ2,
    flex_apart Θ0 Δρ P1 ψ1 ->
    flex_apart Θ0 Δρ P2 ψ2 ->
    flex_apart Θ0 Δρ (pskl_arrow P1 P2) (uskl_arrow ψ1 ψ2)
| fa_all_etag : forall L ε P0 ψ,
    (forall α, α `notin` L ->
       flex_apart Θ0 Δρ (open_pskl_wrt_pskl P0 (pskl_var_f α))
                        (open_uskl_wrt_uskl ψ (uskl_var_f α))) ->
    flex_apart Θ0 Δρ (pskl_all_syn P0) (uskl_all_etag ε ψ)
| fa_all_syn : forall L P0 ψ,
    (forall α, α `notin` L ->
       flex_apart Θ0 Δρ (open_pskl_wrt_pskl P0 (pskl_var_f α))
                        (open_uskl_wrt_uskl ψ (uskl_var_f α))) ->
    flex_apart Θ0 Δρ (pskl_all_syn P0) (uskl_all_syn ψ)
(* ===================================================================== *)
(*  THE TWO BASE ROWS [flex_shield] HAS AND THIS ONE LACKED.              *)
(*                                                                        *)
(*  DESIGN §10: the two repair premises legitimately differ in their       *)
(*  DESCENT discipline — P6-Cv descends consistency, which matches ∀s in   *)
(*  LOCKSTEP ([fa_all_etag] / [fa_all_syn], Δρ fixed), while P6-Sv         *)
(*  descends subtyping, which INSTANTIATES ([fsh_all_r], Δρ grows).  That  *)
(*  difference is real and must stay.  Their BASE rows, on the other hand, *)
(*  say the same thing about the same hazard and must agree — and these    *)
(*  two were missing here:                                                 *)
(*                                                                        *)
(*   · [fa_flexfree] — nothing to keep apart when the payload has no raw   *)
(*     Θ0-flexible at all.  [fa_unit] / [fa_var_rigid] / [fa_hole] were    *)
(*     three special cases of it; the general rule was never written.      *)
(*   · [fa_rho_var] — a ρ-REPLACED RIGID VARIABLE is safe opposite ANY     *)
(*     payload.  This is P6-Cv's own leaf: the precision premise forces    *)
(*     [Pi] to be that very variable, SolS-Var / SolE-Var keep it, and the *)
(*     conclusion's precision is the var rule, so no dirt reaches the      *)
(*     payload however dirty the position is.  [flex_shield] states it as  *)
(*     [fsh_rho_var] for exactly this reason.                              *)
(*                                                                        *)
(*  ⚠️ WITHOUT them the premise is TOO STRONG — [sub_shield] is            *)
(*  UNSATISFIABLE at an ARROW P0 against a tagged-identity guess, because  *)
(*  Sub-ForallL's walk step makes the guess mention the very binder it put *)
(*  into Δρ and nothing was left to apply.  Machine-checked in             *)
(*  cex/cex_p7_shield_arrow.v (two witnesses: the first needs              *)
(*  [fa_flexfree], the second needs [fa_rho_var]).                         *)
(*                                                                        *)
(*  NEITHER disturbs the lockstep inversions: [fa_flexfree]'s conclusion   *)
(*  re-applies at any sub-payload (flex-freedom is inherited), and         *)
(*  [fa_rho_var]'s target is a bare variable, which every ∀ / arrow        *)
(*  inversion discriminates away.  An [fa_all_r] row WOULD have broken     *)
(*  them, which is why it is deliberately absent.                          *)
(* ===================================================================== *)
| fa_flexfree : forall P0 ψa,
    pskl_flex_free Θ0 P0 ->
    flex_apart Θ0 Δρ P0 ψa
| fa_rho_var : forall P0 α,
    α `in` Δρ ->
    flex_apart Θ0 Δρ P0 (uskl_var_f α).


(* Inversions used by the ∀◇/∀◈ congruence cases. *)
Lemma flex_apart_topholeg_target_inv : forall Θ0 Δρ P ψ,
  flex_apart Θ0 Δρ P (uskl_topholeg ψ) ->
  flex_apart Θ0 Δρ P ψ.
Proof.
  intros Θ0 Δρ P ψ H.
  remember (uskl_topholeg ψ) as t eqn:Heqt.
  revert ψ Heqt; induction H; intros ψ' Heqt;
    try discriminate Heqt; subst.
  - apply fa_clean.
    match goal with Hc : _ ∩ _ [=] empty |- _ =>
      simpl in Hc; exact Hc end.
  - apply fa_unit.
  - apply fa_var_rigid; assumption.
  - apply fa_hole.
  - apply fa_tophole; auto.
  - (* fa_flexfree : flex-freedom does not look at the target *)
    apply fa_flexfree; assumption.
Qed.

Lemma flex_apart_tophole_p0_inv : forall Θ0 Δρ P ψ,
  flex_apart Θ0 Δρ (pskl_tophole P) ψ ->
  flex_apart Θ0 Δρ P ψ.
Proof.
  intros Θ0 Δρ P ψ H.
  remember (pskl_tophole P) as t eqn:Heqt.
  revert P Heqt; induction H; intros P' Heqt;
    try discriminate Heqt; subst.
  - apply fa_clean; assumption.
  - inversion Heqt; subst; assumption.
  - (* fa_flexfree : ∀◇'s body inherits flex-freedom *)
    subst. apply fa_flexfree; eapply pskl_flex_free_tophole_inv; eassumption.
  - (* fa_rho_var : the target is a bare Δρ-variable, unchanged *)
    apply fa_rho_var; assumption.
Qed.

(** THE FLEX-P0 READ-OFF.  A [flex_apart] whose P0 is a FLEXIBLE variable has
    only two ways to hold.  [fa_var_rigid] wants that very variable RIGID and
    [fa_flexfree] wants it non-flexible, so both are excluded by the caller's
    own [a_flex_tvar]; the arrow / ∀ rows want another P0 shape; and
    and the ∀◈ target has its own row of the consumer's induction, so it is
    excluded here by a SHAPE side condition — exactly as [flex_shield_flex_leaf]
    does it on the shield side.  That leaves [fa_clean] — the guess is Δρ-CLEAN,
    i.e. ρ acts as the identity on it ([uskl_rho_clean_eq]) — and [fa_rho_var],
    where the guess IS a Δρ-variable.

    ⚠️ The second disjunct is NEW (DESIGN §10): before [fa_rho_var] existed
    this read-off was an equation, and the premise was correspondingly TOO
    STRONG.  It costs the consumer nothing, because a Δρ-VARIABLE is already a
    mono paint — which is exactly what the cleanliness was being used to
    establish (P6-Cs's Arrow row feeds it to
    [ad_pat_consis_rho_subst_psia_mono] to get "ψa is mono, hence tag-free"). *)
Lemma flex_apart_flex_var_clean : forall Θ0 Δρ β ψa,
  flex_apart Θ0 Δρ (pskl_var_f β) ψa ->
  ~ binds β abind_tvar Θ0 ->
  a_flex_tvar Θ0 β ->
  (ftvar_in_uskl ψa) ∩ Δρ [=] empty
  \/ (exists α0, ψa = uskl_var_f α0 /\ α0 `in` Δρ).
Proof.
  intros Θ0 Δρ β ψa H.
  remember (pskl_var_f β) as t eqn:Heqt.
  revert β Heqt; induction H; intros β' Heqt Hnr Hflex;
    try discriminate Heqt; subst.
  - (* fa_clean *) left; assumption.
  - (* fa_var_rigid : the caller's own [a_flex_tvar] excludes it *)
    inversion Heqt; subst; contradiction.
  - (* fa_flexfree : IMPOSSIBLE — β is flexible, so P0 is not flex-free *)
    exfalso. apply (H β'); [ simpl; clear; fsetdec | exact Hflex ].
  - (* fa_rho_var : the guess IS a Δρ-variable — already a mono paint *)
    right; exists α; split; [ reflexivity | exact H ].
Qed.

(* ===================================================================== *)
(*  Arrow-case flex-subcase discharge (Phase B).                           *)
(*  (B1) On a Δρ-clean target the ρ-relation degenerates to equality;      *)
(*  (B2) a mono paint that refines the consistency counterpart is precise  *)
(*  against the (tag-sorted) consistency subject.                          *)
(* ===================================================================== *)

Lemma uskl_rho_clean_eq : forall NM Θ Δρ Ψρ R' R,
  uskl_rho NM Θ Δρ Ψρ R' R ->
  (ftvar_in_uskl R) ∩ Δρ [=] empty ->
  R' = R /\ Ψρ [=] empty.
Proof.
  intros NM Θ Δρ Ψρ R' R H; induction H; intros Hclean.
  - split; [ reflexivity | assumption ].
  - (* leaf: the target variable is IN Δρ — contradiction with cleanliness *)
    exfalso. simpl in Hclean.
    match goal with Hα : α `in` Δρ |- _ => clear - Hα Hclean; fsetdec end.
  - (* arrow *)
    simpl in Hclean.
    destruct IHuskl_rho1 as [-> HΨ1]; [ clear - Hclean; fsetdec | ].
    destruct IHuskl_rho2 as [-> HΨ2]; [ clear - Hclean; fsetdec | ].
    split; [ reflexivity | ].
    match goal with HΨ : Ψρ [=] union _ _ |- _ =>
      clear - HΨ HΨ1 HΨ2; fsetdec end.
  - (* all_syn *)
    simpl in Hclean.
    pick fresh α for
      (L `union` Δρ `union` ftvar_in_uskl R' `union` ftvar_in_uskl R).
    destruct (H0 α ltac:(fsetdec)) as [Heq HΨ].
    { pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R (uskl_var_f α)).
      simpl in *. clear - Hclean H1 Fr. fsetdec. }
    split; [ | exact HΨ ].
    f_equal.
    apply open_uskl_wrt_uskl_inj with (α1 := α);
      [ clear - Fr; fsetdec | clear - Fr; fsetdec | exact Heq ].
  - (* all_etag *)
    simpl in Hclean.
    pick fresh α for
      (L `union` Δρ `union` ftvar_in_uskl R' `union` ftvar_in_uskl R).
    destruct (H0 α ltac:(fsetdec)) as [Heq HΨ].
    { pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R (uskl_var_f α)).
      simpl in *. clear - Hclean H1 Fr. fsetdec. }
    split; [ | exact HΨ ].
    f_equal.
    apply open_uskl_wrt_uskl_inj with (α1 := α);
      [ clear - Fr; fsetdec | clear - Fr; fsetdec | exact Heq ].
  - (* tophole *)
    simpl in Hclean.
    destruct IHuskl_rho as [-> HΨ]; [ exact Hclean | ].
    split; [ reflexivity | exact HΨ ].
  - (* topholeg *)
    simpl in Hclean.
    destruct IHuskl_rho as [-> HΨ]; [ exact Hclean | ].
    split; [ reflexivity | exact HΨ ].
Qed.

(* Mono paints never refine into a ∀-painted RHS. *)
Lemma ad_refine_mono_paint_allinh_rhs_absurd : forall Θ Δr Q' Q,
  a_wf_aenv Θ ->
  Θ ⨟ Δr ⊢ᵣᵃ Q' ⊳ Q ->
  forall Q0, Q = bskl_all_inh Q0 ->
  forall τb, Q' = ptyp_to_bskl_syn τb -> mono_ptyp τb ->
  False.
Proof.
  intros Θ Δr Q' Q HwfΘ H; induction H; intros Q0' HeqQ τb HeqL Hmb;
    try discriminate HeqQ.
  - (* all *) destruct τb; simpl in HeqL; discriminate HeqL.
  - (* hole *) destruct τb; simpl in HeqL; discriminate HeqL.
  - (* tophole_remove *) destruct τb; simpl in HeqL; discriminate HeqL.
  - (* flex_l *)
    destruct τb; simpl in HeqL; try discriminate HeqL.
    inversion HeqL; subst.
    eapply IHad_refine_syn;
      [ exact HwfΘ | reflexivity | reflexivity
      | eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

Lemma ad_refine_mono_paint_allsyn_rhs_absurd : forall Θ Δr Q' Q,
  a_wf_aenv Θ ->
  Θ ⨟ Δr ⊢ᵣᵃ Q' ⊳ Q ->
  forall Q0, Q = bskl_all_syn Q0 ->
  forall τb, Q' = ptyp_to_bskl_syn τb -> mono_ptyp τb ->
  False.
Proof.
  intros Θ Δr Q' Q HwfΘ H; induction H; intros Q0' HeqQ τb HeqL Hmb;
    try discriminate HeqQ.
  - (* hole: RHS is a syn painting — could be all_syn; LHS □ not a paint *)
    destruct τb; simpl in HeqL; discriminate HeqL.
  - (* tophole_remove *) destruct τb; simpl in HeqL; discriminate HeqL.
  - (* tophole_fill *) destruct τb; simpl in HeqL; discriminate HeqL.
  - (* flex_l *)
    destruct τb; simpl in HeqL; try discriminate HeqL.
    inversion HeqL; subst.
    eapply IHad_refine_syn;
      [ exact HwfΘ | reflexivity | reflexivity
      | eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

(* Counterpart shapes reachable by refining FROM a mono paint: the
   mono-ish bskl grammar (unit / any var / arrow). *)
Inductive bskl_monoish : bskl -> Prop :=
| bmi_unit : bskl_monoish bskl_unit
| bmi_var : forall α, bskl_monoish (bskl_var_f α)
| bmi_arrow : forall Q1 Q2,
    bskl_monoish Q1 -> bskl_monoish Q2 ->
    bskl_monoish (bskl_arrow Q1 Q2).

Lemma bskl_monoish_paint : forall τ,
  mono_ptyp τ -> bskl_monoish (ptyp_to_bskl_syn τ).
Proof. intros τ Hm; induction Hm; simpl; constructor; auto. Qed.

Lemma ad_refine_mono_paint_rhs_monoish : forall Θ Δr Q' Q,
  a_wf_aenv Θ ->
  Θ ⨟ Δr ⊢ᵣᵃ Q' ⊳ Q ->
  forall τb, Q' = ptyp_to_bskl_syn τb -> mono_ptyp τb ->
  bskl_monoish Q.
Proof.
  intros Θ Δr Q' Q HwfΘ H; induction H; intros τb HeqL Hmb.
  - apply bmi_unit.
  - apply bmi_var.
  - (* arrow *)
    symmetry in HeqL.
    destruct (ptyp_to_bskl_syn_arrow_inv _ HeqL)
      as (τ1 & τ2 & -> & Heq1 & Heq2).
    apply bmi_arrow;
      [ eapply IHad_refine_syn1;
          [ exact HwfΘ | exact Heq1 | inversion Hmb; assumption ]
      | eapply IHad_refine_syn2;
          [ exact HwfΘ | exact Heq2 | inversion Hmb; assumption ] ].
  - (* all: LHS all_inh, never a paint *)
    destruct τb; simpl in HeqL; discriminate HeqL.
  - (* hole: LHS □, never a paint *)
    destruct τb; simpl in HeqL; discriminate HeqL.
  - (* tophole_remove *) destruct τb; simpl in HeqL; discriminate HeqL.
  - (* tophole_fill *) destruct τb; simpl in HeqL; discriminate HeqL.
  - (* tophole_keep *) destruct τb; simpl in HeqL; discriminate HeqL.
  - (* flex_l *)
    destruct τb; simpl in HeqL; try discriminate HeqL.
    inversion HeqL; subst.
    eapply IHad_refine_syn;
      [ exact HwfΘ | reflexivity | eapply a_wf_aenv_binds_def_mono; eauto ].
  - (* flex_r *) apply bmi_var.
Qed.

(* Against a mono-ish counterpart, a tag-sorted consistency subject is
   itself a mono paint and the derivation solves no tags. *)
Lemma ad_pat_consis_monoish_counterpart : forall Ψs Θ ψa Q,
  Ψs ⨟ Θ ⊢ₛᵃ ψa ∼ Q ->
  a_wf_aenv Θ ->
  is_tskl ψa ->
  bskl_monoish Q ->
  Ψs [=] empty /\
  exists τa, mono_ptyp τa /\ ψa = ptyp_to_uskl_syn τa.
Proof.
  intros Ψs Θ ψa Q H; induction H; intros HwfΘ Htsk Hmi.
  - (* unit *)
    split; [ assumption | exists ptyp_unit; split;
      [ apply mono_ptyp__unit | reflexivity ] ].
  - (* var *)
    split; [ assumption | exists (ptyp_var_f α); split;
      [ apply mono_ptyp__var | reflexivity ] ].
  - (* arrow *)
    inversion Hmi; subst.
    assert (Ht1 : is_tskl R1) by (inversion Htsk; assumption).
    assert (Ht2 : is_tskl R2) by (inversion Htsk; assumption).
    destruct (IHad_pat_consis1 HwfΘ Ht1 ltac:(assumption))
      as (HΨ1 & τ1 & Hm1 & ->).
    destruct (IHad_pat_consis2 HwfΘ Ht2 ltac:(assumption))
      as (HΨ2 & τ2 & Hm2 & ->).
    split.
    + match goal with HΨ : Ψ [=] union _ _ |- _ =>
        clear - HΨ HΨ1 HΨ2; fsetdec end.
    + exists (ptyp_arrow τ1 τ2); split;
        [ apply mono_ptyp__arrow; assumption | reflexivity ].
  - (* forall_inh_tagged: Q = all_inh, not mono-ish *) inversion Hmi.
  - (* forall_inh_untagged *) inversion Hmi.
  - (* forall_syn_tagged *) inversion Hmi.
  - (* forall_syn *) inversion Hmi.
  - (* ghostg: Q = hole *) inversion Hmi.
  - (* topholeg: Q = tophole *) inversion Hmi.
  - (* hole: subject not a tskl *) inversion Htsk.
  - (* tophole *) inversion Htsk.
  - (* tophole_inh *) inversion Htsk.
  - (* tophole_drop *) inversion Htsk.
  - (* flex_l: subject var α (defined) — itself a mono paint *)
    assert (Hmd : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact HwfΘ | eassumption ]).
    destruct (IHad_pat_consis HwfΘ
                ltac:(apply is_tskl_mono_paint; exact Hmd) Hmi)
      as (HΨ & _).
    split; [ exact HΨ | ].
    exists (ptyp_var_f α); split; [ apply mono_ptyp__var | reflexivity ].
  - (* flex_r: unfold the counterpart definition — still mono-ish *)
    assert (Hmd : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact HwfΘ | eassumption ]).
    apply IHad_pat_consis;
      [ exact HwfΘ | exact Htsk | apply bskl_monoish_paint; exact Hmd ].
Qed.
(* LHS flex_l-spine chases at concrete counterpart shapes, with the
   component/continuation obligations passed as functionals. *)
Lemma ppre_paint_arrow_chase : forall Θ Δr Q' Q,
  a_wf_aenv Θ ->
  Θ ⨟ Δr ⊢ᵣᵃ Q' ⊳ Q ->
  forall Q1 Q2 (ψ1 ψ2 : uskl),
  Q = bskl_arrow Q1 Q2 ->
  (forall Δr' τ1, Δr' [=] empty -> mono_ptyp τ1 ->
     Θ ⨟ Δr' ⊢ᵣᵃ (ptyp_to_bskl_syn τ1) ⊳ Q1 ->
     forall Δ, Θ ⨟ Δ ⊢ (ptyp_to_pskl τ1) ⊑ᵖ[ empty ] ψ1) ->
  (forall Δr' τ2, Δr' [=] empty -> mono_ptyp τ2 ->
     Θ ⨟ Δr' ⊢ᵣᵃ (ptyp_to_bskl_syn τ2) ⊳ Q2 ->
     forall Δ, Θ ⨟ Δ ⊢ (ptyp_to_pskl τ2) ⊑ᵖ[ empty ] ψ2) ->
  forall τb, Q' = ptyp_to_bskl_syn τb -> mono_ptyp τb ->
  Δr [=] empty ->
  forall Δ, Θ ⨟ Δ ⊢ (ptyp_to_pskl τb) ⊑ᵖ[ empty ] (uskl_arrow ψ1 ψ2).
Proof.
  intros Θ Δr Q' Q HwfΘ H;
    induction H; intros Q1' Q2' ψ1 ψ2 HeqQ CONT1 CONT2 τb HeqL Hmb HΔr Δo;
    try discriminate HeqQ.
  - (* arrow *)
    inversion HeqQ; subst.
    symmetry in HeqL.
    destruct (ptyp_to_bskl_syn_arrow_inv _ HeqL)
      as (τb1 & τb2 & -> & Heqb1 & Heqb2).
    assert (Hm1 : mono_ptyp τb1) by (inversion Hmb; assumption).
    assert (Hm2 : mono_ptyp τb2) by (inversion Hmb; assumption).
    simpl.
    apply ad_ppre__arrow with (Ψ1 := empty) (Ψ2 := empty);
      [ eapply CONT1;
          [ exact HΔr | exact Hm1 | rewrite <- Heqb1; eassumption ]
      | eapply CONT2;
          [ exact HΔr | exact Hm2 | rewrite <- Heqb2; eassumption ]
      | clear; fsetdec ].
  - (* hole: LHS never a paint *)
    destruct τb; simpl in HeqL; discriminate HeqL.
  - (* tophole_remove *)
    destruct τb; simpl in HeqL; discriminate HeqL.
  - (* flex_l *)
    destruct τb; simpl in HeqL; try discriminate HeqL.
    inversion HeqL; subst.
    simpl.
    eapply ad_ppre__flex_l; [ eassumption | ].
    eapply IHad_refine_syn;
      [ exact HwfΘ | reflexivity | exact CONT1 | exact CONT2
      | reflexivity | eapply a_wf_aenv_binds_def_mono; eauto | exact HΔr ].
Qed.

Lemma ppre_paint_flexvar_chase : forall Θ Δr Q' Q,
  a_wf_aenv Θ ->
  Θ ⨟ Δr ⊢ᵣᵃ Q' ⊳ Q ->
  forall α1 τα1 (ψa : uskl),
  Q = bskl_var_f α1 ->
  binds α1 (abind_flex_mono_def τα1) Θ ->
  (forall Δr' τc, Δr' [=] empty -> mono_ptyp τc ->
     Θ ⨟ Δr' ⊢ᵣᵃ (ptyp_to_bskl_syn τc) ⊳ (ptyp_to_bskl_syn τα1) ->
     forall Δ, Θ ⨟ Δ ⊢ (ptyp_to_pskl τc) ⊑ᵖ[ empty ] ψa) ->
  forall τb, Q' = ptyp_to_bskl_syn τb -> mono_ptyp τb ->
  Δr [=] empty ->
  forall Δ, Θ ⨟ Δ ⊢ (ptyp_to_pskl τb) ⊑ᵖ[ empty ] ψa.
Proof.
  intros Θ Δr Q' Q HwfΘ H;
    induction H; intros α1 τα1 ψa HeqQ Hbγ CONT τb HeqL Hmb HΔr Δo;
    try discriminate HeqQ.
  - (* var: the counterpart variable itself *)
    inversion HeqQ; subst.
    symmetry in HeqL; apply ptyp_to_bskl_syn_var_inv in HeqL; subst.
    assert (Hmγ : mono_ptyp τα1)
      by (eapply a_wf_aenv_binds_def_mono; [ exact HwfΘ | exact Hbγ ]).
    assert (Hwfγ : a_wf_ptyp Θ τα1)
      by (eapply a_wf_aenv_binds_def_wf; [ exact HwfΘ | exact Hbγ ]).
    simpl.
    eapply ad_ppre__flex_l; [ exact Hbγ | ].
    eapply CONT;
      [ exact HΔr | exact Hmγ
      | apply ad_refine_mono_paint_refl; [ exact Hwfγ | exact Hmγ ] ].
  - (* hole: LHS never a paint *)
    destruct τb; simpl in HeqL; discriminate HeqL.
  - (* tophole_remove *)
    destruct τb; simpl in HeqL; discriminate HeqL.
  - (* flex_l *)
    destruct τb; simpl in HeqL; try discriminate HeqL.
    inversion HeqL; subst.
    simpl.
    eapply ad_ppre__flex_l; [ eassumption | ].
    eapply IHad_refine_syn;
      [ exact HwfΘ | reflexivity | exact Hbγ | exact CONT
      | reflexivity | eapply a_wf_aenv_binds_def_mono; eauto | exact HΔr ].
  - (* flex_r: the same definition by uniqueness *)
    inversion HeqQ; subst.
    match goal with
    | Hb2 : binds _ (abind_flex_mono_def ?t) Θ,
      Hr0 : _ ⨟ _ ⊢ᵣᵃ _ ⊳ ptyp_to_bskl_syn ?t |- _ =>
        pose proof (binds_unique _ _ _ _ _ Hb2 Hbγ (a_wf_aenv_uniq HwfΘ))
          as Hcc;
        injection Hcc; intros ->;
        eapply CONT; [ exact HΔr | exact Hmb | exact Hr0 ]
    end.
Qed.

(* (B2) The bridge: a mono paint refining the counterpart of a MONO-PAINT
   consistency subject is partially precise against that subject. *)
Lemma mono_paint_paint_refine_consis_ppre : forall Ψs Θ R Q,
  Ψs ⨟ Θ ⊢ₛᵃ R ∼ Q ->
  a_wf_aenv Θ ->
  forall τa, R = ptyp_to_uskl_syn τa -> mono_ptyp τa ->
  forall Δr τb, Δr [=] empty -> mono_ptyp τb ->
  Θ ⨟ Δr ⊢ᵣᵃ (ptyp_to_bskl_syn τb) ⊳ Q ->
  forall Δ, Θ ⨟ Δ ⊢ (ptyp_to_pskl τb) ⊑ᵖ[ empty ] (ptyp_to_uskl_syn τa).
Proof.
  intros Ψs Θ R Q H; induction H;
    intros HwfΘ τa HeqS Hma Δr τb HΔr Hmb Hrefine Δo.
  - (* unit *)
    symmetry in HeqS; apply ptyp_to_uskl_syn_unit_inv in HeqS; subst.
    eapply ad_refine_mono_paint_lhs_ppre with (τ := ptyp_unit);
      [ exact HwfΘ | exact HΔr | exact Hrefine | reflexivity | reflexivity
      | exact Hmb | apply mono_ptyp__unit ].
  - (* var *)
    symmetry in HeqS; apply ptyp_to_uskl_syn_var_inv in HeqS; subst.
    eapply ad_refine_mono_paint_lhs_ppre with (τ := ptyp_var_f α);
      [ exact HwfΘ | exact HΔr | exact Hrefine | reflexivity | reflexivity
      | exact Hmb | apply mono_ptyp__var ].
  - (* arrow *)
    symmetry in HeqS.
    destruct (ptyp_to_uskl_syn_arrow_inv _ HeqS)
      as (τa1 & τa2 & -> & Heqa1 & Heqa2).
    assert (Hma1 : mono_ptyp τa1) by (inversion Hma; assumption).
    assert (Hma2 : mono_ptyp τa2) by (inversion Hma; assumption).
    subst.
    eapply ppre_paint_arrow_chase with
      (ψ1 := ptyp_to_uskl_syn τa1) (ψ2 := ptyp_to_uskl_syn τa2);
      [ exact HwfΘ | exact Hrefine | reflexivity
      | intros Δr' τ1 HΔr' Hm1 Hr1 Δ1;
        eapply IHad_pat_consis1;
          [ exact HwfΘ | reflexivity | exact Hma1 | exact HΔr'
          | exact Hm1 | exact Hr1 ]
      | intros Δr' τ2 HΔr' Hm2 Hr2 Δ2;
        eapply IHad_pat_consis2;
          [ exact HwfΘ | reflexivity | exact Hma2 | exact HΔr'
          | exact Hm2 | exact Hr2 ]
      | reflexivity | exact Hmb | exact HΔr ].
  - (* forall_inh_tagged: subject all_etag never a mono paint *)
    exfalso; eapply ptyp_to_uskl_syn_all_etag_absurd; symmetry; exact HeqS.
  - (* forall_inh_untagged: subject all_syn, mono excluded *)
    destruct τa; simpl in HeqS; try discriminate HeqS. inversion Hma.
  - (* forall_syn_tagged *)
    exfalso; eapply ptyp_to_uskl_syn_all_etag_absurd; symmetry; exact HeqS.
  - (* forall_syn *)
    destruct τa; simpl in HeqS; try discriminate HeqS. inversion Hma.
  - (* ghostg: subject holeg never a paint *)
    destruct τa; simpl in HeqS; discriminate HeqS.
  - (* topholeg *)
    destruct τa; simpl in HeqS; discriminate HeqS.
  - (* hole *)
    destruct τa; simpl in HeqS; discriminate HeqS.
  - (* tophole *)
    destruct τa; simpl in HeqS; discriminate HeqS.
  - (* tophole_inh *)
    destruct τa; simpl in HeqS; discriminate HeqS.
  - (* tophole_drop *)
    destruct τa; simpl in HeqS; discriminate HeqS.
  - (* flex_l: subject var α (defined) *)
    symmetry in HeqS; apply ptyp_to_uskl_syn_var_inv in HeqS; subst.
    assert (Hmd : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact HwfΘ | eassumption ]).
    simpl.
    eapply ad_ppre__flex_r; [ eassumption | ].
    eapply IHad_pat_consis;
      [ exact HwfΘ | reflexivity | exact Hmd | exact HΔr
      | exact Hmb | exact Hrefine ].
  - (* flex_r: chase the counterpart definition *)
    eapply ad_partial_precise_psi_cong;
      [ eapply ppre_paint_flexvar_chase;
          [ exact HwfΘ | exact Hrefine | reflexivity | eassumption
          | intros Δr' τc HΔr' Hmc Hrc Δc;
            eapply IHad_pat_consis;
              [ exact HwfΘ | exact HeqS | exact Hma | exact HΔr'
              | exact Hmc | exact Hrc ]
          | reflexivity | exact Hmb | exact HΔr ]
      | clear; fsetdec ].
Qed.

(* ===================================================================== *)
(*  Arrow-case grid support (Phase C): component inversions at both-arrow *)
(*  nodes, the mono-SUBJECT tag-emptiness lemma (the [Pi = var] rows of   *)
(*  the CORE grids), and the [flex_apart] arrow inversion.                 *)
(* ===================================================================== *)

(** Component inversions at both-arrow nodes (names controlled by the
    caller, unlike a raw [inversion]). *)
Lemma ad_ppre_arrow_arrow_inv : forall Θ Δ Ψ P1 P2 ψ1 ψ2,
  Θ ⨟ Δ ⊢ (pskl_arrow P1 P2) ⊑ᵖ[ Ψ ] (uskl_arrow ψ1 ψ2) ->
  exists Ψ1 Ψ2, (Θ ⨟ Δ ⊢ P1 ⊑ᵖ[ Ψ1 ] ψ1) /\ (Θ ⨟ Δ ⊢ P2 ⊑ᵖ[ Ψ2 ] ψ2)
    /\ Ψ [=] Ψ1 `union` Ψ2.
Proof.
  intros Θ Δ Ψ P1 P2 ψ1 ψ2 H; inversion H; subst.
  match goal with
  | Hp1 : Θ ⨟ Δ ⊢ P1 ⊑ᵖ[ ?A ] ψ1, Hp2 : Θ ⨟ Δ ⊢ P2 ⊑ᵖ[ ?B ] ψ2 |- _ =>
    exists A, B; split; [ exact Hp1 | split; [ exact Hp2 | assumption ] ]
  end.
Qed.

Lemma ad_refine_arrow_arrow_inv : forall Θ Δr Q1' Q2' Q1 Q2,
  Θ ⨟ Δr ⊢ᵣᵃ (bskl_arrow Q1' Q2') ⊳ (bskl_arrow Q1 Q2) ->
  (Θ ⨟ Δr ⊢ᵣᵃ Q1' ⊳ Q1) /\ (Θ ⨟ Δr ⊢ᵣᵃ Q2' ⊳ Q2).
Proof.
  intros Θ Δr Q1' Q2' Q1 Q2 H; inversion H; subst; split; assumption.
Qed.

(** A mono-paint SUBJECT forces an empty tag reading of the target: the
    precision rules reachable from a paint (unit/var/arrow congruences +
    the flex chains) only ever meet tag-free target shapes — a mono paint
    has no ∀, so [ad_ppre__forall] (the only tag producer) cannot fire.
    Discharges the [Pi = var] rows of the Arrow-case CORE grid
    (Ψ' [=] ∅ ⇒ Ψa [=] ∅) and, by the ε-membership contradiction, kills
    the [Pi = var] rows of the tagged-∀ cases. *)
Lemma ad_ppre_mono_subject_target_tags_empty : forall Θ Δ Ψ P ψ,
  a_wf_aenv Θ ->
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  forall τ, P = ptyp_to_pskl τ -> mono_ptyp τ ->
  forall Ψt, d_tags_skl Ψt ψ -> Ψt [=] empty.
Proof.
  intros Θ Δ Ψ P ψ HwfΘ H; induction H; intros τ0 HeqP Hm Ψt Hdt.
  - (* unit *) exact (d_tags_skl_unit_inv Hdt).
  - (* var *) exact (d_tags_skl_var_inv Hdt).
  - (* arrow *)
    destruct τ0; simpl in HeqP; try discriminate HeqP.
    inversion HeqP; subst.
    destruct (d_tags_skl_arrow_inv Hdt)
      as (Ψt1 & Ψt2 & Hd1 & Hd2 & _ & HeqΨt).
    assert (Hm1 : mono_ptyp τ0_1) by (inversion Hm; assumption).
    assert (Hm2 : mono_ptyp τ0_2) by (inversion Hm; assumption).
    pose proof (IHad_partial_precise1 HwfΘ _ eq_refl Hm1 _ Hd1) as He1.
    pose proof (IHad_partial_precise2 HwfΘ _ eq_refl Hm2 _ Hd2) as He2.
    clear - HeqΨt He1 He2; fsetdec.
  - (* forall: subject all_syn is never a mono paint *)
    destruct τ0; simpl in HeqP; try discriminate HeqP.
    inversion Hm.
  - (* hole: never a paint *)
    destruct τ0; simpl in HeqP; discriminate HeqP.
  - (* tophole_remove *)
    destruct τ0; simpl in HeqP; discriminate HeqP.
  - (* tophole_fill *)
    destruct τ0; simpl in HeqP; discriminate HeqP.
  - (* tophole_keep *)
    destruct τ0; simpl in HeqP; discriminate HeqP.
  - (* flex_l: chase the definition (still a mono paint) *)
    destruct τ0; simpl in HeqP; try discriminate HeqP.
    inversion HeqP; subst.
    eapply IHad_partial_precise;
      [ exact HwfΘ | reflexivity
      | eapply a_wf_aenv_binds_def_mono; eauto | exact Hdt ].
  - (* flex_r: target var carries no tags *)
    exact (d_tags_skl_var_inv Hdt).
Qed.

(** [flex_apart] inversion at a both-arrow node: the clean case distributes
    the free-variable condition; the arrow case is direct.  (Of the other
    constructors, none matches an arrow P0 against an arrow target.) *)
Lemma flex_apart_arrow_inv : forall Θ0 Δρ P1 P2 ψ1 ψ2,
  flex_apart Θ0 Δρ (pskl_arrow P1 P2) (uskl_arrow ψ1 ψ2) ->
  flex_apart Θ0 Δρ P1 ψ1 /\ flex_apart Θ0 Δρ P2 ψ2.
Proof.
  intros Θ0 Δρ P1 P2 ψ1 ψ2 H; inversion H; subst.
  - (* fa_clean *)
    match goal with
    | Hc : _ ∩ _ [=] empty |- _ => simpl in Hc;
        split; apply fa_clean; clear - Hc; fsetdec
    end.
  - (* fa_arrow *)
    split; assumption.
  - (* fa_flexfree : both components inherit flex-freedom *)
    match goal with Hff : pskl_flex_free _ _ |- _ =>
      destruct (pskl_flex_free_arrow_inv Hff) as [Hff1 Hff2] end.
    split; apply fa_flexfree; assumption.
Qed.

(* ===================================================================== *)
(*  REPAIR KIT (DESIGN §6(l)) — support lemmas for the tagged-∀ cases.    *)
(* ===================================================================== *)

(** Precision respects set-equality of Δ. *)
Lemma ad_partial_precise_delta_cong : forall Θ Δ Ψ P ψ,
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  forall Δ', Δ [=] Δ' ->
  Θ ⨟ Δ' ⊢ P ⊑ᵖ[ Ψ ] ψ.
Proof.
  intros Θ Δ Ψ P ψ H; induction H; intros Δ' Heq.
  - apply ad_ppre__unit; assumption.
  - apply ad_ppre__var; [ assumption | ].
    match goal with Hor : _ \/ a_binds_tvar _ _ |- _ =>
      destruct Hor as [HΔ | Hb];
      [ left; clear - HΔ Heq; fsetdec | right; assumption ] end.
  - eapply ad_ppre__arrow; eauto.
  - eapply ad_ppre__forall with (L := L);
      [ intros α Hα; apply (H0 α Hα); clear - Heq; fsetdec | assumption ].
  - apply ad_ppre__hole; [ assumption | ].
    match goal with Hint : _ ∩ _ [=] empty |- _ =>
      clear - Hint Heq; fsetdec end.
  - apply ad_ppre__tophole_remove; auto.
  - eapply ad_ppre__tophole_fill with (L := L); eauto.
  - apply ad_ppre__tophole_keep; auto.
  - eapply ad_ppre__flex_l; eauto.
  - eapply ad_ppre__flex_r; eauto.
Qed.

(** Δ-weakening by variables fresh for the target and for Θ's definition
    images.  (Unconditional Δ-weakening is FALSE — the □-rule's
    Δ-disjointness is antitone — but target-fresh extensions never meet a
    □-instance's side condition.) *)
Lemma ad_partial_precise_delta_weaken_fresh : forall Θ Δ Ψ P ψ,
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  forall Δ',
  Δ' ∩ ftvar_in_uskl ψ [=] empty ->
  delta_def_fresh Δ' Θ ->
  Θ ⨟ (Δ `union` Δ') ⊢ P ⊑ᵖ[ Ψ ] ψ.
Proof.
  intros Θ Δ Ψ P ψ H; induction H; intros Δ' HΔ' Hdf.
  - apply ad_ppre__unit; assumption.
  - apply ad_ppre__var; [ assumption | ].
    match goal with Hor : _ \/ a_binds_tvar _ _ |- _ =>
      destruct Hor as [HΔ | Hb];
      [ left; clear - HΔ; fsetdec | right; assumption ] end.
  - simpl in HΔ'.
    eapply ad_ppre__arrow;
      [ apply IHad_partial_precise1; [ clear - HΔ'; fsetdec | exact Hdf ]
      | apply IHad_partial_precise2; [ clear - HΔ'; fsetdec | exact Hdf ]
      | assumption ].
  - (* forall *)
    simpl in HΔ'.
    eapply ad_ppre__forall with (L := L `union` Δ'); [ | eassumption ].
    intros α0 Hα0.
    assert (HSX : Δ' ∩
              (ftvar_in_uskl (open_uskl_wrt_uskl ψ (uskl_var_f α0)))
              [=] empty).
    { pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ (uskl_var_f α0))
        as Hup.
      simpl in Hup. clear - HΔ' Hα0 Hup. fsetdec. }
    eapply ad_partial_precise_delta_cong;
      [ apply (H0 α0 ltac:(clear - Hα0; fsetdec) Δ' HSX Hdf)
      | clear; fsetdec ].
  - (* hole *)
    apply ad_ppre__hole; [ assumption | ].
    match goal with Hint : _ ∩ _ [=] empty |- _ =>
      clear - Hint HΔ'; fsetdec end.
  - apply ad_ppre__tophole_remove; auto.
  - (* tophole_fill *)
    eapply ad_ppre__tophole_fill with (L := L `union` Δ').
    intros α0 Hα0.
    assert (HSX : Δ' ∩
              (ftvar_in_uskl (open_uskl_wrt_uskl ψ (uskl_var_f α0)))
              [=] empty).
    { pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ (uskl_var_f α0))
        as Hup.
      simpl in Hup. clear - HΔ' Hα0 Hup. fsetdec. }
    assert (Hdf' : delta_def_fresh Δ' ((α0 ~ abind_tvar) ++ Θ)).
    { intros β α τ Hβ Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
        [ discriminate Hc | exact (Hdf β α τ Hβ Hb') ]. }
    apply (H0 α0 ltac:(clear - Hα0; fsetdec) Δ' HSX Hdf').
  - (* tophole_keep *)
    simpl in HΔ'.
    apply ad_ppre__tophole_keep; apply IHad_partial_precise; auto.
  - eapply ad_ppre__flex_l; [ eassumption | ].
    apply IHad_partial_precise; auto.
  - (* flex_r: the target hops to the definition's paint *)
    eapply ad_ppre__flex_r; [ eassumption | ].
    apply IHad_partial_precise; [ | exact Hdf ].
    rewrite ftvar_in_uskl_ptyp_to_uskl_syn.
    apply atoms_inter_empty_pointwise.
    intros y Hy. eapply Hdf; [ exact Hy | eassumption ].
Qed.

(** Moving a Δr-entry of the refinement into the aenv as a rigid tvar
    (mid-insertion general, for the fill rule's context growth). *)
Lemma ad_refine_syn_delta_to_tvar_mid : forall Θfull Δr Q' Q,
  Θfull ⨟ Δr ⊢ᵣᵃ Q' ⊳ Q ->
  forall α1 Θ1 Θ0 Δr', Θfull = Θ1 ++ Θ0 ->
  Δr [<=] add α1 Δr' ->
  (Θ1 ++ (α1 ~ abind_tvar) ++ Θ0) ⨟ Δr' ⊢ᵣᵃ Q' ⊳ Q.
Proof.
  intros Θfull Δr Q' Q H; induction H;
    intros α2 Θ1 Θt Δr' HeqΘ Hsub; subst.
  - apply ad_refine_syn__unit.
  - (* var *)
    apply ad_refine_syn__var.
    match goal with Hor : _ \/ a_binds_tvar ?α _ |- _ =>
      destruct Hor as [HΔ | Hbt];
      [ destruct (α == α2) as [-> | Hne];
        [ right; left; unfold binds;
          apply in_or_app; right; left; reflexivity
        | left; clear - HΔ Hsub Hne; fsetdec ]
      | right;
        destruct Hbt as [Hb | [Hb | [τ0 Hb]]];
        [ left; apply binds_weaken; exact Hb
        | right; left; apply binds_weaken; exact Hb
        | right; right; exists τ0; apply binds_weaken; exact Hb ] ]
    end.
  - apply ad_refine_syn__arrow; eauto.
  - (* all *)
    apply ad_refine_syn__all with (L := L).
    intros α Hα.
    apply (H0 α Hα α2 Θ1 Θt (add α Δr') eq_refl).
    clear - Hsub; fsetdec.
  - (* hole *)
    apply ad_refine_syn__hole.
    eapply a_wf_pskl_weaken;
      [ intros x b Hb; apply binds_weaken; exact Hb | eassumption ].
  - apply ad_refine_syn__tophole_remove; auto.
  - (* tophole_fill: the aenv grows on the left *)
    apply ad_refine_syn__tophole_fill with (L := L).
    intros α Hα.
    apply (H0 α Hα α2 ((α ~ abind_tvar) ++ Θ1) Θt Δr' eq_refl Hsub).
  - apply ad_refine_syn__tophole_keep; auto.
  - eapply ad_refine_syn__flex_l;
      [ apply binds_weaken; eassumption | auto ].
  - eapply ad_refine_syn__flex_r;
      [ apply binds_weaken; eassumption | auto ].
Qed.

Lemma ad_refine_syn_delta_to_tvar : forall Θ Δr Q' Q α1 Δr',
  Θ ⨟ Δr ⊢ᵣᵃ Q' ⊳ Q ->
  Δr [<=] add α1 Δr' ->
  ((α1 ~ abind_tvar) ++ Θ) ⨟ Δr' ⊢ᵣᵃ Q' ⊳ Q.
Proof.
  intros Θ Δr Q' Q α1 Δr' H Hsub.
  exact (@ad_refine_syn_delta_to_tvar_mid _ _ _ _ H α1 nil Θ Δr'
           eq_refl Hsub).
Qed.

(** Free variables of a consistency SUBJECT are counterpart variables or
    Θ's defined flexibles / their definition images.  (The tight bound —
    rigid tvar entries never pollute it — which is what survives the
    ∀-descent's context extensions.) *)
Lemma ad_pat_consis_ftv_bound : forall Ψ Θ R' Q,
  Ψ ⨟ Θ ⊢ₛᵃ R' ∼ Q ->
  forall α', α' `in` ftvar_in_uskl R' ->
  α' `in` ftvar_in_bskl Q \/
  (exists α τ, binds α (abind_flex_mono_def τ) Θ /\
     (α' = α \/ α' `in` ftvar_in_ptyp τ)).
Proof.
  intros Ψ Θ R' Q H; induction H; intros α0 HX0; simpl in HX0.
  - (* unit *) exfalso; clear - HX0; fsetdec.
  - (* var *) left; simpl; clear - HX0; fsetdec.
  - (* arrow *)
    apply union_iff in HX0; destruct HX0 as [HX0 | HX0];
      [ destruct (IHad_pat_consis1 α0 HX0) as [Hin | Hdef]
      | destruct (IHad_pat_consis2 α0 HX0) as [Hin | Hdef] ];
      solve [ left; simpl; clear - Hin; fsetdec | right; exact Hdef ].
  - (* forall_inh_tagged *)
    pick fresh β for
      (L `union` singleton α0 `union` ftvar_in_bskl Q).
    assert (HX0' : α0 `in`
              ftvar_in_uskl (open_uskl_wrt_uskl R (uskl_var_f β)))
      by (pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R
                        (uskl_var_f β)) as Hlow; clear - HX0 Hlow; fsetdec).
    destruct (H0 β ltac:(clear - Fr; fsetdec) α0 HX0')
      as [Hin | (α & τ & Hb & Hor)].
    + left.
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q
                    (bskl_var_f β)) as Hup.
      simpl in *. clear - Hin Hup Fr. fsetdec.
    + destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
        [ discriminate Hc | right; exists α, τ; auto ].
  - (* forall_inh_untagged *)
    pick fresh β for
      (L `union` singleton α0 `union` ftvar_in_bskl Q).
    assert (HX0' : α0 `in`
              ftvar_in_uskl (open_uskl_wrt_uskl R (uskl_var_f β)))
      by (pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R
                        (uskl_var_f β)) as Hlow; clear - HX0 Hlow; fsetdec).
    destruct (H0 β ltac:(clear - Fr; fsetdec) α0 HX0')
      as [Hin | (α & τ & Hb & Hor)].
    + left.
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q
                    (bskl_var_f β)) as Hup.
      simpl in *. clear - Hin Hup Fr. fsetdec.
    + destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
        [ discriminate Hc | right; exists α, τ; auto ].
  - (* forall_syn_tagged *)
    pick fresh β for
      (L `union` singleton α0 `union` ftvar_in_bskl Q).
    assert (HX0' : α0 `in`
              ftvar_in_uskl (open_uskl_wrt_uskl R (uskl_var_f β)))
      by (pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R
                        (uskl_var_f β)) as Hlow; clear - HX0 Hlow; fsetdec).
    destruct (H0 β ltac:(clear - Fr; fsetdec) α0 HX0')
      as [Hin | (α & τ & Hb & Hor)].
    + left.
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q
                    (bskl_var_f β)) as Hup.
      simpl in *. clear - Hin Hup Fr. fsetdec.
    + destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
        [ discriminate Hc | right; exists α, τ; auto ].
  - (* forall_syn *)
    pick fresh β for
      (L `union` singleton α0 `union` ftvar_in_bskl Q).
    assert (HX0' : α0 `in`
              ftvar_in_uskl (open_uskl_wrt_uskl R (uskl_var_f β)))
      by (pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R
                        (uskl_var_f β)) as Hlow; clear - HX0 Hlow; fsetdec).
    destruct (H0 β ltac:(clear - Fr; fsetdec) α0 HX0')
      as [Hin | (α & τ & Hb & Hor)].
    + left.
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q
                    (bskl_var_f β)) as Hup.
      simpl in *. clear - Hin Hup Fr. fsetdec.
    + destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
        [ discriminate Hc | right; exists α, τ; auto ].
  - (* ghostg *) exfalso; clear - HX0; fsetdec.
  - (* topholeg *)
    destruct (IHad_pat_consis α0 HX0) as [Hin | Hdef];
      [ left; simpl; clear - Hin; fsetdec | right; exact Hdef ].
  - (* hole *) exfalso; clear - HX0; fsetdec.
  - (* tophole *)
    destruct (IHad_pat_consis α0 HX0) as [Hin | Hdef];
      [ left; simpl; clear - Hin; fsetdec | right; exact Hdef ].
  - (* tophole_inh: subject fixed under the counterpart binder *)
    pick fresh β for
      (L `union` singleton α0 `union` ftvar_in_bskl Q).
    destruct (H0 β ltac:(clear - Fr; fsetdec) α0 ltac:(simpl; exact HX0))
      as [Hin | (α & τ & Hb & Hor)].
    + left.
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q
                    (bskl_var_f β)) as Hup.
      simpl in *. clear - Hin Hup Fr. fsetdec.
    + destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
        [ discriminate Hc | right; exists α, τ; auto ].
  - (* tophole_drop *)
    destruct (IHad_pat_consis α0 HX0) as [Hin | Hdef];
      [ left; exact Hin | right; exact Hdef ].
  - (* flex_l: the subject variable is itself a defined flexible *)
    right; exists α, τ; split; [ assumption | left; clear - HX0; fsetdec ].
  - (* flex_r: unfolding the counterpart definition *)
    destruct (IHad_pat_consis α0 HX0) as [Hin | Hdef];
      [ | right; exact Hdef ].
    unfold ptyp_to_bskl_syn in Hin.
    rewrite ftvar_pskl_to_bskl_syn in Hin.
    right; exists α, τ; split;
      [ assumption
      | right;
        pose proof (ftvar_in_pskl_ptyp_to_pskl τ) as Hp;
        clear - Hin Hp; fsetdec ].
Qed.

(** ρ's target free variables are subject variables or replaced ones. *)
Lemma uskl_rho_ftv_target_bound : forall NM Θ Δρ Ψρ R' R,
  uskl_rho NM Θ Δρ Ψρ R' R ->
  ftvar_in_uskl R [<=] ftvar_in_uskl R' `union` Δρ.
Proof.
  intros NM Θ Δρ Ψρ R' R H; induction H; simpl; try fsetdec.
  - (* all_syn *)
    pick fresh α for
      (L `union` ftvar_in_uskl R' `union` ftvar_in_uskl R).
    pose proof (H0 α ltac:(clear - Fr; fsetdec)) as Hα.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f α)).
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R' (uskl_var_f α)).
    simpl in *. clear - Hα H1 H2 Fr. fsetdec.
  - (* all_etag *)
    pick fresh α for
      (L `union` ftvar_in_uskl R' `union` ftvar_in_uskl R).
    pose proof (H0 α ltac:(clear - Fr; fsetdec)) as Hα.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f α)).
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R' (uskl_var_f α)).
    simpl in *. clear - Hα H1 H2 Fr. fsetdec.
Qed.

(** Cofinite inversions of the tag-sorting components at a tagged ∀. *)
Lemma is_tskl_all_etag_inv : forall ε ψ,
  is_tskl (uskl_all_etag ε ψ) ->
  exists L, forall α, α `notin` L ->
    is_tskl (open_uskl_wrt_uskl ψ (uskl_var_f α)).
Proof. intros ε ψ H; inversion H; subst. eexists; eassumption. Qed.

Lemma uskl_ghost_free_all_etag_inv : forall ε ψ,
  uskl_ghost_free (uskl_all_etag ε ψ) ->
  exists L, forall α, α `notin` L ->
    uskl_ghost_free (open_uskl_wrt_uskl ψ (uskl_var_f α)).
Proof. intros ε ψ H; inversion H; subst. eexists; eassumption. Qed.

(** [a_tags_sort] inversion at a tagged ∀ (all components cofinite). *)
Lemma a_tags_sort_all_etag_inv : forall NM Ψ ε ψ,
  a_tags_sort NM Ψ (uskl_all_etag ε ψ) ->
  exists L Ψ0,
    (forall α, α `notin` L ->
       a_tags_sort NM Ψ0 (open_uskl_wrt_uskl ψ (uskl_var_f α))) /\
    ε `notin` Ψ0 /\ Ψ [=] add ε Ψ0.
Proof.
  intros NM Ψ ε ψ H.
  inversion H; subst.
  - (* SK *)
    match goal with Hts : is_tskl _ |- _ =>
      destruct (is_tskl_all_etag_inv Hts) as (L1 & Hti) end.
    match goal with Hd : d_tags_skl _ _ |- _ =>
      destruct (d_tags_skl_all_etag_inv Hd)
        as (L2 & Ψ0 & Hd0 & Hnin & Heq) end.
    exists (L1 `union` L2), Ψ0.
    split; [ | split; [ exact Hnin | exact Heq ] ].
    intros α Hα; apply a_tags_sort__sk;
      [ apply Hti; clear - Hα; fsetdec
      | apply Hd0; clear - Hα; fsetdec ].
  - (* TY *)
    match goal with Hts : is_tskl _ |- _ =>
      destruct (is_tskl_all_etag_inv Hts) as (L1 & Hti) end.
    match goal with Hd : d_tags_skl _ _ |- _ =>
      destruct (d_tags_skl_all_etag_inv Hd)
        as (L2 & Ψ0 & Hd0 & Hnin & Heq) end.
    match goal with Hg : uskl_ghost_free _ |- _ =>
      destruct (uskl_ghost_free_all_etag_inv Hg) as (L3 & Hgf) end.
    exists (L1 `union` L2 `union` L3), Ψ0.
    split; [ | split; [ exact Hnin | exact Heq ] ].
    intros α Hα; apply a_tags_sort__ty;
      [ apply Hti; clear - Hα; fsetdec
      | apply Hd0; clear - Hα; fsetdec
      | apply Hgf; clear - Hα; fsetdec ].
Qed.

(** [flex_apart] aenv weakening (binds-monotone).  ⚠️ Since [fa_flexfree]
    (DESIGN §10) reads the context NEGATIVELY, the map must also create no new
    flexibles — true of every RIGID extension, which is what all the callers do.
    A FLEXIBLE prefix needs the ftv-scoped twin below, exactly as on the
    [flex_shield] side. *)
Lemma flex_apart_weaken : forall Θ0 Δρ P ψ,
  flex_apart Θ0 Δρ P ψ ->
  forall Θ0', (forall x b, binds x b Θ0 -> binds x b Θ0') ->
  (forall α, a_flex_tvar Θ0' α -> a_flex_tvar Θ0 α) ->
  flex_apart Θ0' Δρ P ψ.
Proof.
  intros Θ0 Δρ P ψ H; induction H; intros Θ0' Hmon Hfx.
  - apply fa_clean; assumption.
  - apply fa_unit.
  - apply fa_var_rigid; auto.
  - apply fa_hole.
  - apply fa_tophole; auto.
  - apply fa_arrow; auto.
  - eapply fa_all_etag with (L := L); eauto.
  - eapply fa_all_syn with (L := L); eauto.
  - apply fa_flexfree; intros α Hα Hflex; apply (H α Hα); auto.
  - apply fa_rho_var; assumption.
Qed.

(** …and the FLEXIBLE-prefix twin ([flex_shield_weaken_flex_prefix]'s mirror):
    a payload variable outside [dom Ξ] keeps its Θ0 binding, so flex-freedom
    survives.  The opened binder in the ∀ rows must miss [dom Ξ] too. *)
Lemma flex_apart_weaken_flex_prefix : forall Θ0 Δρ P ψ,
  flex_apart Θ0 Δρ P ψ ->
  forall Ξ, (ftvar_in_pskl P) ∩ (dom Ξ) [=] empty ->
  flex_apart (Ξ ++ Θ0) Δρ P ψ.
Proof.
  intros Θ0 Δρ P ψ H; induction H; intros Ξ Hfr.
  - apply fa_clean; assumption.
  - apply fa_unit.
  - apply fa_var_rigid; apply binds_app_3; assumption.
  - apply fa_hole.
  - simpl in Hfr. apply fa_tophole; apply IHflex_apart; exact Hfr.
  - simpl in Hfr. apply fa_arrow;
      [ apply IHflex_apart1 | apply IHflex_apart2 ]; clear - Hfr; fsetdec.
  - apply fa_all_etag with (L := L `union` dom Ξ); intros α Hα.
    apply H0; [ clear - Hα; solve_notin | ].
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0 (pskl_var_f α)) as Hup.
    simpl in Hup, Hfr. clear - Hup Hfr Hα; fsetdec.
  - apply fa_all_syn with (L := L `union` dom Ξ); intros α Hα.
    apply H0; [ clear - Hα; solve_notin | ].
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0 (pskl_var_f α)) as Hup.
    simpl in Hup, Hfr. clear - Hup Hfr Hα; fsetdec.
  - (* flexfree: a payload variable outside [dom Ξ] keeps its Θ0 binding *)
    apply fa_flexfree. intros α Hα Hflex.
    assert (HαΞ : α `notin` dom Ξ) by (clear - Hfr Hα; fsetdec).
    apply (H α Hα).
    destruct Hflex as [Hb | [τ Hb]];
      [ left | right; exists τ ];
      (destruct (binds_app_1 _ _ _ _ _ Hb) as [Hb' | Hb'];
        [ exfalso; apply HαΞ; eapply binds_In; exact Hb' | exact Hb' ]).
  - apply fa_rho_var; assumption.
Qed.

(* ===================================================================== *)
(*  [flex_apart] ALONG THE WALK                                           *)
(* ===================================================================== *)

(** P6-Cv's premise [flex_apart] is the Δρ-half of the invariant, and this
    lemma only THREADS it — but it cannot descend it: [flex_apart] has
    TWO-SIDED ∀ rows, and a two-sided family ties both binders to one
    variable, so a one-sided descent (Sub-ForallR opens the payload;
    Sub-ForallL instantiates the guess) cannot be recovered from it.  That
    is a structure mismatch, not a naming one — renaming aligns a pair, it
    does not manufacture a family — so no rename kit repairs it, and adding
    one-sided rows to [flex_apart] would break the two-sided descent P6-Cv
    itself performs.

    The fix costs nothing and touches no closed file: index the premise by
    the WALK.  [fa_step] has one constructor per descent THIS induction
    performs; [flex_apart_walk] demands [flex_apart] at every state
    reachable by them.  Closure under a descent is then a one-step prepend
    ([flex_apart_walk_step]) and the delegation to P6-Cv reads the current
    state off at reflexivity ([flex_apart_walk_here]).  [flex_apart] itself
    is untouched, so P6-Cv and P6-Cs stay exactly as they are — and unlike
    strengthening P6-Cv to [flex_shield], this keeps P6-Cs's call site
    (Δρ = ∅, a TAGGED guess, [fa_clean]) satisfiable. *)
(** ⚠️ Like [p0_step] and [ss_step], the walk carries an AVOID SET [A] that the
    ∀-descent's binder must miss — [fastep_all_l] is the only step that moves
    the PAYLOAD by opening a binder, and without the condition the walk reaches
    payloads mentioning an arbitrary γ, which blocks the FLEXIBLE-prefix
    transport ([fa_flexfree] is anti-monotone in the context, so it needs
    [ftv P0' ∩ dom Ξ = ∅]).  [flex_apart_walk] instantiates [A := dom Θ0]. *)
Inductive fa_step (A : atoms) :
  atoms -> pskl -> uskl -> atoms -> pskl -> uskl -> Prop :=
| fastep_arrow_l : forall Δρ P1 P2 ψ1 ψ2,
    fa_step A Δρ (pskl_arrow P1 P2) (uskl_arrow ψ1 ψ2) Δρ P1 ψ1
| fastep_arrow_r : forall Δρ P1 P2 ψ1 ψ2,
    fa_step A Δρ (pskl_arrow P1 P2) (uskl_arrow ψ1 ψ2) Δρ P2 ψ2
(* ⚠️ NO GUESS-FIXED P0 ARROW DESCENT (DESIGN §14.3, settled 2026-08-03).
   Two rows [fastep_p0_arrow_l] / [fastep_p0_arrow_r] used to live here —
   [fa_step A Δρ (P1 → P2) ψa Δρ Pi ψa], descending P0 while the guess stood
   still — so that [flex_apart_walk_p0] could hand P6-Cs its own P0-only
   closure out of P6-Ss's walk.  They made this walk UNSATISFIABLE: composed
   with [fastep_all_r] (Sub-ForallL, which OPENS the guess and grows Δρ) they
   reach a raw Θ0-flexible facing the OPENED body, e.g. [(α̂, β→β)] at
   [β ∈ Δρ], where [fa_clean] is blocked by β, [fa_flexfree] / [fa_var_rigid]
   by the flexible and every congruence by shape.  Machine-checked at a
   REACHABLE P7b node in cex/cex_p7_shield_realizable.v.
   The two closures are now kept apart: this one is POSITIONAL (P0 moves only
   in lockstep with the guess, or under a row where the guess cannot move at
   all), and P6-Cs's Δρ-CONSTANT [flex_apart_p0] below is carried as its own
   [sub_shield] conjunct instead of being derived from this one. *)
| fastep_all_l : forall Δρ P0 ψa γ,            (* Sub-ForallR *)
    γ `notin` A ->
    fa_step A Δρ (pskl_all_syn P0) ψa
            Δρ (open_pskl_wrt_pskl P0 (pskl_var_f γ)) ψa
| fastep_all_r : forall Δρ ε P0 ψ β,           (* Sub-ForallL *)
    fa_step A Δρ P0 (uskl_all_etag ε ψ)
            (add β Δρ) P0 (open_uskl_wrt_uskl ψ (uskl_var_f β))
| fastep_tophole_l : forall Δρ P0 ψa,
    fa_step A Δρ (pskl_tophole P0) ψa Δρ P0 ψa
| fastep_topholeg_r : forall Δρ P0 ψ,          (* Sub-UnivGhostLG *)
    fa_step A Δρ P0 (uskl_topholeg ψ) Δρ P0 ψ
| fastep_flexdef_r : forall Δρ P0 α τ,         (* FlexMono *)
    (* the definition that justifies this step lives in the TARGET context Θ,
       not in Θ0, and Θ grows across ForallR — so the step stays CONTEXT-FREE
       and carries the one consequence of Θ that matters instead: the
       unfolded painting is Δρ-clean.  [delta_def_fresh] is what supplies it,
       and P6-Sv's FlexMono row (the ONLY builder of this step) already has it
       on hand as [Hclean] for its own [fsh_clean].
       ⚠️ WITHOUT this premise the walk admits an ARBITRARY τ, and then
       [flex_apart_walk] is not derivable from cleanliness of ψa at all —
       which is exactly what blocks P7's [sub_shield] supply
       (docs/DESIGN-completeness-subtyping.md §9.0). *)
    (ftvar_in_uskl (ptyp_to_uskl_syn τ)) ∩ Δρ [=] empty ->
    fa_step A Δρ P0 (uskl_var_f α) Δρ P0 (ptyp_to_uskl_syn τ).

Inductive fa_walk (A : atoms) :
  atoms -> pskl -> uskl -> atoms -> pskl -> uskl -> Prop :=
| fw_refl : forall Δρ P0 ψa, fa_walk A Δρ P0 ψa Δρ P0 ψa
| fw_step : forall Δρ P0 ψa Δρ1 P1 ψ1 Δρ2 P2 ψ2,
    fa_step A Δρ P0 ψa Δρ1 P1 ψ1 ->
    fa_walk A Δρ1 P1 ψ1 Δρ2 P2 ψ2 ->
    fa_walk A Δρ P0 ψa Δρ2 P2 ψ2.

Lemma fa_walk_mono : forall A A' Δρ P0 ψa Δρ' P0' ψa',
  fa_walk A Δρ P0 ψa Δρ' P0' ψa' -> A' [<=] A ->
  fa_walk A' Δρ P0 ψa Δρ' P0' ψa'.
Proof.
  intros A A' Δρ P0 ψa Δρ' P0' ψa' H; induction H; intros Hsub;
    [ apply fw_refl | ].
  eapply fw_step; [ | apply IHfa_walk; exact Hsub ].
  destruct H;
    solve [ constructor
          | apply fastep_all_l; clear - H Hsub; fsetdec
          | constructor; assumption ].
Qed.

(** The PAYLOAD's free variables still miss [A]: the ψ-side steps leave it
    alone and the P0-side ones take subterms or open at a binder outside [A]. *)
Lemma fa_walk_ftv : forall A Δρ P0 ψa Δρ' P0' ψa',
  fa_walk A Δρ P0 ψa Δρ' P0' ψa' ->
  (ftvar_in_pskl P0) ∩ A [=] empty ->
  (ftvar_in_pskl P0') ∩ A [=] empty.
Proof.
  intros A Δρ P0 ψa Δρ' P0' ψa' H; induction H; intros Hfr; [ exact Hfr | ].
  apply IHfa_walk. destruct H; simpl in Hfr;
    try solve [ clear - Hfr; fsetdec ].
  pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0 (pskl_var_f γ)) as Hup.
  simpl in Hup. clear - Hup Hfr H; fsetdec.
Qed.

Definition flex_apart_walk (Θ0 : aenv) (Δρ : atoms) (P0 : pskl) (ψa : uskl)
  : Prop :=
  forall Δρ' P0' ψa', fa_walk (dom Θ0) Δρ P0 ψa Δρ' P0' ψa' ->
    flex_apart Θ0 Δρ' P0' ψa'.

(** What the delegation to P6-Cv reads off. *)
Lemma flex_apart_walk_here : forall Θ0 Δρ P0 ψa,
  flex_apart_walk Θ0 Δρ P0 ψa -> flex_apart Θ0 Δρ P0 ψa.
Proof. intros Θ0 Δρ P0 ψa H; apply H; apply fw_refl. Qed.

(** …and what every descent needs: closure, by prepending the step. *)
Lemma flex_apart_walk_step : forall Θ0 Δρ P0 ψa Δρ1 P1 ψ1,
  flex_apart_walk Θ0 Δρ P0 ψa ->
  fa_step (dom Θ0) Δρ P0 ψa Δρ1 P1 ψ1 ->
  flex_apart_walk Θ0 Δρ1 P1 ψ1.
Proof.
  intros Θ0 Δρ P0 ψa Δρ1 P1 ψ1 H Hstep Δρ' P0' ψa' Hw.
  apply H. eapply fw_step; [ exact Hstep | exact Hw ].
Qed.

(** …and the context weakening the ∀ cases need, which is just
    [flex_apart_weaken] pointwise (the walk itself is context-free). *)
Lemma flex_apart_walk_weaken : forall Θ0 Δρ P0 ψa,
  flex_apart_walk Θ0 Δρ P0 ψa ->
  forall Θ0', (forall x b, binds x b Θ0 -> binds x b Θ0') ->
  (forall α, a_flex_tvar Θ0' α -> a_flex_tvar Θ0 α) ->
  (dom Θ0) [<=] (dom Θ0') ->
  flex_apart_walk Θ0' Δρ P0 ψa.
Proof.
  intros Θ0 Δρ P0 ψa H Θ0' Hmon Hfx Hdom Δρ' P0' ψa' Hw.
  eapply flex_apart_weaken;
    [ apply H; eapply fa_walk_mono; [ exact Hw | exact Hdom ]
    | exact Hmon | exact Hfx ].
Qed.

(** The FLEXIBLE-prefix transport — the [flex_apart_p0] / [sub_shield] mirror,
    and what the avoid set on [fastep_all_l] was added for. *)
Lemma flex_apart_walk_weaken_flex_prefix : forall Θ0 Δρ P0 ψa Ξ,
  flex_apart_walk Θ0 Δρ P0 ψa ->
  (ftvar_in_pskl P0) ∩ (dom Ξ) [=] empty ->
  flex_apart_walk (Ξ ++ Θ0) Δρ P0 ψa.
Proof.
  intros Θ0 Δρ P0 ψa Ξ H Hfr Δρ' P0' ψa' Hw.
  assert (HwΞ : fa_walk (dom Ξ) Δρ P0 ψa Δρ' P0' ψa')
    by (eapply fa_walk_mono; [ exact Hw | rewrite dom_app; clear; fsetdec ]).
  assert (Hw0 : fa_walk (dom Θ0) Δρ P0 ψa Δρ' P0' ψa')
    by (eapply fa_walk_mono; [ exact Hw | rewrite dom_app; clear; fsetdec ]).
  eapply flex_apart_weaken_flex_prefix;
    [ apply H; exact Hw0 | eapply fa_walk_ftv; [ exact HwΞ | exact Hfr ] ].
Qed.

(** Adding a RIGID creates no flexible, so this one stays free. *)
Lemma flex_apart_walk_weaken_tvar : forall Θ0 Δρ P0 ψa β,
  flex_apart_walk Θ0 Δρ P0 ψa ->
  flex_apart_walk ((β ~ abind_tvar) ++ Θ0) Δρ P0 ψa.
Proof.
  intros Θ0 Δρ P0 ψa β H.
  eapply flex_apart_walk_weaken;
    [ exact H | intros x b Hb; apply binds_app_3; exact Hb
    | apply a_flex_tvar_strip_tvar | simpl; clear; fsetdec ].
Qed.

(* ===================================================================== *)
(*  The P0-ONLY walk (P6-Cs).                                             *)
(*                                                                        *)
(*  P6-Cs descends P0 alone — ψa is the single guess for the looked-up α  *)
(*  and NEVER moves — so it needs [flex_apart] only at the P0-subterms it  *)
(*  actually reaches, at a CONSTANT Δρ.  That is strictly weaker than      *)
(*  [flex_apart_walk], whose [fastep_all_r] can grow Δρ, and the           *)
(*  difference is what makes the paper-faithful ρ = identity corollary of  *)
(*  P6-Cs PREMISE-FREE: at Δρ = ∅ every reachable state is [fa_clean].     *)
(*  ⚠️ P6-Ss carries this closure as its OWN [sub_shield] conjunct — it is  *)
(*  NOT derivable from [flex_apart_walk], and the two rows that once made   *)
(*  it so are what sank that premise (DESIGN §14.3; see the ⚠️ note on      *)
(*  [fa_step]).                                                            *)
(* ===================================================================== *)

(** ⚠️ The walk carries an AVOID SET [A], and the ∀-descent's binder must miss
    it — exactly as [ss_step] does (prop_look_complete_sub_cstr.v:90) and for
    exactly the same reason.  Without it the walk reaches states mentioning an
    ARBITRARY γ, and [flex_apart_p0] could then not be transported across a
    FLEXIBLE PREFIX at all: [fa_flexfree] is anti-monotone in the context, so
    its transport needs [ftv P0' ∩ dom Ξ = ∅], which only holds if the opened
    binders miss [dom Ξ].  [flex_apart_p0] instantiates [A := dom Θ0], and
    every call site picks its binder fresh for the context anyway — so the
    condition costs nothing and buys [flex_apart_p0_weaken_flex_prefix]. *)
Inductive p0_step (A : atoms) : pskl -> pskl -> Prop :=
| p0step_arrow_l : forall P1 P2, p0_step A (pskl_arrow P1 P2) P1
| p0step_arrow_r : forall P1 P2, p0_step A (pskl_arrow P1 P2) P2
| p0step_all     : forall P0 γ,
    γ `notin` A ->
    p0_step A (pskl_all_syn P0) (open_pskl_wrt_pskl P0 (pskl_var_f γ))
| p0step_tophole : forall P0, p0_step A (pskl_tophole P0) P0.

Inductive p0_walk (A : atoms) : pskl -> pskl -> Prop :=
| p0w_refl : forall P0, p0_walk A P0 P0
| p0w_step : forall P0 P1 P2,
    p0_step A P0 P1 -> p0_walk A P1 P2 -> p0_walk A P0 P2.

(** Shrinking the avoid set only admits MORE walks. *)
Lemma p0_walk_mono : forall A A' P0 P1,
  p0_walk A P0 P1 -> A' [<=] A -> p0_walk A' P0 P1.
Proof.
  intros A A' P0 P1 H; induction H; intros Hsub; [ apply p0w_refl | ].
  eapply p0w_step; [ | apply IHp0_walk; exact Hsub ].
  destruct H;
    [ apply p0step_arrow_l | apply p0step_arrow_r
    | apply p0step_all; clear - H Hsub; fsetdec
    | apply p0step_tophole ].
Qed.

(** …and the endpoint's free variables still miss [A]. *)
Lemma p0_walk_ftv : forall A P0 P1,
  p0_walk A P0 P1 -> (ftvar_in_pskl P0) ∩ A [=] empty ->
  (ftvar_in_pskl P1) ∩ A [=] empty.
Proof.
  intros A P0 P1 H; induction H; intros Hfr; [ exact Hfr | ].
  apply IHp0_walk. destruct H; simpl in Hfr;
    try solve [ clear - Hfr; fsetdec ].
  pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0 (pskl_var_f γ)) as Hup.
  simpl in Hup. clear - Hup Hfr H; fsetdec.
Qed.

Definition flex_apart_p0 (Θ0 : aenv) (Δρ : atoms) (P0 : pskl) (ψa : uskl)
  : Prop :=
  forall P0', p0_walk (dom Θ0) P0 P0' -> flex_apart Θ0 Δρ P0' ψa.

Lemma flex_apart_p0_here : forall Θ0 Δρ P0 ψa,
  flex_apart_p0 Θ0 Δρ P0 ψa -> flex_apart Θ0 Δρ P0 ψa.
Proof. intros Θ0 Δρ P0 ψa H; apply H; apply p0w_refl. Qed.

Lemma flex_apart_p0_step : forall Θ0 Δρ P0 ψa P1,
  flex_apart_p0 Θ0 Δρ P0 ψa -> p0_step (dom Θ0) P0 P1 ->
  flex_apart_p0 Θ0 Δρ P1 ψa.
Proof.
  intros Θ0 Δρ P0 ψa P1 H Hs P0' Hw.
  apply H; eapply p0w_step; [ exact Hs | exact Hw ].
Qed.

Lemma flex_apart_p0_weaken : forall Θ0 Δρ P0 ψa,
  flex_apart_p0 Θ0 Δρ P0 ψa ->
  forall Θ0', (forall x b, binds x b Θ0 -> binds x b Θ0') ->
  (forall α, a_flex_tvar Θ0' α -> a_flex_tvar Θ0 α) ->
  (dom Θ0) [<=] (dom Θ0') ->
  flex_apart_p0 Θ0' Δρ P0 ψa.
Proof.
  intros Θ0 Δρ P0 ψa H Θ0' Hmon Hfx Hdom P0' Hw.
  eapply flex_apart_weaken;
    [ apply H; eapply p0_walk_mono; [ exact Hw | exact Hdom ]
    | exact Hmon | exact Hfx ].
Qed.

Lemma flex_apart_p0_weaken_tvar : forall Θ0 Δρ P0 ψa β,
  flex_apart_p0 Θ0 Δρ P0 ψa ->
  flex_apart_p0 ((β ~ abind_tvar) ++ Θ0) Δρ P0 ψa.
Proof.
  intros Θ0 Δρ P0 ψa β H.
  eapply flex_apart_p0_weaken;
    [ exact H | intros x b Hb; apply binds_app_3; exact Hb
    | apply a_flex_tvar_strip_tvar | simpl; clear; fsetdec ].
Qed.

(** The FLEXIBLE-prefix transport (the [sub_shield_weaken_flex_prefix] mirror):
    the walk misses [dom Ξ] throughout, so its endpoint does, and [fa_flexfree]
    survives.  This is what the avoid set on [p0_step] was added for. *)
Lemma flex_apart_p0_weaken_flex_prefix : forall Θ0 Δρ P0 ψa Ξ,
  flex_apart_p0 Θ0 Δρ P0 ψa ->
  (ftvar_in_pskl P0) ∩ (dom Ξ) [=] empty ->
  flex_apart_p0 (Ξ ++ Θ0) Δρ P0 ψa.
Proof.
  intros Θ0 Δρ P0 ψa Ξ H HfrP0 P0' Hw.
  assert (HwΞ : p0_walk (dom Ξ) P0 P0')
    by (eapply p0_walk_mono; [ exact Hw | rewrite dom_app; clear; fsetdec ]).
  assert (Hw0 : p0_walk (dom Θ0) P0 P0')
    by (eapply p0_walk_mono; [ exact Hw | rewrite dom_app; clear; fsetdec ]).
  assert (HfrP0' : (ftvar_in_pskl P0') ∩ (dom Ξ) [=] empty)
    by (eapply p0_walk_ftv; [ exact HwΞ | exact HfrP0 ]).
  eapply flex_apart_weaken_flex_prefix; [ apply H; exact Hw0 | exact HfrP0' ].
Qed.

(** A Δρ-CLEAN guess shields every P0-subterm at once — in particular at
    Δρ = ∅, which is what the ρ = identity corollary of P6-Cs uses. *)
Lemma flex_apart_p0_clean : forall Θ0 Δρ P0 ψa,
  (ftvar_in_uskl ψa) ∩ Δρ [=] empty ->
  flex_apart_p0 Θ0 Δρ P0 ψa.
Proof. intros Θ0 Δρ P0 ψa Hc P0' _; apply fa_clean; exact Hc. Qed.

(** ⚠️ There is NO [flex_apart_walk_p0] (DESIGN §14.3, 2026-08-03).  P6-Ss's
    walk used to imply this closure, via the two guess-fixed P0 arrow steps
    [fa_step] carried for exactly that purpose — and those steps made
    [flex_apart_walk] unsatisfiable at a reachable P7b node (see the ⚠️ note
    on [fa_step]).  [flex_apart_p0] is now an INDEPENDENT [sub_shield]
    conjunct: P6-Ss reads it off directly instead of deriving it.  The two
    closures are compatible at a [sub_shield] position precisely because the
    Δρ' quantifier there keeps the guess CLEAN for the grown part of Δρ',
    which the guess-OPENING step [fastep_all_r] does not. *)

(** [flex_apart] binder descent at a tagged-∀ target with a ∀-source. *)
Lemma flex_apart_all_etag_forall_inv : forall Θ0 Δρ ε P0 ψ,
  flex_apart Θ0 Δρ (pskl_all_syn P0) (uskl_all_etag ε ψ) ->
  exists L, forall α, α `notin` L ->
    flex_apart Θ0 Δρ (open_pskl_wrt_pskl P0 (pskl_var_f α))
                     (open_uskl_wrt_uskl ψ (uskl_var_f α)).
Proof.
  intros Θ0 Δρ ε P0 ψ H; inversion H; subst.
  - (* fa_clean: bodies stay clean at fresh openings *)
    match goal with Hc : _ ∩ _ [=] empty |- _ =>
      exists Δρ; intros α Hα; apply fa_clean;
      pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ
                    (uskl_var_f α)) as Hup;
      simpl in *; clear - Hc Hup Hα; fsetdec
    end.
  - (* fa_all_etag: the cofinite family, directly *)
    match goal with
    | Hf : forall α, α `notin` ?L0 -> flex_apart _ _ _ _ |- _ =>
      exists L0; exact Hf
    end.
  - (* fa_flexfree : the ∀-body inherits flex-freedom at any fresh opener *)
    match goal with Hff : pskl_flex_free _ _ |- _ =>
      exists (ftvar_in_pskl P0 `union` dom Θ0); intros α Hα;
      apply fa_flexfree; intros α0 Hα0 Hflex;
      apply (Hff α0); [ | exact Hflex ];
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0
                    (pskl_var_f α)) as Hup;
      simpl in Hup |- *;
      assert (Hne : α0 <> α)
        by (intro; subst; destruct Hflex as [Hb | [τ Hb]];
            apply binds_In in Hb; clear - Hα Hb; fsetdec);
      clear - Hup Hα0 Hne; fsetdec
    end.
Qed.


(** Absorb Δr-entries that are rigid tvars of the aenv (the Δr-refinement
    → statement-form transfer, given Δr ⊆ dom Θtv and Θ ⊇ Θtv). *)
Lemma ad_refine_syn_delta_absorb : forall Θ Δr Q' Q,
  Θ ⨟ Δr ⊢ᵣᵃ Q' ⊳ Q ->
  forall Δr', (forall α2, α2 `in` Δr -> α2 `in` Δr' \/ binds α2 abind_tvar Θ) ->
  Θ ⨟ Δr' ⊢ᵣᵃ Q' ⊳ Q.
Proof.
  intros Θ Δr Q' Q H; induction H; intros Δr' Habs.
  - apply ad_refine_syn__unit.
  - apply ad_refine_syn__var.
    match goal with Hor : _ \/ a_binds_tvar ?α _ |- _ =>
      destruct Hor as [HΔ | Hbt];
      [ destruct (Habs _ HΔ) as [HΔ' | Hb];
        [ left; exact HΔ' | right; left; exact Hb ]
      | right; exact Hbt ] end.
  - apply ad_refine_syn__arrow; auto.
  - apply ad_refine_syn__all with (L := L).
    intros α Hα. apply (H0 α Hα (add α Δr')).
    intros α2 Hα2.
    destruct (AtomSetProperties.In_dec α2 (add α Δr')) as [Hin | Hnin];
      [ left; exact Hin | ].
    destruct (Habs α2 ltac:(clear - Hα2 Hnin; fsetdec)) as [HΔ' | Hb];
      [ left; clear - HΔ' Hnin; fsetdec | right; exact Hb ].
  - apply ad_refine_syn__hole; assumption.
  - apply ad_refine_syn__tophole_remove; auto.
  - apply ad_refine_syn__tophole_fill with (L := L).
    intros α Hα. apply (H0 α Hα Δr').
    intros α2 Hα2.
    destruct (Habs α2 Hα2) as [HΔ' | Hb];
      [ left; exact HΔ' | right; apply binds_cons_3; exact Hb ].
  - apply ad_refine_syn__tophole_keep; auto.
  - eapply ad_refine_syn__flex_l; eauto.
  - eapply ad_refine_syn__flex_r; eauto.
Qed.

(** Hole-free skeletons: for them partial precision is fully Δ-MONOTONE
    (the □-rule — the only Δ-antitone rule — never fires). *)
Fixpoint pskl_no_hole (P : pskl) : Prop :=
  match P with
  | pskl_unit => True
  | pskl_var_b _ => True
  | pskl_var_f _ => True
  | pskl_arrow P1 P2 => pskl_no_hole P1 /\ pskl_no_hole P2
  | pskl_all_syn P0 => pskl_no_hole P0
  | pskl_hole => False
  | pskl_tophole P0 => pskl_no_hole P0
  end.

Lemma pskl_no_hole_open_rec : forall P P' k,
  pskl_no_hole P -> pskl_no_hole P' ->
  pskl_no_hole (open_pskl_wrt_pskl_rec k P' P).
Proof.
  induction P; intros P' k HP HV; simpl in *; auto.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; auto.
  - destruct HP; split; auto.
Qed.

Lemma pskl_no_hole_open : forall P α,
  pskl_no_hole P ->
  pskl_no_hole (open_pskl_wrt_pskl P (pskl_var_f α)).
Proof.
  intros P α HP. apply pskl_no_hole_open_rec; simpl; auto.
Qed.

Lemma ptyp_to_pskl_no_hole : forall τ,
  pskl_no_hole (ptyp_to_pskl τ).
Proof. induction τ; simpl; auto. Qed.

Lemma ad_ppre_no_hole_subject_delta_mono : forall Θ Δ Ψ P ψ,
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  pskl_no_hole P ->
  forall Δ', Δ [<=] Δ' ->
  Θ ⨟ Δ' ⊢ P ⊑ᵖ[ Ψ ] ψ.
Proof.
  intros Θ Δ Ψ P ψ H; induction H; intros Hnh Δ' Hsub.
  - apply ad_ppre__unit; assumption.
  - apply ad_ppre__var; [ assumption | ].
    match goal with Hor : _ \/ a_binds_tvar _ _ |- _ =>
      destruct Hor as [HΔ | Hb];
      [ left; clear - HΔ Hsub; fsetdec | right; assumption ] end.
  - simpl in Hnh; destruct Hnh.
    eapply ad_ppre__arrow; eauto.
  - simpl in Hnh.
    eapply ad_ppre__forall with (L := L); [ | eassumption ].
    intros α Hα.
    apply (H0 α Hα); [ apply pskl_no_hole_open; exact Hnh | ].
    clear - Hsub; fsetdec.
  - simpl in Hnh; contradiction.
  - simpl in Hnh.
    apply ad_ppre__tophole_remove; auto.
  - simpl in Hnh.
    eapply ad_ppre__tophole_fill with (L := L); eauto.
  - simpl in Hnh.
    apply ad_ppre__tophole_keep; auto.
  - eapply ad_ppre__flex_l; [ eassumption | ].
    apply IHad_partial_precise;
      [ apply ptyp_to_pskl_no_hole | exact Hsub ].
  - eapply ad_ppre__flex_r; [ eassumption | ]. auto.
Qed.

(** Refinement's target free variables are source variables or Θ-scoped
    (fills are wf at empty Δ; definitions are Θ-scoped). *)
Lemma ad_refine_syn_ftv_rhs_bound : forall Θ Δr Qh Q,
  a_wf_aenv Θ ->
  Θ ⨟ Δr ⊢ᵣᵃ Qh ⊳ Q ->
  ftvar_in_bskl Q [<=] ftvar_in_bskl Qh `union` dom Θ.
Proof.
  intros Θ Δr Qh Q HwfΘ H; induction H; simpl; try (clear; fsetdec).
  - (* arrow *)
    clear - IHad_refine_syn1 IHad_refine_syn2 HwfΘ.
    specialize (IHad_refine_syn1 HwfΘ).
    specialize (IHad_refine_syn2 HwfΘ).
    fsetdec.
  - (* all *)
    pick fresh α for
      (L `union` ftvar_in_bskl Q `union` ftvar_in_bskl P
         `union` dom Θ).
    pose proof (H0 α ltac:(clear - Fr; fsetdec) HwfΘ) as Hα.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_lower P (bskl_var_f α))
      as Hlow.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f α))
      as Hup.
    simpl in *. clear - Hα Hlow Hup Fr. fsetdec.
  - (* hole: the fill is wf at empty Δ *)
    pose proof (a_wf_pskl_ftv_dom H) as Hd.
    rewrite ftvar_pskl_to_bskl_syn.
    clear - Hd; fsetdec.
  - (* tophole_remove *)
    specialize (IHad_refine_syn HwfΘ). clear - IHad_refine_syn; fsetdec.
  - (* tophole_fill *)
    pick fresh α for
      (L `union` ftvar_in_bskl P `union` ftvar_in_bskl Q
         `union` dom Θ).
    assert (HwfΘ' : a_wf_aenv ((α ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - Fr; fsetdec | exact HwfΘ ]).
    pose proof (H0 α ltac:(clear - Fr; fsetdec) HwfΘ') as Hα.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_lower P (bskl_var_f α))
      as Hlow.
    simpl in *. clear - Hα Hlow Fr. fsetdec.
  - (* tophole_keep *)
    specialize (IHad_refine_syn HwfΘ). clear - IHad_refine_syn; fsetdec.
  - (* flex_l: the definition image is Θ-scoped *)
    specialize (IHad_refine_syn HwfΘ).
    assert (Hd : ftvar_in_ptyp τ [<=] dom Θ)
      by (eapply a_wf_aenv_def_ftv_dom; eauto).
    unfold ptyp_to_bskl_syn in IHad_refine_syn.
    rewrite ftvar_pskl_to_bskl_syn in IHad_refine_syn.
    pose proof (ftvar_in_pskl_ptyp_to_pskl τ) as Hp.
    clear - IHad_refine_syn Hd Hp; fsetdec.
  - (* flex_r *)
    match goal with Hb : binds _ _ _ |- _ =>
      pose proof (binds_In _ _ _ _ Hb) as Hdom end.
    clear - Hdom; fsetdec.
Qed.

(* ===================================================================== *)
(*  PHASE-2 KIT (repair, §6(m)) — no_hole solve/refine facts, the         *)
(*  primary→plain refinement transfer, and the Δ-monotone leaf closer.    *)
(* ===================================================================== *)

(** Defined-flex bindings live in the Θr part of the split. *)
Lemma binds_def_split : forall Θtv Θr α τ,
  (forall x b, binds x b Θtv -> b = abind_tvar) ->
  binds α (abind_flex_mono_def τ) (Θtv ++ Θr) ->
  binds α (abind_flex_mono_def τ) Θr.
Proof.
  intros Θtv Θr α τ Htvs Hb.
  unfold binds in *.
  apply in_app_or in Hb; destruct Hb as [Hb | Hb]; [ | exact Hb ].
  exfalso. pose proof (Htvs _ _ Hb) as Hc. discriminate Hc.
Qed.

(** The primary (Θr, Δr)-refinement in statement form (Θ, ∅). *)
Lemma refine_primary_to_plain : forall Θtv Θr Δr Q' Q,
  (forall x b, binds x b Θtv -> b = abind_tvar) ->
  Δr [=] dom Θtv ->
  Θr ⨟ Δr ⊢ᵣᵃ Q' ⊳ Q ->
  (Θtv ++ Θr) ⨟ empty ⊢ᵣᵃ Q' ⊳ Q.
Proof.
  intros Θtv Θr Δr Q' Q Htvs HΔr H.
  eapply ad_refine_syn_delta_absorb with (Δr := Δr).
  - eapply ad_refine_syn_weaken; [ exact H | ].
    intros x b Hb. unfold binds in *. apply in_or_app; right; exact Hb.
  - intros α2 Hα2. right.
    assert (HZd : α2 `in` dom Θtv) by (clear - Hα2 HΔr; fsetdec).
    apply binds_In_inv in HZd; destruct HZd as [b Hb].
    pose proof (Htvs _ _ Hb) as Heqb; subst b.
    unfold binds in *. apply in_or_app; left; exact Hb.
Qed.

(** no_hole is reflected by opening. *)
Lemma pskl_no_hole_open_rec_inv : forall P P' k,
  pskl_no_hole (open_pskl_wrt_pskl_rec k P' P) -> pskl_no_hole P.
Proof.
  induction P; intros P' k H; simpl in *; auto.
  - destruct H as [H1 H2]; split; eauto.
  - eauto.
  - eauto.
Qed.

Lemma pskl_no_hole_open_inv : forall P V,
  pskl_no_hole (open_pskl_wrt_pskl P V) -> pskl_no_hole P.
Proof.
  intros P V H. eapply pskl_no_hole_open_rec_inv; exact H.
Qed.

(** no_hole survives ABSTRACTION — needed now that the solve ∀-rules close
    their outputs explicitly (DESIGN §4.3): [close] only ever swaps a free
    variable for a bound index, and neither is a hole. *)
Lemma pskl_no_hole_close_rec : forall P β k,
  pskl_no_hole P -> pskl_no_hole (close_pskl_wrt_pskl_rec k β P).
Proof.
  induction P; intros β k H; simpl in *; auto.
  - (* var_b *) destruct (lt_ge_dec n k); simpl; auto.
  - (* var_f *) destruct (β == α); simpl; auto.
  - (* arrow *) destruct H; split; auto.
Qed.

Lemma pskl_no_hole_close : forall P β,
  pskl_no_hole P -> pskl_no_hole (close_pskl_wrt_pskl β P).
Proof.
  intros P β H; unfold close_pskl_wrt_pskl;
    apply pskl_no_hole_close_rec; exact H.
Qed.

(** msubst preserves and reflects no_hole (images are paints). *)
Lemma msubst_pskl_no_hole : forall κ P,
  pskl_no_hole P -> pskl_no_hole (msubst_pskl κ P).
Proof.
  intros κ; induction P; intros H; simpl in *; auto.
  - apply ptyp_to_pskl_no_hole.
  - destruct H; split; auto.
Qed.

Lemma msubst_pskl_no_hole_inv : forall κ P,
  pskl_no_hole (msubst_pskl κ P) -> pskl_no_hole P.
Proof.
  intros κ; induction P; intros H; simpl in *; auto.
  destruct H; split; auto.
Qed.

(** The solve output is hole-free whenever the counterpart is: holes in
    the output only ever come from a □-counterpart (VacuousR).

    ⭐ The repaired SE-FlexR strengthens rather than threatens this: its
    output is [guess^TY]'s, a PAINT, and a paint has no holes by
    construction — that is the whole point of running the pattern through
    [guess^TY] before it is assigned.  (The old row returned the flexible,
    which was hole-free for the duller reason that a variable is.) *)
Lemma a_solve_eq_no_hole_p0 : forall Θ Pi P0 Ξ Pa,
  Θ ⊢ₑ Pi ∼ P0 ⤳ Ξ ⨾ Pa ->
  pskl_no_hole P0 ->
  pskl_no_hole Pa.
Proof.
  intros Θ Pi P0 Ξ Pa H; induction H; intros Hnh; simpl in *; auto.
  - (* flex_r: guess^TY's output is a paint *) apply ptyp_to_pskl_no_hole.
  - (* hole_r: the counterpart is □ — excluded *) contradiction.
  - (* arrow *) destruct Hnh; split; auto.
  - (* forall *)
    apply pskl_no_hole_close.
    apply IHa_solve_eq. apply pskl_no_hole_open_rec; simpl; auto.
  - (* tophole_l_all (GhostForall) *)
    apply pskl_no_hole_close.
    apply IHa_solve_eq. apply pskl_no_hole_open_rec; simpl; auto.
  - (* all_l_tophole (ForallGhost) *)
    apply pskl_no_hole_close.
    apply IHa_solve_eq; exact Hnh.
Qed.

(** A refinement into a Δr-binder variable (α0 outside the refinement's
    aenv) forces a hole-free source: the □-fill would have to BE that
    variable, which is not Θr-wf; flex hops never reach it. *)
Lemma ad_refine_inh_deltar_var_rhs_no_hole : forall Θr Δr Q' Q,
  Θr ⨟ Δr ⊢ᵣᵃ Q' ⊳ Q ->
  forall α0 P', Q = bskl_var_f α0 -> Q' = pskl_to_bskl_inh P' ->
  α0 `notin` dom Θr ->
  pskl_no_hole P'.
Proof.
  intros Θr Δr Q' Q H; induction H; intros α0 P' HeqQ HeqL HX0;
    try discriminate HeqQ.
  - (* var *)
    destruct P'; simpl in HeqL; try discriminate HeqL.
    simpl; exact I.
  - (* hole: the fill would be the binder variable — not Θr-wf *)
    exfalso.
    destruct P; simpl in HeqQ; try discriminate HeqQ.
    inversion HeqQ; subst.
    match goal with Hwf : _ ⨟ _ ⊢ₚₛᵃ pskl_var_f _ |- _ =>
      inversion Hwf; subst end.
    match goal with Hor : _ \/ a_binds_tvar _ _ |- _ =>
      destruct Hor as [Hin | [Hb | [Hb | [τ0 Hb]]]];
      [ clear - Hin; fsetdec
      | apply HX0; eapply binds_In; exact Hb
      | apply HX0; eapply binds_In; exact Hb
      | apply HX0; eapply binds_In; exact Hb ] end.
  - (* tophole_remove *)
    destruct P'; simpl in HeqL; try discriminate HeqL.
    inversion HeqL; subst.
    simpl. eapply IHad_refine_syn; eauto.
  - (* flex_l: the source is a bare variable *)
    destruct P'; simpl in HeqL; try discriminate HeqL.
    simpl; exact I.
  - (* flex_r: the target variable would be Θr-defined *)
    inversion HeqQ; subst.
    exfalso. apply HX0.
    match goal with Hb : binds _ (abind_flex_mono_def _) _ |- _ =>
      eapply binds_In; exact Hb end.
Qed.

(** The consistency subject's variables under the split: counterpart
    variables or Θr-scoped flex-definition data (the Θtv binders never
    pollute the bound). *)
Lemma consis_subject_ftv_split_bound : forall Ψ Θ R Q Θtv Θr,
  Ψ ⨟ Θ ⊢ₛᵃ R ∼ Q ->
  Θ = Θtv ++ Θr ->
  (forall x b, binds x b Θtv -> b = abind_tvar) ->
  a_wf_aenv Θ ->
  ftvar_in_uskl R [<=] ftvar_in_bskl Q `union` dom Θr.
Proof.
  intros Ψ Θ R Q Θtv Θr H HeqΘ Htvs Hwf.
  assert (HwfΘr : a_wf_aenv Θr)
    by (apply a_wf_aenv_app_r with (Θp := Θtv);
        rewrite <- HeqΘ; exact Hwf).
  intros x Hx.
  destruct (ad_pat_consis_ftv_bound H Hx) as [Hin | (α & τ & Hb & Hor)].
  - clear - Hin; fsetdec.
  - subst Θ.
    assert (Hbr : binds α (abind_flex_mono_def τ) Θr)
      by (eapply binds_def_split; [ exact Htvs | exact Hb ]).
    destruct Hor as [-> | Hτ].
    + pose proof (binds_In _ _ _ _ Hbr) as Hd. clear - Hd; fsetdec.
    + assert (Hd : ftvar_in_ptyp τ [<=] dom Θr)
        by (eapply a_wf_aenv_def_ftv_dom; [ exact HwfΘr | exact Hbr ]).
      clear - Hτ Hd; fsetdec.
Qed.

(** Rigid-variable-source refinement into a non-variable target is absurd,
    sub-context version (the def-lookup transports along binds-inclusion
    into the full context, where uniqueness kills it). *)
Lemma ad_refine_syn_rigid_var_nonvar_absurd_sub : forall Θr Δr β Q,
  Θr ⨟ Δr ⊢ᵣᵃ (bskl_var_f β) ⊳ Q ->
  forall Θfull, (forall x b, binds x b Θr -> binds x b Θfull) ->
  uniq Θfull ->
  binds β abind_tvar Θfull ->
  (forall β0, Q <> bskl_var_f β0) ->
  False.
Proof.
  intros Θr Δr β Q H; inversion H; subst; intros Θfull Hmon Hu Hb Hnv.
  - eapply Hnv; reflexivity.
  - match goal with Hbd : binds _ (abind_flex_mono_def _) _ |- _ =>
      pose proof (Hmon _ _ Hbd) as Hbd';
      pose proof (binds_unique _ _ _ _ _ Hb Hbd' Hu) as Hc;
      discriminate Hc end.
  - eapply Hnv; reflexivity.
Qed.

(** Δ-monotone variant of the leaf closer (the target is a replaced rigid
    variable; the var rule is Δ-positive). *)
Lemma p6cv_close_leaf_mono :
  forall NM Θ0 Θ κ Δ Δρ Ψρ Ψ' Ψi Ψa ψsub ψa Pi P0,
  a_wf_aenv Θ ->
  a_tags_sort NM Ψ' ψa ->
  Ψi `union` Ψa [<=] Ψ' ->
  rho_fresh Δρ Θ κ ->
  Δρ [<=] Δ ->
  (forall α, α `in` Δρ -> α `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
  Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa ->
  rho_leaf NM Θ Δρ Ψρ ψsub ψa ->
  (* closes by SE-Var, so the block is [nil] and no κ-extension arises *)
  exists Pa, Θ0 ⊢ₑ Pi ∼ P0 ⤳ nil ⨾ Pa /\
    forall Δ', Δ [<=] Δ' ->
    Θ ⨟ Δ' ⊢ (msubst_pskl κ Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa.
Proof.
  intros NM Θ0 Θ κ Δ Δρ Ψρ Ψ' Ψi Ψa ψsub ψa Pi P0
    HwfΘ Htags Hsub Hfresh Hdelta Hshield Hpre Hleaf.
  destruct Hleaf as (α & Ψ'' & Heqψa & HαΔρ & Htagsub & Hwfsub & HΨρ).
  subst ψa.
  pose proof (Hfresh α HαΔρ) as (HXb & Hκav & Hdef).
  assert (HαΔ : α `in` Δ) by (clear - Hdelta HαΔρ; fsetdec).
  pose proof (Hshield α HαΔρ) as Hsh.
  destruct (ad_ppre_delta_var_inv Hpre eq_refl HwfΘ HαΔ HXb Hdef Hsh)
    as (Heqm & HΨie).
  assert (HeqPi : Pi = pskl_var_f α)
    by (eapply msubst_pskl_var_inv; eassumption).
  assert (HΨ'e : Ψ' [=] empty)
    by (exact (d_tags_skl_var_inv (a_tags_sort_d_tags Htags))).
  assert (HΨae : Ψa [=] empty) by (clear - Hsub HΨ'e; fsetdec).
  exists Pi. split.
  - rewrite HeqPi. apply a_solve_eq__var.
  - intros Δ' Hsub'.
    rewrite Heqm.
    apply ad_ppre__var;
      [ clear - HΨie HΨae; fsetdec
      | left; clear - HαΔ Hsub'; fsetdec ].
Qed.

(* [wf-side-condition] delta_def_fresh Δ Θ — the paper's implicit wf of the
   Δ-extended precision context: Δ's binders postdate Θ's definition images.
   Discovered NECESSARY at the Var case (P6-Cv): with a defined-flex target
   var α whose definition mentions β ∈ Δ, the Pi = □ subcase's conclusion
   precision needs the □-rule at the definition's paint, whose Δ-disjointness
   premise fails — a machine-checked counterexample against the Δ-free
   statement (see DESIGN §6(h)).  All call sites satisfy it: ForallInh
   binders are fresh w.r.t. dom Θ ⊇ def-ftvs (a_wf_aenv_def_ftv_dom), Δρ
   carries it in rho_fresh, and the initial Δ obeys the same discipline. *)

(* ===================================================================== *)
(*  PHASE-3 KIT — the precision RENAME (the ∀-cases' cofinite bodies come *)
(*  from renaming the single fresh-α run: the solve is not deterministic, *)
(*  so per-α reruns would return unrelated outputs) + the msubst/subst    *)
(*  commutation.                                                           *)
(* ===================================================================== *)

Lemma msubst_pskl_subst_var : forall κ P' α' β,
  α' `notin` dom κ -> β `notin` dom κ ->
  (forall p, In p κ -> α' `notin` ftvar_in_ptyp (snd p)) ->
  subst_pskl_in_pskl (pskl_var_f β) α' (msubst_pskl κ P')
  = msubst_pskl κ (subst_pskl_in_pskl (pskl_var_f β) α' P').
Proof.
  intros κ P' α' β Hα Hβ Hav; induction P'; simpl;
    try (f_equal; auto; fail).
  (* var_f *)
  destruct (α == α') as [-> | Hne].
    + rewrite (msubst_lookup_notin_dom _ Hα).
      simpl.
      rewrite (msubst_lookup_notin_dom _ Hβ).
      default_simp.
    + assert (Hfr : α' `notin`
                ftvar_in_pskl (ptyp_to_pskl (msubst_lookup κ α))).
      { rewrite ftvar_in_pskl_ptyp_to_pskl.
        intros Hc.
        assert (Heq : α = α')
          by (eapply msubst_lookup_ftv_avoid; [ exact Hav | exact Hc ]).
        auto. }
      rewrite (subst_pskl_in_pskl_fresh_eq _ _ _ Hfr).
      reflexivity.
Qed.

(** Renaming a Δ-variable in a partial-precision derivation.  [α] is a
    Δ-only variable (outside Θ and its definition images), [β] globally
    fresh; the □-rule survives because its Δ-disjointness already forces
    α out of the local target. *)
Lemma ad_partial_precise_rename : forall Θ Δ Ψ P ψ,
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  forall αr βr,
  αr `in` Δ ->
  αr `notin` dom Θ ->
  βr `notin` dom Θ -> βr `notin` Δ ->
  βr `notin` ftvar_in_pskl P -> βr `notin` ftvar_in_uskl ψ ->
  (forall α τ, binds α (abind_flex_mono_def τ) Θ ->
     αr `notin` ftvar_in_ptyp τ /\ βr `notin` ftvar_in_ptyp τ) ->
  Θ ⨟ (add βr (remove αr Δ)) ⊢
    (subst_pskl_in_pskl (pskl_var_f βr) αr P)
    ⊑ᵖ[ Ψ ] (subst_bskl_in_uskl (uskl_var_f βr) αr ψ).
Proof.
  intros Θ Δ Ψ P ψ H; induction H;
    intros αr βr HαΔ HαΘ HβΘ HβΔ HYP Hβψ Hdefs; simpl in *.
  - (* unit *) apply ad_ppre__unit; assumption.
  - (* var *)
    destruct (eq_var α αr) as [-> | Hne].
    + destruct_if as [_ | Hc]; [ | exfalso; auto ].
      apply ad_ppre__var; [ assumption | left; clear; fsetdec ].
    + destruct_if as [Hc | _]; [ exfalso; auto | ].
      apply ad_ppre__var; [ assumption | ].
      match goal with Hor : _ \/ a_binds_tvar _ _ |- _ =>
        destruct Hor as [HΔ | Hb];
        [ left; clear - HΔ Hne; fsetdec | right; assumption ] end.
  - (* arrow *)
    eapply ad_ppre__arrow;
      [ apply IHad_partial_precise1; auto
      | apply IHad_partial_precise2; auto
      | assumption ].
  - (* forall *)
    eapply ad_ppre__forall
      with (L := L `union` singleton αr `union` singleton βr
                   `union` Δ `union` dom Θ); [ | eassumption ].
    intros α2 Hα2.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hα2; fsetdec | apply lc_pskl_var_f ].
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | clear - Hα2; fsetdec | apply lc_uskl_var_f ].
    eapply ad_partial_precise_delta_cong;
      [ apply (H0 α2 ltac:(clear - Hα2; fsetdec) αr βr);
        [ clear - HαΔ; fsetdec
        | exact HαΘ | exact HβΘ
        | clear - HβΔ Hα2; fsetdec
        | pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P
                        (pskl_var_f α2)) as Hup;
          simpl in Hup; clear - HYP Hα2 Hup; fsetdec
        | pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ
                        (uskl_var_f α2)) as Hup;
          simpl in Hup; clear - Hβψ Hα2 Hup; fsetdec
        | exact Hdefs ]
      | clear - Hα2; fsetdec ].
  - (* hole: α is already out of the local target *)
    match goal with Hint : _ ∩ _ [=] empty |- _ =>
      assert (Hαψ : αr `notin` ftvar_in_uskl ψ)
        by (clear - Hint HαΔ; fsetdec);
      rewrite (subst_bskl_in_uskl_fresh_eq _ _ _ Hαψ);
      apply ad_ppre__hole; [ assumption | clear - Hint Hβψ; fsetdec ]
    end.
  - (* tophole_remove *)
    apply ad_ppre__tophole_remove.
    apply IHad_partial_precise; auto.
  - (* tophole_fill *)
    eapply ad_ppre__tophole_fill
      with (L := L `union` singleton αr `union` singleton βr
                   `union` Δ `union` dom Θ).
    intros α2 Hα2.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | clear - Hα2; fsetdec | apply lc_uskl_var_f ].
    replace (pskl_tophole (subst_pskl_in_pskl (pskl_var_f βr) αr P))
      with (subst_pskl_in_pskl (pskl_var_f βr) αr (pskl_tophole P))
      by reflexivity.
    apply (H0 α2 ltac:(clear - Hα2; fsetdec) αr βr).
    + exact HαΔ.
    + simpl. clear - HαΘ Hα2; fsetdec.
    + simpl. clear - HβΘ Hα2; fsetdec.
    + exact HβΔ.
    + simpl. simpl in HYP. exact HYP.
    + pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ
                    (uskl_var_f α2)) as Hup;
      simpl in Hup; clear - Hβψ Hα2 Hup; fsetdec.
    + intros α τ Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
        [ discriminate Hc | exact (Hdefs _ _ Hb') ].
  - (* tophole_keep *)
    apply ad_ppre__tophole_keep.
    apply IHad_partial_precise; auto.
  - (* flex_l *)
    assert (Hne : α <> αr).
    { intros ->. apply HαΘ. eapply binds_In; eassumption. }
    destruct_if as [Hc | _]; [ exfalso; auto | ].
    destruct (Hdefs _ _ H) as [Hατ Hβτ].
    eapply ad_ppre__flex_l; [ eassumption | ].
    assert (Hfr : αr `notin` ftvar_in_pskl (ptyp_to_pskl τ))
      by (rewrite ftvar_in_pskl_ptyp_to_pskl; exact Hατ).
    rewrite <- (subst_pskl_in_pskl_fresh_eq
                  (ptyp_to_pskl τ) (pskl_var_f βr) αr Hfr).
    apply IHad_partial_precise; auto.
    rewrite ftvar_in_pskl_ptyp_to_pskl. exact Hβτ.
  - (* flex_r *)
    assert (Hne : α <> αr).
    { intros ->. apply HαΘ. eapply binds_In; eassumption. }
    destruct_if as [Hc | _]; [ exfalso; auto | ].
    destruct (Hdefs _ _ H) as [Hατ Hβτ].
    eapply ad_ppre__flex_r; [ eassumption | ].
    assert (Hfr : αr `notin` ftvar_in_uskl (ptyp_to_uskl_syn τ))
      by (rewrite ftvar_in_uskl_ptyp_to_uskl_syn; exact Hατ).
    rewrite <- (subst_bskl_in_uskl_fresh_eq
                  (ptyp_to_uskl_syn τ) (uskl_var_f βr) αr Hfr).
    apply IHad_partial_precise; auto.
    rewrite ftvar_in_uskl_ptyp_to_uskl_syn. exact Hβτ.
Qed.
