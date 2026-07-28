(** P6 — COMPLETENESS OF CONSTRAINT COLLECTION AND SOLVING (the "look"
    cluster [a_looksub]/[a_lookeq]/[a_solve_sub]/[a_solve_eq]/
    [a_solve_cstr]/[a_extract], algo/def_extra.v:287-498).

    Paper lemmas (docs/DESIGN-completeness-subtyping.md §7):
      P6-Cv  [a_solve_eq_complete_var]   consistency-proofs.tex:1180
      P6-Cs  [a_lookeq_solve_complete]   consistency-proofs.tex:920
      P6-Sv  [a_solve_sub_complete_var]  subtyping-proofs.tex:1696
      P6-Ss  [a_looksub_solve_complete]  subtyping-proofs.tex:2202
      P6-L   [a_extract_complete]        subtyping-proofs.tex:2729

    THE ρ REPRESENTATION (design locked in DESIGN §7, 2026-07-24): the
    paper's ρ — a substitution from rigid type variables to decorated
    skeletons, with Ψ the solved tags it introduces — is mechanized as
    the RELATION [uskl_rho] "ψsub ⊒ρ[Δρ;Ψρ] ψa" (ψsub = ρ(ψa), Δρ = the
    replaced variables): same-constructor congruences + a REFL rule
    (identity-ρ call sites) + one replace-leaf [ψ'' ⊒ var X].  A relation
    rather than a function ([list (atom * uskl)] + msubst) NOT because of
    capture-avoidance — locally nameless + cofinite binders give that for
    free, as for θ — but because the main inductions run on the
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
    the replaced variables — [X ∈ Δ] (blocks the precision hole rule),
    [binds X abind_tvar Θ] (blocks flex_r), X avoided by θ's images, by
    Θ's definition images ([rho_fresh]), and by the subject's ⊤◇-shielded
    variables ([pskl_shielded_ftv]).  Δ-membership ALONE is insufficient
    (counterexamples v4/v5, DESIGN §7): precision's tophole_remove/flex_l
    admit ⊤◇-wrapped or definition-chained leaf positions whose
    SE-GhostForall output breaks the conclusion precision.  The freshness
    facts hold at the one leaf-creating call site (P6-Sv ForallL: the
    freshly opened binder postdates θ and Θ's definitions, and the
    [a_wf_pskl__tophole] empty-Δ-body discipline keeps it out of ⊤◇
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
| urho__leaf : forall Δρ Ψρ X Ψ'' ψ'',
    X `in` Δρ ->
    a_tags_sort NM Ψ'' ψ'' ->
    Θ ⨟ empty ⊢ₚₛᵃ ⌊ ψ'' ⌋ˢ ->
    Ψρ [=] Ψ'' ->
    uskl_rho NM Θ Δρ Ψρ ψ'' (uskl_var_f X)
| urho__arrow : forall Δρ Ψρ Ψ1 Ψ2 S1 S2 R1 R2,
    uskl_rho NM Θ Δρ Ψ1 S1 R1 ->
    uskl_rho NM Θ Δρ Ψ2 S2 R2 ->
    Ψρ [=] Ψ1 `union` Ψ2 ->
    uskl_rho NM Θ Δρ Ψρ (uskl_arrow S1 S2) (uskl_arrow R1 R2)
| urho__all_syn : forall L Δρ Ψρ S R,
    (forall X, X `notin` L ->
       uskl_rho NM Θ Δρ Ψρ
         (open_uskl_wrt_uskl S (uskl_var_f X))
         (open_uskl_wrt_uskl R (uskl_var_f X))) ->
    uskl_rho NM Θ Δρ Ψρ (uskl_all_syn S) (uskl_all_syn R)
| urho__all_etag : forall L Δρ Ψρ ε S R,
    (forall X, X `notin` L ->
       uskl_rho NM Θ Δρ Ψρ
         (open_uskl_wrt_uskl S (uskl_var_f X))
         (open_uskl_wrt_uskl R (uskl_var_f X))) ->
    uskl_rho NM Θ Δρ Ψρ (uskl_all_etag ε S) (uskl_all_etag ε R)
| urho__tophole : forall Δρ Ψρ S R,
    uskl_rho NM Θ Δρ Ψρ S R ->
    uskl_rho NM Θ Δρ Ψρ (uskl_tophole S) (uskl_tophole R)
| urho__topholeg : forall Δρ Ψρ S R,
    uskl_rho NM Θ Δρ Ψρ S R ->
    uskl_rho NM Θ Δρ Ψρ (uskl_topholeg S) (uskl_topholeg R).

(** Re-tag under set equality. *)
Lemma uskl_rho_psi_cong : forall NM Θ Δρ Ψρ S R,
  uskl_rho NM Θ Δρ Ψρ S R ->
  forall Ψρ', Ψρ [=] Ψρ' ->
  uskl_rho NM Θ Δρ Ψρ' S R.
Proof.
  intros NM Θ Δρ Ψρ S R H; induction H; intros Ψρ' Heq.
  - apply urho__refl; [ assumption | fsetdec ].
  - eapply urho__leaf; [ exact H | exact H0 | exact H1 | fsetdec ].
  - eapply urho__arrow; [ exact H | exact H0 | fsetdec ].
  - eapply urho__all_syn with (L := L); intros X HX; eauto.
  - eapply urho__all_etag with (L := L); intros X HX; eauto.
  - apply urho__tophole; eauto.
  - apply urho__topholeg; eauto.
Qed.

(** Widen the replaced-variable bound. *)
Lemma uskl_rho_delta_mono : forall NM Θ Δρ Ψρ S R,
  uskl_rho NM Θ Δρ Ψρ S R ->
  forall Δρ', Δρ [<=] Δρ' ->
  uskl_rho NM Θ Δρ' Ψρ S R.
Proof.
  intros NM Θ Δρ Ψρ S R H; induction H; intros Δρ' Hsub.
  - apply urho__refl; assumption.
  - eapply urho__leaf; [ | exact H0 | exact H1 | exact H2 ]. fsetdec.
  - eapply urho__arrow; [ apply IHuskl_rho1 | apply IHuskl_rho2 | ];
      assumption.
  - eapply urho__all_syn with (L := L); intros X HX; eauto.
  - eapply urho__all_etag with (L := L); intros X HX; eauto.
  - apply urho__tophole; eauto.
  - apply urho__topholeg; eauto.
Qed.

(** The subject's tags are bounded by the replacement tags plus ψa's. *)
Lemma uskl_rho_ftag_sub : forall NM Θ Δρ Ψρ S R,
  uskl_rho NM Θ Δρ Ψρ S R ->
  ftag_in_uskl S [<=] Ψρ `union` ftag_in_uskl R.
Proof.
  intros NM Θ Δρ Ψρ S R H; induction H; simpl; try fsetdec.
  - (* leaf: tags of the image are exactly Ψ'' *)
    pose proof (d_tags_skl_ftag (a_tags_sort_d_tags H0)) as Ht.
    fsetdec.
  - (* all_syn *)
    pick fresh X for L.
    pose proof (H0 X ltac:(fsetdec)) as HX.
    pose proof (ftag_in_uskl_open_var S X).
    pose proof (ftag_in_uskl_open_var R X).
    fsetdec.
  - (* all_etag *)
    pick fresh X for L.
    pose proof (H0 X ltac:(fsetdec)) as HX.
    pose proof (ftag_in_uskl_open_var S X).
    pose proof (ftag_in_uskl_open_var R X).
    fsetdec.
Qed.

(* ===================================================================== *)
(*  Inversion of [uskl_rho] BY SUBJECT SHAPE (P6-Cv/Sv consume these: the   *)
(*  induction is on the [ad_pat_consis]/[ad_pat_sub] derivation of the      *)
(*  ρ(ψa)-SUBJECT, so each case fixes the subject shape and reads off ψa's  *)
(*  shape — either a matching structural congruence / reflexive copy, or a  *)
(*  ρ-LEAF [ψa = var X] with the subject as X's image).                     *)
(* ===================================================================== *)

(** [ψa = var X] with the subject as X's ρ-image (the leaf disjunct). *)
Definition rho_leaf (NM : a_sub_mode) (Θ : aenv) (Δρ Ψρ : atoms)
    (S : uskl) (ψa : uskl) : Prop :=
  exists X Ψ'', ψa = uskl_var_f X /\ X `in` Δρ /\
    a_tags_sort NM Ψ'' S /\ Θ ⨟ empty ⊢ₚₛᵃ ⌊ S ⌋ˢ /\ Ψρ [=] Ψ''.

(* [andsplit] splits ONLY [/\] goals — plain [split] would enter the
   single-constructor [a_tags_sort] inside [rho_leaf]. *)
Local Ltac rho_andsplit := repeat match goal with |- _ /\ _ => split end.
Local Ltac rho_refl_tac := left; split; [ reflexivity | assumption ].

Lemma uskl_rho_arrow_l_inv : forall NM Θ Δρ Ψρ S1 S2 ψa,
  uskl_rho NM Θ Δρ Ψρ (uskl_arrow S1 S2) ψa ->
  (ψa = uskl_arrow S1 S2 /\ Ψρ [=] empty)
  \/ rho_leaf NM Θ Δρ Ψρ (uskl_arrow S1 S2) ψa
  \/ (exists R1 R2 Ψ1 Ψ2, ψa = uskl_arrow R1 R2 /\
        uskl_rho NM Θ Δρ Ψ1 S1 R1 /\ uskl_rho NM Θ Δρ Ψ2 S2 R2 /\
        Ψρ [=] Ψ1 `union` Ψ2).
Proof.
  intros NM Θ Δρ Ψρ S1 S2 ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; left; exists X, Ψ''; rho_andsplit; try reflexivity; assumption.
  - right; right; exists R1, R2, Ψ1, Ψ2; rho_andsplit;
      try reflexivity; assumption.
Qed.

Lemma uskl_rho_unit_l_inv : forall NM Θ Δρ Ψρ ψa,
  uskl_rho NM Θ Δρ Ψρ uskl_unit ψa ->
  (ψa = uskl_unit /\ Ψρ [=] empty) \/ rho_leaf NM Θ Δρ Ψρ uskl_unit ψa.
Proof.
  intros NM Θ Δρ Ψρ ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; exists X, Ψ''; rho_andsplit; try reflexivity; assumption.
Qed.

Lemma uskl_rho_var_l_inv : forall NM Θ Δρ Ψρ Y ψa,
  uskl_rho NM Θ Δρ Ψρ (uskl_var_f Y) ψa ->
  (ψa = uskl_var_f Y /\ Ψρ [=] empty) \/ rho_leaf NM Θ Δρ Ψρ (uskl_var_f Y) ψa.
Proof.
  intros NM Θ Δρ Ψρ Y ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; exists X, Ψ''; rho_andsplit; try reflexivity; assumption.
Qed.

Lemma uskl_rho_hole_l_inv : forall NM Θ Δρ Ψρ ψa,
  uskl_rho NM Θ Δρ Ψρ uskl_hole ψa ->
  (ψa = uskl_hole /\ Ψρ [=] empty) \/ rho_leaf NM Θ Δρ Ψρ uskl_hole ψa.
Proof.
  intros NM Θ Δρ Ψρ ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; exists X, Ψ''; rho_andsplit; try reflexivity; assumption.
Qed.

Lemma uskl_rho_holeg_l_inv : forall NM Θ Δρ Ψρ ψa,
  uskl_rho NM Θ Δρ Ψρ uskl_holeg ψa ->
  (ψa = uskl_holeg /\ Ψρ [=] empty) \/ rho_leaf NM Θ Δρ Ψρ uskl_holeg ψa.
Proof.
  intros NM Θ Δρ Ψρ ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; exists X, Ψ''; rho_andsplit; try reflexivity; assumption.
Qed.

Lemma uskl_rho_tophole_l_inv : forall NM Θ Δρ Ψρ S ψa,
  uskl_rho NM Θ Δρ Ψρ (uskl_tophole S) ψa ->
  (ψa = uskl_tophole S /\ Ψρ [=] empty)
  \/ rho_leaf NM Θ Δρ Ψρ (uskl_tophole S) ψa
  \/ (exists R, ψa = uskl_tophole R /\ uskl_rho NM Θ Δρ Ψρ S R).
Proof.
  intros NM Θ Δρ Ψρ S ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; left; exists X, Ψ''; rho_andsplit; try reflexivity; assumption.
  - right; right; exists R; split; [ reflexivity | assumption ].
Qed.

Lemma uskl_rho_topholeg_l_inv : forall NM Θ Δρ Ψρ S ψa,
  uskl_rho NM Θ Δρ Ψρ (uskl_topholeg S) ψa ->
  (ψa = uskl_topholeg S /\ Ψρ [=] empty)
  \/ rho_leaf NM Θ Δρ Ψρ (uskl_topholeg S) ψa
  \/ (exists R, ψa = uskl_topholeg R /\ uskl_rho NM Θ Δρ Ψρ S R).
Proof.
  intros NM Θ Δρ Ψρ S ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; left; exists X, Ψ''; rho_andsplit; try reflexivity; assumption.
  - right; right; exists R; split; [ reflexivity | assumption ].
Qed.

Lemma uskl_rho_all_syn_l_inv : forall NM Θ Δρ Ψρ S ψa,
  uskl_rho NM Θ Δρ Ψρ (uskl_all_syn S) ψa ->
  (ψa = uskl_all_syn S /\ Ψρ [=] empty)
  \/ rho_leaf NM Θ Δρ Ψρ (uskl_all_syn S) ψa
  \/ (exists L R, ψa = uskl_all_syn R /\
        forall X, X `notin` L ->
          uskl_rho NM Θ Δρ Ψρ (open_uskl_wrt_uskl S (uskl_var_f X))
                              (open_uskl_wrt_uskl R (uskl_var_f X))).
Proof.
  intros NM Θ Δρ Ψρ S ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; left; exists X, Ψ''; rho_andsplit; try reflexivity; assumption.
  - right; right; exists L, R; split; [ reflexivity | eassumption ].
Qed.

Lemma uskl_rho_all_etag_l_inv : forall NM Θ Δρ Ψρ ε S ψa,
  uskl_rho NM Θ Δρ Ψρ (uskl_all_etag ε S) ψa ->
  (ψa = uskl_all_etag ε S /\ Ψρ [=] empty)
  \/ rho_leaf NM Θ Δρ Ψρ (uskl_all_etag ε S) ψa
  \/ (exists L R, ψa = uskl_all_etag ε R /\
        forall X, X `notin` L ->
          uskl_rho NM Θ Δρ Ψρ (open_uskl_wrt_uskl S (uskl_var_f X))
                              (open_uskl_wrt_uskl R (uskl_var_f X))).
Proof.
  intros NM Θ Δρ Ψρ ε S ψa H; inversion H; subst.
  - rho_refl_tac.
  - right; left; exists X, Ψ''; rho_andsplit; try reflexivity; assumption.
  - right; right; exists L, R; split; [ reflexivity | eassumption ].
Qed.

(* ===================================================================== *)
(*  Shielded free variables + the ρ-freshness pack (DESIGN §7).            *)
(*                                                                         *)
(*  [pskl_shielded_ftv P] collects the free type variables occurring       *)
(*  UNDER some ⊤◇ of [P].  The replaced variables of ρ must avoid them     *)
(*  (together with θ's and Θ's definition images): this is what recovers   *)
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

(** The ρ-freshness pack for the Θ/θ-stable components: every replaced
    variable is a rigid tvar of Θ that postdates θ's flexible images and
    Θ's definition images.  (The Pi-dependent component —
    [X ∉ pskl_shielded_ftv (msubst_pskl θ Pi)] — and the Δ-membership
    [X ∈ Δ] are separate premises, since Pi and Δ vary per case.) *)
Definition rho_fresh (Δρ : atoms) (Θ : aenv) (θ : metasubst) : Prop :=
  forall X, X `in` Δρ ->
    binds X abind_tvar Θ /\
    (forall p, In p θ -> X `notin` ftvar_in_ptyp (snd p)) /\
    (forall α τ, binds α (abind_flex_mono_def τ) Θ ->
       X `notin` ftvar_in_ptyp τ).

(* ===================================================================== *)
(*  Leaf inversion: partial precision at a rigid replaced-variable target  *)
(*  forces the subject to be EXACTLY that variable.                        *)
(* ===================================================================== *)

(** No partial-precision derivation targets [var X] from an [X]-free
    subject when [X] is a Δ-visible rigid tvar avoided by Θ's definition
    images: the var rule needs the occurrence, the hole rule is blocked
    by its Δ-disjointness premise, flex_l chains stay inside Θ's
    definition images, flex_r clashes with X's rigidity. *)
Lemma ad_ppre_var_target_absent : forall Θ Δ Ψ P ψ,
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  forall X, ψ = uskl_var_f X ->
  a_wf_aenv Θ ->
  X `in` Δ ->
  binds X abind_tvar Θ ->
  (forall α τ, binds α (abind_flex_mono_def τ) Θ ->
     X `notin` ftvar_in_ptyp τ) ->
  X `notin` ftvar_in_pskl P ->
  False.
Proof.
  intros Θ Δ Ψ P ψ H; induction H;
    intros X0 Heq Hwf HXΔ HXb Hdef Hftv; try discriminate Heq.
  - (* var *)
    inversion Heq; subst. simpl in Hftv. clear - Hftv; fsetdec.
  - (* hole: Δ ∩ ftvar(var X0) = ∅ vs X0 ∈ Δ *)
    subst ψ. simpl in H0. clear - H0 HXΔ; fsetdec.
  - (* tophole_remove *)
    simpl in Hftv. eapply IHad_partial_precise; eauto.
  - (* flex_l: subject var α unfolds to its Θ-scoped definition *)
    eapply IHad_partial_precise; eauto.
    pose proof (ptyp_to_pskl_ftv τ) as Hp.
    pose proof (Hdef _ _ H) as Hd. clear - Hp Hd; fsetdec.
  - (* flex_r: X0 both rigid and defined-flexible — wf-uniq clash *)
    inversion Heq; subst.
    pose proof (binds_unique _ _ _ _ _ H HXb (a_wf_aenv_uniq Hwf)) as Habs.
    discriminate Habs.
Qed.

(** THE LEAF INVERSION ([paper-gap]: the paper's positional side condition
    "P_i has the same rigid variable in the same position", recovered from
    the freshness of the replaced variable): at target [var X] with
    [X ∈ Δ], [X] rigid in Θ, [X] avoided by Θ's definition images and by
    the subject's ⊤◇-shielded variables, the subject IS [var X] and the
    solved tags are empty. *)
Lemma ad_ppre_delta_var_inv : forall Θ Δ Ψ P ψ,
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  forall X, ψ = uskl_var_f X ->
  a_wf_aenv Θ ->
  X `in` Δ ->
  binds X abind_tvar Θ ->
  (forall α τ, binds α (abind_flex_mono_def τ) Θ ->
     X `notin` ftvar_in_ptyp τ) ->
  X `notin` pskl_shielded_ftv P ->
  P = pskl_var_f X /\ Ψ [=] empty.
Proof.
  intros Θ Δ Ψ P ψ H; induction H;
    intros X0 Heq Hwf HXΔ HXb Hdef Hsh; try discriminate Heq.
  - (* var *)
    inversion Heq; subst. split; [ reflexivity | assumption ].
  - (* hole: blocked by Δ-disjointness *)
    exfalso. subst ψ. simpl in H0. clear - H0 HXΔ; fsetdec.
  - (* tophole_remove: the body is wholly shielded — absent-lemma kills *)
    exfalso. simpl in Hsh.
    eapply ad_ppre_var_target_absent; eauto.
  - (* flex_l: the unfolded definition is X0-free — absent-lemma kills *)
    exfalso.
    eapply (ad_ppre_var_target_absent H0 Heq Hwf HXΔ HXb Hdef).
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
    [a_flex_tvar] (positively) and [a_flex] (negatively). *)
Lemma a_solve_sub_eq_ctx_change :
  (forall Θ m P Q P', Θ ⊢ₛ P ≼[ m ] Q ⤳ P' ->
     forall Θ',
     (forall α, a_flex_tvar Θ α -> a_flex_tvar Θ' α) ->
     (forall P0, a_flex Θ' P0 -> a_flex Θ P0) ->
     Θ' ⊢ₛ P ≼[ m ] Q ⤳ P') /\
  (forall Θ P Q P', Θ ⊢ₑ P ∼ Q ⤳ P' ->
     forall Θ',
     (forall α, a_flex_tvar Θ α -> a_flex_tvar Θ' α) ->
     (forall P0, a_flex Θ' P0 -> a_flex Θ P0) ->
     Θ' ⊢ₑ P ∼ Q ⤳ P').
Proof.
  apply a_solve_sub_eq_mutind; intros;
    try solve [ econstructor; eauto ].
  - (* SE-FlexR *)
    match goal with
      Hb : a_flex_tvar _ _,
      Hnf : a_non_flex _ _,
      Hmono : forall _ : atom, a_flex_tvar _ _ -> a_flex_tvar _ _,
      Hfl : forall _ : pskl, a_flex _ _ -> a_flex _ _ |- _ =>
        destruct Hnf as [Hlc Hnf'];
        apply a_solve_eq__flex_r; [ apply Hmono; exact Hb | ];
        split; [ exact Hlc | intro Hf; exact (Hnf' (Hfl _ Hf)) ]
    end.
Qed.

(** Strengthening: drop a rigid tvar cons. *)
Lemma a_solve_eq_strengthen_tvar : forall β Θ0 P Q P',
  ((β ~ abind_tvar) ++ Θ0) ⊢ₑ P ∼ Q ⤳ P' ->
  Θ0 ⊢ₑ P ∼ Q ⤳ P'.
Proof.
  intros β Θ0 P Q P' H.
  eapply (proj2 a_solve_sub_eq_ctx_change); [ exact H | | ].
  - intros α Hft.
    destruct Hft as [Hb | [τ Hb]];
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq Habs] | Hb'];
      solve [ discriminate Habs
            | left; exact Hb'
            | right; exists τ; exact Hb' ].
  - intros P0 Hf; inversion Hf; subst.
    + apply a_flex__var with (α := α); unfold binds; simpl; right; auto.
    + apply a_flex__var_def with (α := α) (τ := τ);
        unfold binds; simpl; right; auto.
Qed.

Lemma a_solve_sub_strengthen_tvar : forall β Θ0 m P Q P',
  ((β ~ abind_tvar) ++ Θ0) ⊢ₛ P ≼[ m ] Q ⤳ P' ->
  Θ0 ⊢ₛ P ≼[ m ] Q ⤳ P'.
Proof.
  intros β Θ0 m P Q P' H.
  eapply (proj1 a_solve_sub_eq_ctx_change); [ exact H | | ].
  - intros α Hft.
    destruct Hft as [Hb | [τ Hb]];
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq Habs] | Hb'];
      solve [ discriminate Habs
            | left; exact Hb'
            | right; exists τ; exact Hb' ].
  - intros P0 Hf; inversion Hf; subst.
    + apply a_flex__var with (α := α); unfold binds; simpl; right; auto.
    + apply a_flex__var_def with (α := α) (τ := τ);
        unfold binds; simpl; right; auto.
Qed.

(** Weakening: add a rigid tvar cons. *)
Lemma a_solve_eq_weaken_tvar : forall β Θ0 P Q P',
  Θ0 ⊢ₑ P ∼ Q ⤳ P' ->
  ((β ~ abind_tvar) ++ Θ0) ⊢ₑ P ∼ Q ⤳ P'.
Proof.
  intros β Θ0 P Q P' H.
  eapply (proj2 a_solve_sub_eq_ctx_change); [ exact H | | ].
  - intros α Hft.
    destruct Hft as [Hb | [τ Hb]];
      [ left | right; exists τ ]; unfold binds; simpl; right; exact Hb.
  - intros P0 Hf; inversion Hf; subst;
      match goal with
        Hb : binds _ _ ((_ ~ abind_tvar) ++ _) |- _ =>
          destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq Habs] | Hb'];
          [ discriminate Habs
          | solve [ eapply a_flex__var; exact Hb'
                  | eapply a_flex__var_def; exact Hb' ] ]
      end.
Qed.

(** Rename preserves non-flexibility when both names are fresh from Θ. *)
Lemma a_non_flex_rename : forall Θ P X Y,
  X `notin` dom Θ -> Y `notin` dom Θ ->
  a_non_flex Θ P ->
  a_non_flex Θ (subst_pskl_in_pskl (pskl_var_f Y) X P).
Proof.
  intros Θ P X Y HX HY [Hlc Hnf].
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

(** Rename preserves guardedness ([var Y] is guarded). *)
Lemma guarded_pskl_rename : forall A X Y,
  guarded_pskl A ->
  guarded_pskl (subst_pskl_in_pskl (pskl_var_f Y) X A).
Proof.
  intros A X Y Hg; inversion Hg; subst; simpl.
  - constructor.
  - destruct_if;
      constructor.
  - constructor;
      (apply subst_pskl_in_pskl_lc_pskl;
        [ assumption | apply lc_pskl_var_f ]).
Qed.

(** Rigid-variable rename through the solve judgments (X, Y fresh from Θ,
    so the flex rules are untouched). *)
Lemma a_solve_sub_eq_rename :
  (forall Θ m P Q P', Θ ⊢ₛ P ≼[ m ] Q ⤳ P' ->
     forall X Y, X `notin` dom Θ -> Y `notin` dom Θ ->
     Θ ⊢ₛ (subst_pskl_in_pskl (pskl_var_f Y) X P) ≼[ m ]
          (subst_pskl_in_pskl (pskl_var_f Y) X Q)
          ⤳ (subst_pskl_in_pskl (pskl_var_f Y) X P')) /\
  (forall Θ P Q P', Θ ⊢ₑ P ∼ Q ⤳ P' ->
     forall X Y, X `notin` dom Θ -> Y `notin` dom Θ ->
     Θ ⊢ₑ (subst_pskl_in_pskl (pskl_var_f Y) X P)
        ∼ (subst_pskl_in_pskl (pskl_var_f Y) X Q)
        ⤳ (subst_pskl_in_pskl (pskl_var_f Y) X P')).
Proof.
  apply a_solve_sub_eq_mutind; intros; simpl;
    (* var-subject rules: the substituted subject is still a var *)
    try solve
      [ destruct_if;
        constructor
      | constructor ].
  - (* SS-ForallL *)
    apply a_solve_sub__forall_l with
      (L := L `union` singleton X `union` singleton Y).
    intros β Hβ.
    rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var P (pskl_var_f Y))
      by (solve [ clear - Hβ; fsetdec | constructor ]).
    rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var P' (pskl_var_f Y))
      by (solve [ clear - Hβ; fsetdec | constructor ]).
    apply H; [ clear - Hβ; fsetdec | assumption | assumption ].
  - (* SS-UnivGhostL *)
    apply a_solve_sub__univ_ghost_l; apply H; assumption.
  - (* SS-Check *)
    apply a_solve_sub__check;
      [ apply guarded_pskl_rename; assumption
      | apply guarded_pskl_rename; assumption
      | apply H; assumption ].
  - (* SS-ForallR *)
    apply a_solve_sub__forall_r with
      (L := L `union` singleton X `union` singleton Y).
    intros β Hβ.
    rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var B (pskl_var_f Y))
      by (solve [ clear - Hβ; fsetdec | constructor ]).
    apply H; [ clear - Hβ; fsetdec | assumption | assumption ].
  - (* SS-Arrow *)
    apply a_solve_sub__arrow; [ apply H | apply H0 ]; assumption.
  - (* SS-GhostLF *)
    apply a_solve_sub__ghost_l_fn; [ apply H | apply H0 ]; assumption.
  - (* SS-GhostL *)
    apply a_solve_sub__ghost_l; apply guarded_pskl_rename; assumption.
  - (* SE-FlexR *)
    assert (Hne : α <> X)
      by (match goal with Hft : a_flex_tvar _ α |- _ =>
            destruct Hft as [Hb | [τ0 Hb]]; apply binds_In in Hb;
            intro Heq; subst; contradiction
          end).
    destruct_if;
      [ exfalso; congruence | ].
    apply a_solve_eq__flex_r;
      [ assumption | apply a_non_flex_rename; assumption ].
  - (* SE-Arrow *)
    apply a_solve_eq__arrow; [ apply H | apply H0 ]; assumption.
  - (* SE-Forall *)
    apply a_solve_eq__forall with
      (L := L `union` singleton X `union` singleton Y).
    intros β Hβ.
    rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var P (pskl_var_f Y))
      by (solve [ clear - Hβ; fsetdec | constructor ]).
    rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q (pskl_var_f Y))
      by (solve [ clear - Hβ; fsetdec | constructor ]).
    rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var P' (pskl_var_f Y))
      by (solve [ clear - Hβ; fsetdec | constructor ]).
    apply H; [ clear - Hβ; fsetdec | assumption | assumption ].
  - (* SE-UnivGhost *)
    apply a_solve_eq__tophole_both; apply H; assumption.
  - (* SE-GhostForall *)
    apply a_solve_eq__tophole_l_all with
      (L := L `union` singleton X `union` singleton Y).
    intros β Hβ.
    rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q (pskl_var_f Y))
      by (solve [ clear - Hβ; fsetdec | constructor ]).
    rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var P' (pskl_var_f Y))
      by (solve [ clear - Hβ; fsetdec | constructor ]).
    specialize (H β ltac:(clear - Hβ; fsetdec) X Y H0 H1).
    simpl in H. exact H.
  - (* SE-GhostGuarded *)
    apply a_solve_eq__tophole_l_guarded;
      [ apply guarded_pskl_rename; assumption | apply H; assumption ].
  - (* SE-ForallGhost *)
    apply a_solve_eq__all_l_tophole with
      (L := L `union` singleton X `union` singleton Y).
    intros β Hβ.
    rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var P (pskl_var_f Y))
      by (solve [ clear - Hβ; fsetdec | constructor ]).
    rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var P' (pskl_var_f Y))
      by (solve [ clear - Hβ; fsetdec | constructor ]).
    specialize (H β ltac:(clear - Hβ; fsetdec) X Y H0 H1).
    simpl in H. exact H.
  - (* SE-GuardedGhost *)
    apply a_solve_eq__tophole_r_guarded;
      [ apply guarded_pskl_rename; assumption | apply H; assumption ].
Qed.

(* ===================================================================== *)
(*  Shape/tags helpers for the special cases (P0 = □; synthesized Q).      *)
(* ===================================================================== *)

(** Syn-paintings are synthesized skeletons. *)
Lemma is_sskl_pskl_to_bskl_syn : forall P,
  lc_pskl P -> is_sskl (pskl_to_bskl_syn P).
Proof.
  intros P Hlc; induction Hlc; simpl; try solve [ constructor; auto ].
  apply is_sskl__all with (L := {}).
  intros X _. rewrite <- pskl_to_bskl_syn_open. auto.
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
Lemma ad_pat_consis_sskl_tags : forall Ψ Θ S Q,
  Ψ ⨟ Θ ⊢ₛᵃ S ∼ Q ->
  a_wf_aenv Θ ->
  is_sskl Q ->
  Ψ [=] empty.
Proof.
  intros Ψ Θ S Q H; induction H; intros Hwf Hsk;
    try solve [ assumption | inversion Hsk ].
  - (* arrow *)
    inversion Hsk; subst.
    specialize (IHad_pat_consis1 Hwf ltac:(assumption)).
    specialize (IHad_pat_consis2 Hwf ltac:(assumption)).
    fsetdec.
  - (* forall_syn_tagged *)
    inversion Hsk; subst.
    match goal with HskB : forall X, X `notin` ?L0 -> is_sskl _ |- _ =>
      pick fresh X for (L `union` L0 `union` dom Θ);
      apply (H0 X ltac:(fsetdec));
      [ apply a_wf_aenv__tvar; [ fsetdec | exact Hwf ]
      | apply HskB; fsetdec ]
    end.
  - (* forall_syn *)
    inversion Hsk; subst.
    match goal with HskB : forall X, X `notin` ?L0 -> is_sskl _ |- _ =>
      pick fresh X for (L `union` L0 `union` dom Θ);
      apply (H0 X ltac:(fsetdec));
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

Lemma pskl_shielded_ftv_open_rec_lower : forall P V k,
  pskl_shielded_ftv P [<=]
  pskl_shielded_ftv (open_pskl_wrt_pskl_rec k V P).
Proof.
  induction P; intros V k; simpl; try fsetdec.
  - pose proof (IHP1 V k); pose proof (IHP2 V k); fsetdec.
  - apply IHP.
  - pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_rec_lower P V k); fsetdec.
Qed.

Lemma pskl_shielded_ftv_open_rec_upper : forall P V k,
  pskl_shielded_ftv (open_pskl_wrt_pskl_rec k V P) [<=]
  pskl_shielded_ftv P `union` ftvar_in_pskl V.
Proof.
  induction P; intros V k; simpl; try fsetdec.
  - (* var_b *)
    destruct (lt_eq_lt_dec n k) as [[Hlt | Heq] | Hgt]; simpl;
      try fsetdec.
    pose proof (pskl_shielded_ftv_sub_ftv V); fsetdec.
  - pose proof (IHP1 V k); pose proof (IHP2 V k); fsetdec.
  - apply IHP.
  - pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_rec_upper P V k); fsetdec.
Qed.

Lemma pskl_shielded_ftv_open_lower : forall P V,
  pskl_shielded_ftv P [<=]
  pskl_shielded_ftv (open_pskl_wrt_pskl P V).
Proof. intros; apply pskl_shielded_ftv_open_rec_lower. Qed.

Lemma pskl_shielded_ftv_open_upper : forall P V,
  pskl_shielded_ftv (open_pskl_wrt_pskl P V) [<=]
  pskl_shielded_ftv P `union` ftvar_in_pskl V.
Proof. intros; apply pskl_shielded_ftv_open_rec_upper. Qed.

(** Solving bounds the output's shielded variables by the subject's
    shielded variables plus ALL of the target's variables. *)
Lemma a_solve_sub_eq_shielded :
  (forall Θ m P Q P', Θ ⊢ₛ P ≼[ m ] Q ⤳ P' ->
     pskl_shielded_ftv P' [<=]
     pskl_shielded_ftv P `union` ftvar_in_pskl Q) /\
  (forall Θ P Q P', Θ ⊢ₑ P ∼ Q ⤳ P' ->
     pskl_shielded_ftv P' [<=]
     pskl_shielded_ftv P `union` ftvar_in_pskl Q).
Proof.
  apply a_solve_sub_eq_mutind; intros; simpl in *;
    (* ⊤◇-bodied outputs: switch to the ftv bound *)
    try solve
      [ fsetdec
      | match goal with
        | Hs : _ ⊢ₛ ?P0 ≼[ _ ] ?Q0 ⤳ ?P0' |- _ =>
            pose proof (a_solve_sub_ftv Hs)
        | He : _ ⊢ₑ ?P0 ∼ ?Q0 ⤳ ?P0' |- _ =>
            pose proof ((proj2 a_solve_sub_eq_ftv) _ _ _ _ He)
        end; fsetdec
      | pose proof (pskl_shielded_ftv_sub_ftv Q); fsetdec ].
  - (* SS-ForallL: ∀P ≼ Q ⤳ ∀P' *)
    pick fresh β for
      (L `union` pskl_shielded_ftv P' `union` pskl_shielded_ftv P).
    specialize (H β ltac:(fsetdec)).
    pose proof (pskl_shielded_ftv_open_lower P' (pskl_var_f β)).
    pose proof (pskl_shielded_ftv_open_upper P (pskl_var_f β)).
    simpl in *. fsetdec.
  - (* SS-ForallR: target opens *)
    pick fresh β for (L `union` pskl_shielded_ftv P').
    specialize (H β ltac:(fsetdec)).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B (pskl_var_f β)).
    simpl in *. fsetdec.
  - (* SS-GhostLF: output ⊤◇(P1'→P2') *)
    match goal with
      He1 : _ ⊢ₑ pskl_hole ∼ _ ⤳ _, Hs2 : _ ⊢ₛ pskl_hole ≼[ _ ] _ ⤳ _ |- _ =>
        pose proof ((proj2 a_solve_sub_eq_ftv) _ _ _ _ He1);
        pose proof (a_solve_sub_ftv Hs2)
    end.
    simpl in *. fsetdec.
  - (* SE-Forall *)
    pick fresh β for
      (L `union` pskl_shielded_ftv P' `union` pskl_shielded_ftv P).
    specialize (H β ltac:(fsetdec)).
    pose proof (pskl_shielded_ftv_open_lower P' (pskl_var_f β)).
    pose proof (pskl_shielded_ftv_open_upper P (pskl_var_f β)).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q (pskl_var_f β)).
    simpl in *. fsetdec.
  - (* SE-GhostForall: subject stays ⊤◇P *)
    pick fresh β for (L `union` pskl_shielded_ftv P').
    specialize (H β ltac:(fsetdec)).
    pose proof (pskl_shielded_ftv_open_lower P' (pskl_var_f β)).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q (pskl_var_f β)).
    simpl in *. fsetdec.
  - (* SE-GhostGuarded: subject ⊤◇P peels *)
    pose proof (pskl_shielded_ftv_sub_ftv P).
    simpl in *. fsetdec.
  - (* SE-ForallGhost *)
    pick fresh β for
      (L `union` pskl_shielded_ftv P' `union` pskl_shielded_ftv P).
    specialize (H β ltac:(fsetdec)).
    pose proof (pskl_shielded_ftv_open_lower P' (pskl_var_f β)).
    pose proof (pskl_shielded_ftv_open_upper P (pskl_var_f β)).
    simpl in *. fsetdec.
Qed.

(* ===================================================================== *)
(*  msubst-avoidance: a variable fresh from θ's images survives msubst.    *)
(* ===================================================================== *)

Lemma msubst_lookup_ftv_avoid : forall θ X Y,
  (forall p, In p θ -> X `notin` ftvar_in_ptyp (snd p)) ->
  X `in` ftvar_in_ptyp (msubst_lookup θ Y) ->
  Y = X.
Proof.
  induction θ as [ | [Z τ] θ' IH ]; intros X Y Hav HX; simpl in HX.
  - clear - HX; fsetdec.
  - destruct (Y == Z) as [Heq | Hne].
    + exfalso. apply (Hav (Z, τ) (or_introl eq_refl)). exact HX.
    + apply IH; [ intros p Hp; apply Hav; right; exact Hp | exact HX ].
Qed.

Lemma msubst_pskl_ftv_avoid : forall θ P X,
  (forall p, In p θ -> X `notin` ftvar_in_ptyp (snd p)) ->
  X `notin` ftvar_in_pskl P ->
  X `notin` ftvar_in_pskl (msubst_pskl θ P).
Proof.
  intros θ P X Hav.
  induction P as [ | n | Y | Pa IHa Pb IHb | Pall IHall | | Pt IHt ];
    intros Hni HX; simpl in *.
  - fsetdec.
  - fsetdec.
  - (* var *)
    pose proof (ftvar_in_ptyp_to_pskl (msubst_lookup θ Y)) as Hp.
    assert (HX' : X `in` ftvar_in_ptyp (msubst_lookup θ Y))
      by (clear - HX Hp; fsetdec).
    apply msubst_lookup_ftv_avoid in HX'; [ subst | exact Hav ].
    clear - Hni; fsetdec.
  - apply union_1 in HX; destruct HX as [HX | HX];
      [ apply IHa | apply IHb ];
      solve [ clear - Hni; fsetdec | exact HX ].
  - apply IHall; [ clear - Hni; fsetdec | exact HX ].
  - fsetdec.
  - apply IHt; [ clear - Hni; fsetdec | exact HX ].
Qed.

(** Monotype paintings shield nothing. *)
Lemma pskl_shielded_ftv_ptyp_to_pskl : forall A,
  pskl_shielded_ftv (ptyp_to_pskl A) [=] {}.
Proof. induction A; simpl; fsetdec. Qed.

Lemma msubst_pskl_shielded_avoid : forall θ P X,
  (forall p, In p θ -> X `notin` ftvar_in_ptyp (snd p)) ->
  X `notin` pskl_shielded_ftv P ->
  X `notin` pskl_shielded_ftv (msubst_pskl θ P).
Proof.
  intros θ P X Hav.
  induction P as [ | n | Y | Pa IHa Pb IHb | Pall IHall | | Pt IHt ];
    intros Hni HX; simpl in *.
  - fsetdec.
  - fsetdec.
  - (* var: the image is a painting — nothing shielded *)
    pose proof (pskl_shielded_ftv_ptyp_to_pskl (msubst_lookup θ Y)) as He.
    clear - He HX; fsetdec.
  - apply union_1 in HX; destruct HX as [HX | HX];
      [ apply IHa | apply IHb ];
      solve [ clear - Hni; fsetdec | exact HX ].
  - apply IHall; [ exact Hni | exact HX ].
  - fsetdec.
  - (* tophole: the whole body's ftv *)
    revert HX. apply msubst_pskl_ftv_avoid; [ exact Hav | exact Hni ].
Qed.

(** msubst-image of a var: recover the var (X avoided by θ's images). *)
Lemma msubst_pskl_var_inv : forall θ Pi X,
  (forall p, In p θ -> X `notin` ftvar_in_ptyp (snd p)) ->
  msubst_pskl θ Pi = pskl_var_f X ->
  Pi = pskl_var_f X.
Proof.
  intros θ Pi X Hav Heq.
  destruct Pi as [ | n | Y | | | | ]; simpl in Heq; try discriminate Heq.
  f_equal.
  assert (HX : X `in` ftvar_in_ptyp (msubst_lookup θ Y)).
  { pose proof (ftvar_in_ptyp_to_pskl (msubst_lookup θ Y)) as Hp.
    rewrite Heq in Hp. simpl in Hp. clear - Hp; fsetdec. }
  eapply msubst_lookup_ftv_avoid; eassumption.
Qed.

(* ===================================================================== *)
(*  The packaged -var LEAF case (paper: <<If ψa is a rigid variable        *)
(*  substituted by ρ, then P_i = ψa.  The tag contexts Ψ_i and Ψ_a are     *)
(*  empty, and the goal follows from SE-Var (SS-Var), choosing             *)
(*  P_a = P_i and θ_a = θ.>>  consistency-proofs.tex:1249-1252).           *)
(*  Both P6-Cv and P6-Sv consume it: [SE-Var]/[SS-Var] fire on the         *)
(*  recovered var subject against ANY target.                              *)
(* ===================================================================== *)

Lemma p6_leaf_var : forall NM Θ θ Pi Δ X Ψ' Ψi Ψna,
  a_wf_aenv Θ ->
  a_tags_sort NM Ψ' (uskl_var_f X) ->
  Ψi [<=] Ψ' ->
  Ψna [<=] Ψ' ->
  X `in` Δ ->
  binds X abind_tvar Θ ->
  (forall p, In p θ -> X `notin` ftvar_in_ptyp (snd p)) ->
  (forall α τ, binds α (abind_flex_mono_def τ) Θ ->
     X `notin` ftvar_in_ptyp τ) ->
  X `notin` pskl_shielded_ftv Pi ->
  Θ ⨟ Δ ⊢ (msubst_pskl θ Pi) ⊑ᵖ[ Ψi ] (uskl_var_f X) ->
  Pi = pskl_var_f X /\
  Ψi [=] empty /\
  Ψna [=] empty /\
  Θ ⨟ Δ ⊢ (msubst_pskl θ Pi) ⊑ᵖ[ Ψi `union` Ψna ] (uskl_var_f X).
Proof.
  intros NM Θ θ Pi Δ X Ψ' Ψi Ψna
    Hwf Htag HΨi HΨna HXΔ HXb Hθav Hdef Hsh Hpre.
  assert (Hshθ : X `notin` pskl_shielded_ftv (msubst_pskl θ Pi))
    by (apply msubst_pskl_shielded_avoid; assumption).
  destruct (ad_ppre_delta_var_inv Hpre eq_refl Hwf HXΔ HXb Hdef Hshθ)
    as [Heqm HΨie].
  assert (HeqPi : Pi = pskl_var_f X)
    by (eapply msubst_pskl_var_inv; eassumption).
  assert (HΨ'e : Ψ' [=] empty)
    by (exact (d_tags_skl_var_inv (a_tags_sort_d_tags Htag))).
  split; [ exact HeqPi | ].
  split; [ exact HΨie | ].
  split; [ clear - HΨna HΨ'e; fsetdec | ].
  rewrite Heqm.
  apply ad_ppre__var; [ clear - HΨie HΨna HΨ'e; fsetdec | left; exact HXΔ ].
Qed.

(* ===================================================================== *)
(*  P6-Cv support kit: solve-eq determinism on the hole subject, wf        *)
(*  preservation for [a_solve_eq], Θ-weakening of the ρ relation, and      *)
(*  the Θ-tvar strengthening of partial precision (for the binder cases    *)
(*  whose IH runs at [(X~tvar)++Θ]).                                       *)
(* ===================================================================== *)

(** Solving with the hole subject returns the target verbatim (the only
    applicable rules are SE-GhostL / SE-VacuousR / SE-FlexR).  The paper
    uses this silently in every [P_i = □] subcase: the IH's existential
    output IS the target. *)
Lemma a_solve_eq_hole_subject_inv : forall Θ Q P',
  Θ ⊢ₑ pskl_hole ∼ Q ⤳ P' ->
  P' = Q.
Proof.
  intros Θ Q P' H; inversion H; subst; try reflexivity;
    inv_guarded_hole.
Qed.

(** Θ-weakening of the ρ relation (binds-monotone; the leaf's image wf
    weakens). *)
Lemma uskl_rho_weaken : forall NM Θ Δρ Ψρ S R,
  uskl_rho NM Θ Δρ Ψρ S R ->
  forall Θ', (forall x b, binds x b Θ -> binds x b Θ') ->
  uskl_rho NM Θ' Δρ Ψρ S R.
Proof.
  intros NM Θ Δρ Ψρ S R H; induction H; intros Θ' Hmon.
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
Lemma binds_mid_drop : forall (Θ1 Θ0 : aenv) X Y (b bmid : abind),
  binds Y b (Θ1 ++ (X ~ bmid) ++ Θ0) ->
  (Y = X -> b <> bmid) ->
  binds Y b (Θ1 ++ Θ0).
Proof.
  intros Θ1 Θ0 X Y b bmid Hb Hne.
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
  forall Z Θ1 Θ0,
  Θfull = Θ1 ++ (Z ~ abind_tvar) ++ Θ0 ->
  Z `in` Δ ->
  (Θ1 ++ Θ0) ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ.
Proof.
  intros Θfull Δ Ψ P ψ H; induction H; intros Z Θ1 Θ0 Heq HZΔ; subst.
  - apply ad_ppre__unit; assumption.
  - apply ad_ppre__var; [ assumption | ].
    destruct H0 as [HΔ | [Hb | [Hb | [τ Hb]]]].
    + left; exact HΔ.
    + destruct (X == Z) as [HeqXZ | HneXZ];
        [ subst; left; exact HZΔ
        | right; left; exact (binds_remove_mid _ _ _ _ _ _ _ Hb HneXZ) ].
    + right; right; left.
      eapply binds_mid_drop; [ exact Hb | intros _ Habs; discriminate Habs ].
    + right; right; right; exists τ.
      eapply binds_mid_drop; [ exact Hb | intros _ Habs; discriminate Habs ].
  - eapply ad_ppre__arrow;
      [ apply (IHad_partial_precise1 Z Θ1 Θ0 eq_refl HZΔ)
      | apply (IHad_partial_precise2 Z Θ1 Θ0 eq_refl HZΔ)
      | assumption ].
  - eapply ad_ppre__forall with (L := L);
      [ intros X HX;
        apply (H0 X HX Z Θ1 Θ0 eq_refl); clear - HZΔ; fsetdec
      | assumption ].
  - apply ad_ppre__hole; assumption.
  - apply ad_ppre__tophole_remove.
    apply (IHad_partial_precise Z Θ1 Θ0 eq_refl HZΔ).
  - eapply ad_ppre__tophole_fill with (L := L).
    intros X HX.
    apply (H0 X HX Z ((X ~ abind_tvar) ++ Θ1) Θ0 eq_refl HZΔ).
  - apply ad_ppre__tophole_keep.
    apply (IHad_partial_precise Z Θ1 Θ0 eq_refl HZΔ).
  - eapply ad_ppre__flex_l;
      [ eapply binds_mid_drop;
        [ exact H | intros _ Habs; discriminate Habs ]
      | apply (IHad_partial_precise Z Θ1 Θ0 eq_refl HZΔ) ].
  - eapply ad_ppre__flex_r;
      [ eapply binds_mid_drop;
        [ exact H | intros _ Habs; discriminate Habs ]
      | apply (IHad_partial_precise Z Θ1 Θ0 eq_refl HZΔ) ].
Qed.

Lemma ad_partial_precise_strengthen_tvar : forall Z Θ0 Δ Ψ P ψ,
  ((Z ~ abind_tvar) ++ Θ0) ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  Z `in` Δ ->
  Θ0 ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ.
Proof.
  intros Z Θ0 Δ Ψ P ψ H HZ.
  exact (@ad_partial_precise_strengthen_tvar_mid _ _ _ _ _ H Z nil Θ0
           eq_refl HZ).
Qed.

(** wf preservation for [a_solve_eq] (Δ-uniform; a non-mutual induction —
    the eq half never calls the sub half).  Discharges the paper's
    [Θ0 ⊢ P_a] conclusion of the -var lemmas OUTSIDE their inductions. *)
Lemma a_solve_eq_wf : forall Θ P Q P',
  Θ ⊢ₑ P ∼ Q ⤳ P' ->
  forall Δ,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  Θ ⨟ Δ ⊢ₚₛᵃ Q ->
  Θ ⨟ Δ ⊢ₚₛᵃ P'.
Proof.
  intros Θ P Q P' H; induction H; intros Δ HwfP HwfQ.
  - (* SE-Unit *) apply a_wf_pskl__unit.
  - (* SE-Var *) exact HwfP.
  - (* SE-FlexR *) exact HwfQ.
  - (* SE-GhostL *) exact HwfQ.
  - (* SE-VacuousR *) exact HwfP.
  - (* SE-Arrow *)
    inversion HwfP; subst; inversion HwfQ; subst.
    apply a_wf_pskl__arrow; [ apply IHa_solve_eq1 | apply IHa_solve_eq2 ];
      assumption.
  - (* SE-Forall *)
    inversion HwfP as [ | | | L1 ? ? ? HbP | | ]; subst.
    inversion HwfQ as [ | | | L2 ? ? ? HbQ | | ]; subst.
    apply a_wf_pskl__all with (L := L `union` L1 `union` L2).
    intros X HX.
    apply H0; solve [ clear - HX; fsetdec
                    | apply HbP; clear - HX; fsetdec
                    | apply HbQ; clear - HX; fsetdec ].
  - (* SE-UnivGhost *)
    destruct (a_wf_pskl_tophole_inv HwfP) as [HgP HwfP0].
    destruct (a_wf_pskl_tophole_inv HwfQ) as [HgQ HwfQ0].
    apply a_wf_pskl__tophole.
    + eapply (proj2 a_solve_sub_eq_guarded);
        eauto using a_wf_pskl_lc.
    + apply IHa_solve_eq; assumption.
  - (* SE-GhostForall *)
    destruct (a_wf_pskl_tophole_inv HwfP) as [HgP HwfP0].
    inversion HwfQ as [ | | | L2 ? ? ? HbQ | | ]; subst.
    apply a_wf_pskl__all with (L := L `union` L2).
    intros X HX.
    apply H0;
      solve [ clear - HX; fsetdec
            | apply a_wf_pskl__tophole; assumption
            | apply HbQ; clear - HX; fsetdec ].
  - (* SE-GhostGuarded *)
    destruct (a_wf_pskl_tophole_inv HwfP) as [HgP HwfP0].
    apply IHa_solve_eq;
      [ apply (a_wf_pskl_delta_mono HwfP0); clear; fsetdec | exact HwfQ ].
  - (* SE-ForallGhost *)
    inversion HwfP as [ | | | L1 ? ? ? HbP | | ]; subst.
    destruct (a_wf_pskl_tophole_inv HwfQ) as [HgQ HwfQ0].
    apply a_wf_pskl__all with (L := L `union` L1).
    intros X HX.
    apply H0;
      solve [ clear - HX; fsetdec
            | apply HbP; clear - HX; fsetdec
            | apply a_wf_pskl__tophole; assumption ].
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
    target [ψa] is a replaced rigid variable [var X], the freshness pack
    forces [Pi = var X], and SE-Var solves with [Pa := Pi].  Uniform across
    all 15 cases of the main induction. *)
Lemma p6cv_close_leaf :
  forall NM Θ0 Θ θ Δ Δρ Ψρ Ψ' Ψi Ψa ψsub ψa Pi P0,
  a_wf_aenv Θ ->
  a_tags_sort NM Ψ' ψa ->
  Ψi `union` Ψa [<=] Ψ' ->
  rho_fresh Δρ Θ θ ->
  Δρ [<=] Δ ->
  (forall X, X `in` Δρ -> X `notin` pskl_shielded_ftv (msubst_pskl θ Pi)) ->
  Θ ⨟ Δ ⊢ (msubst_pskl θ Pi) ⊑ᵖ[ Ψi ] ψa ->
  rho_leaf NM Θ Δρ Ψρ ψsub ψa ->
  exists Pa, Θ0 ⊢ₑ Pi ∼ P0 ⤳ Pa /\
             Θ ⨟ Δ ⊢ (msubst_pskl θ Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa.
Proof.
  intros NM Θ0 Θ θ Δ Δρ Ψρ Ψ' Ψi Ψa ψsub ψa Pi P0
    HwfΘ Htags Hsub Hfresh Hdelta Hshield Hpre Hleaf.
  destruct Hleaf as (X & Ψ'' & Heqψa & HXΔρ & Htagsub & Hwfsub & HΨρ).
  subst ψa.
  pose proof (Hfresh X HXΔρ) as (HXb & Hθav & Hdef).
  assert (HXΔ : X `in` Δ) by (clear - Hdelta HXΔρ; fsetdec).
  pose proof (Hshield X HXΔρ) as Hsh.
  destruct (ad_ppre_delta_var_inv Hpre eq_refl HwfΘ HXΔ HXb Hdef Hsh)
    as (Heqm & HΨie).
  assert (HeqPi : Pi = pskl_var_f X)
    by (eapply msubst_pskl_var_inv; eassumption).
  assert (HΨ'e : Ψ' [=] empty)
    by (exact (d_tags_skl_var_inv (a_tags_sort_d_tags Htags))).
  assert (HΨae : Ψa [=] empty) by (clear - Hsub HΨ'e; fsetdec).
  exists Pi. split.
  - rewrite HeqPi. apply a_solve_eq__var.
  - rewrite Heqm.
    apply ad_ppre__var; [ clear - HΨie HΨae; fsetdec | left; exact HXΔ ].
Qed.

(** Painting inversions.  An inherited painting equals a compound [bskl]
    only for the matching [pskl] source; since [θ] maps flexibles to
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
    induction follows [flex_l] definition chains and strips ⊤◇ via
    [tophole_remove].  Discharges the [Pi = □] and ⊤◇-[P0] subcases of the
    Unit consistency case (conclusion: [msubst θ P0 ⊑ᵖ[∅] unit]). *)
Lemma ad_refine_inh_unit_ppre : forall Θ Δr Lhs RHS,
  a_wf_aenv Θ ->
  Θ ⨟ Δr ⊢ᵣᵃ Lhs ⊳ RHS ->
  RHS = bskl_unit ->
  forall P' Δ, Lhs = pskl_to_bskl_inh P' ->
  Θ ⨟ Δ ⊢ P' ⊑ᵖ[ empty ] uskl_unit.
Proof.
  intros Θ Δr Lhs RHS Hwf H; induction H; intros HR P' Δo Heq;
    try discriminate HR; subst.
  - (* unit *)
    destruct P'; simpl in Heq; try discriminate Heq.
    apply ad_ppre__unit. fsetdec.
  - (* hole: RHS = pskl_to_bskl_syn P, forced = unit *)
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
Lemma msubst_lookup_notin_dom : forall ρ X,
  X `notin` dom ρ ->
  msubst_lookup ρ X = ptyp_var_f X.
Proof.
  induction ρ as [ | [Y τ] ρ' IH ]; intros X Hni; simpl in *; auto.
  destruct (X == Y) as [->|Hne]; [ exfalso; auto | ].
  apply IH. auto.
Qed.

Lemma a_inc_dom_flex : forall Θ0 ρ Θ X,
  ρ ∷ Θ0 ⊑ Θ ->
  X `in` dom ρ ->
  a_flex_tvar Θ0 X.
Proof.
  intros Θ0 ρ Θ X Hinc; induction Hinc; intros Hin; simpl in Hin.
  - fsetdec.
  - destruct (X == α) as [->|Hne].
    + left. simpl_env. auto.
    + assert (Ht : X `in` dom ρ) by (clear - Hin Hne; fsetdec).
      destruct (IHHinc Ht) as [Hb | [τ0 Hb]].
      * left. apply binds_cons_3; assumption.
      * right; exists τ0. apply binds_cons_3; assumption.
  - destruct (X == α) as [->|Hne].
    + right; exists τ. simpl_env. auto.
    + assert (Ht : X `in` dom ρ) by (clear - Hin Hne; fsetdec).
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

Lemma msubst_pskl_tvar_id : forall Θ0 ρ Θ X,
  a_wf_aenv Θ0 ->
  ρ ∷ Θ0 ⊑ Θ ->
  binds X abind_tvar Θ0 ->
  msubst_pskl ρ (pskl_var_f X) = pskl_var_f X.
Proof.
  intros Θ0 ρ Θ X Hwf Hinc Hb.
  simpl. rewrite msubst_lookup_notin_dom; [ reflexivity | ].
  intros Hin. pose proof (a_inc_dom_flex Hinc Hin) as Hfl.
  pose proof (a_wf_aenv_uniq Hwf) as Huniq.
  destruct Hfl as [Hbf | [τ Hbf]];
    pose proof (binds_unique _ _ _ _ _ Hb Hbf Huniq) as Hc; discriminate Hc.
Qed.

(** A rigid variable cannot refine into [unit] (only [flex_l] could fire,
    but its [α] would be a defined flexible, clashing with rigidity).  Used
    to discharge the P0 = rigid-variable subcase of the Unit case. *)
Lemma ad_refine_syn_rigid_var_unit_absurd : forall Θ Δ X,
  a_wf_aenv Θ ->
  binds X abind_tvar Θ ->
  Θ ⨟ Δ ⊢ᵣᵃ (bskl_var_f X) ⊳ bskl_unit ->
  False.
Proof.
  intros Θ Δ X Hwf Hb H; inversion H; subst;
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
   binder context Δ.  Strong induction on [size Pi + size P0] so the ⊤◇
   stripping (Pi and P0 sides) recurses. *)
Lemma a_solve_eq_cv_unit : forall n Θ0 Θ θ Δ Ψi Pi P0,
  size_pskl Pi + size_pskl P0 <= n ->
  a_wf_aenv Θ -> a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ Pi -> Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  θ ∷ Θ0 ⊑ Θ ->
  Θ ⨟ Δ ⊢ (msubst_pskl θ Pi) ⊑ᵖ[ Ψi ] uskl_unit ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl θ P0)) ⊳ bskl_unit ->
  exists Pa, Θ0 ⊢ₑ Pi ∼ P0 ⤳ Pa /\
             Θ ⨟ Δ ⊢ (msubst_pskl θ Pa) ⊑ᵖ[ Ψi ] uskl_unit.
Proof.
  induction n; intros Θ0 Θ θ Δ Ψi Pi P0 Hn
    HwfΘ HwfΘ0 HwfPi HwfP0 Hθ Hpre Hrefine.
  { pose proof (size_pskl_min Pi); pose proof (size_pskl_min P0); lia. }
  pose proof (ad_ppre_unit_tags_empty Hpre) as HΨi.
  destruct Pi as [ | nb | X | Pi1 Pi2 | Pib | | Pi' ].
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
        assert (Hmid : msubst_pskl θ (pskl_var_f α) = pskl_var_f α)
          by (eapply msubst_pskl_tvar_id; eauto).
        rewrite Hmid in Hrefine; simpl in Hrefine.
        eapply ad_refine_syn_rigid_var_unit_absurd;
          [ exact HwfΘ | eapply a_inc_binds_tvar; eauto | exact Hrefine ].
      * (* undefined flex : SE-FlexR *)
        exists (pskl_var_f α); split.
        -- apply a_solve_eq__flex_r;
             [ left; exact Hfm | split; [ constructor | intros Hf; inversion Hf ] ].
        -- eapply ad_partial_precise_psi_cong;
             [ eapply ad_refine_inh_unit_ppre;
                 [ exact HwfΘ | exact Hrefine | reflexivity | reflexivity ]
             | clear - HΨi; fsetdec ].
      * (* defined flex : SE-FlexR *)
        exists (pskl_var_f α); split.
        -- apply a_solve_eq__flex_r;
             [ right; exists τ; exact Hfd
             | split; [ constructor | intros Hf; inversion Hf ] ].
        -- eapply ad_partial_precise_psi_cong;
             [ eapply ad_refine_inh_unit_ppre;
                 [ exact HwfΘ | exact Hrefine | reflexivity | reflexivity ]
             | clear - HΨi; fsetdec ].
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
      | Href' : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl θ P0') ⊳ bskl_unit,
        HwfP0' : _ ⨟ _ ⊢ₚₛᵃ P0' |- _ =>
        destruct (IHn Θ0 Θ θ Δ Ψi pskl_unit P0'
                    ltac:(simpl in Hn; simpl; lia)
                    HwfΘ HwfΘ0 HwfPi HwfP0' Hθ Hpre Href')
          as [Pa [Hsolve Hprec]]
      end.
      exists Pa; split;
        [ apply a_solve_eq__tophole_r_guarded; [ constructor | exact Hsolve ]
        | exact Hprec ].
  - (* Pi = var_b : not wf *) inversion HwfPi.
  - (* Pi = var_f X : SE-Var *)
    exists (pskl_var_f X); split; [ apply a_solve_eq__var | exact Hpre ].
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
      | Hpre' : _ ⨟ _ ⊢ msubst_pskl θ Pi' ⊑ᵖ[ _ ] uskl_unit,
        HwfPi' : _ ⨟ _ ⊢ₚₛᵃ Pi' |- _ =>
        destruct (IHn Θ0 Θ θ Δ Ψi Pi' pskl_unit
                    ltac:(simpl in Hn; simpl; lia)
                    HwfΘ HwfΘ0 HwfPi' HwfP0 Hθ Hpre' Hrefine)
          as [Pa [Hsolve Hprec]]
      end.
      exists Pa; split;
        [ apply a_solve_eq__tophole_l_guarded; [ constructor | exact Hsolve ]
        | exact Hprec ].
    + (* P0 = var_b *) inversion HwfP0.
    + (* P0 = var_f α : GhostGuarded (var guarded), recurse (Pi', var α) *)
      match goal with
      | Hpre' : _ ⨟ _ ⊢ msubst_pskl θ Pi' ⊑ᵖ[ _ ] uskl_unit,
        HwfPi' : _ ⨟ _ ⊢ₚₛᵃ Pi' |- _ =>
        destruct (IHn Θ0 Θ θ Δ Ψi Pi' (pskl_var_f α)
                    ltac:(simpl in Hn; simpl; lia)
                    HwfΘ HwfΘ0 HwfPi' HwfP0 Hθ Hpre' Hrefine)
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
      | Hpre' : _ ⨟ _ ⊢ msubst_pskl θ Pi' ⊑ᵖ[ _ ] uskl_unit,
        Href' : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl θ P0') ⊳ bskl_unit,
        HwfPi' : _ ⨟ _ ⊢ₚₛᵃ Pi',
        HwfP0' : _ ⨟ _ ⊢ₚₛᵃ P0' |- _ =>
        destruct (IHn Θ0 Θ θ Δ Ψi Pi' P0'
                    ltac:(simpl in Hn; simpl; lia)
                    HwfΘ HwfΘ0 HwfPi' HwfP0' Hθ Hpre' Href')
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

Lemma ptyp_to_uskl_syn_var_inv : forall τ X,
  ptyp_to_uskl_syn τ = uskl_var_f X -> τ = ptyp_var_f X.
Proof.
  intros τ X H; destruct τ; simpl in H; try discriminate.
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

Lemma ptyp_to_bskl_syn_var_inv : forall τ X,
  ptyp_to_bskl_syn τ = bskl_var_f X -> τ = ptyp_var_f X.
Proof.
  intros τ X H; destruct τ; simpl in H; try discriminate.
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

(* ---- θ-image monotypes ---- *)

Lemma a_inc_lookup_mono : forall Θ0 θ Θ X,
  θ ∷ Θ0 ⊑ Θ ->
  mono_ptyp (msubst_lookup θ X).
Proof.
  intros Θ0 θ Θ X Hinc; induction Hinc; simpl; auto.
  - auto with frost.
  - destruct (X == α); subst; auto.
  - destruct (X == α); subst; auto.
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
  forall Y α τ, Y `in` Δ ->
    binds α (abind_flex_mono_def τ) Θ ->
    Y `notin` ftvar_in_ptyp τ.

(* ---- definition chains (target-side flex unfolding) ---- *)

Inductive a_def_chain (Θ : aenv) : ptyp -> ptyp -> Prop :=
| a_def_chain_refl : forall τ, a_def_chain Θ τ τ
| a_def_chain_step : forall X τd τe,
    binds X (abind_flex_mono_def τd) Θ ->
    a_def_chain Θ τd τe ->
    a_def_chain Θ (ptyp_var_f X) τe.

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

Lemma ad_ppre_flexdef_target_unfold : forall Θ Δ Ψ S ψ,
  a_wf_aenv Θ ->
  delta_def_fresh Δ Θ ->
  Θ ⨟ Δ ⊢ S ⊑ᵖ[ Ψ ] ψ ->
  forall X τd, ψ = uskl_var_f X ->
  binds X (abind_flex_mono_def τd) Θ ->
  Θ ⨟ Δ ⊢ S ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τd).
Proof.
  intros Θ Δ Ψ S ψ HwfΘ Hdf H; induction H; intros X0 τd Heq Hbd;
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

Lemma ad_refine_flexdef_target_unfold : forall Θ Δr L Q,
  a_wf_aenv Θ ->
  Θ ⨟ Δr ⊢ᵣᵃ L ⊳ Q ->
  forall X τd, Q = bskl_var_f X ->
  binds X (abind_flex_mono_def τd) Θ ->
  Θ ⨟ Δr ⊢ᵣᵃ L ⊳ (ptyp_to_bskl_syn τd).
Proof.
  intros Θ Δr L Q HwfΘ H; induction H; intros X0 τd Heq Hbd;
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
  forall Δ Ψ S,
  delta_def_fresh Δ Θ ->
  Θ ⨟ Δ ⊢ S ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τ) ->
  Θ ⨟ Δ ⊢ S ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τe).
Proof.
  intros Θ τ τe Hc; induction Hc; intros HwfΘ Δ Ψ S Hdf Hpre; auto.
  apply IHHc; auto.
  eapply ad_ppre_flexdef_target_unfold;
    [ exact HwfΘ | exact Hdf | exact Hpre | reflexivity | exact H ].
Qed.

Lemma ad_ppre_chain_fold : forall Θ τ τe,
  a_def_chain Θ τ τe ->
  forall Δ Ψ S,
  Θ ⨟ Δ ⊢ S ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τe) ->
  Θ ⨟ Δ ⊢ S ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τ).
Proof.
  intros Θ τ τe Hc; induction Hc; intros Δ Ψ S Hpre; auto.
  simpl. eapply ad_ppre__flex_r; eauto.
Qed.

Lemma ad_refine_chain_unfold : forall Θ τ τe,
  a_def_chain Θ τ τe ->
  a_wf_aenv Θ ->
  forall Δr L,
  Θ ⨟ Δr ⊢ᵣᵃ L ⊳ (ptyp_to_bskl_syn τ) ->
  Θ ⨟ Δr ⊢ᵣᵃ L ⊳ (ptyp_to_bskl_syn τe).
Proof.
  intros Θ τ τe Hc; induction Hc; intros HwfΘ Δr L Href; auto.
  apply IHHc; auto.
  eapply ad_refine_flexdef_target_unfold;
    [ exact HwfΘ | exact Href | reflexivity | exact H ].
Qed.

(* ===================================================================== *)
(*  Phase 2: chain-based shape inversions.  A subject shape meets a mono  *)
(*  paint target only after the target's defined-flex chain is unfolded;  *)
(*  each inversion returns the chain together with the residual premise.  *)
(* ===================================================================== *)

Lemma ad_ppre_unit_subject_chain_inv : forall Θ Δ Ψ S ψ,
  a_wf_aenv Θ ->
  Θ ⨟ Δ ⊢ S ⊑ᵖ[ Ψ ] ψ ->
  S = pskl_unit ->
  forall τ, ψ = ptyp_to_uskl_syn τ -> mono_ptyp τ ->
  a_def_chain Θ τ ptyp_unit /\ Ψ [=] empty.
Proof.
  intros Θ Δ Ψ S ψ HwfΘ H; induction H; intros HeqS τu Hequ Hmu;
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

Lemma ad_ppre_arrow_subject_chain_inv : forall Θ Δ Ψ S ψ,
  a_wf_aenv Θ ->
  Θ ⨟ Δ ⊢ S ⊑ᵖ[ Ψ ] ψ ->
  forall S1 S2, S = pskl_arrow S1 S2 ->
  forall τ, ψ = ptyp_to_uskl_syn τ -> mono_ptyp τ ->
  exists τ1 τ2 Ψ1 Ψ2,
    a_def_chain Θ τ (ptyp_arrow τ1 τ2) /\
    mono_ptyp τ1 /\ mono_ptyp τ2 /\
    Θ ⨟ Δ ⊢ S1 ⊑ᵖ[ Ψ1 ] (ptyp_to_uskl_syn τ1) /\
    Θ ⨟ Δ ⊢ S2 ⊑ᵖ[ Ψ2 ] (ptyp_to_uskl_syn τ2) /\
    Ψ [=] Ψ1 `union` Ψ2.
Proof.
  intros Θ Δ Ψ S ψ HwfΘ H; induction H; intros S1' S2' HeqS τu Hequ Hmu;
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

Lemma ad_ppre_tophole_subject_chain_inv : forall Θ Δ Ψ S ψ,
  a_wf_aenv Θ ->
  Θ ⨟ Δ ⊢ S ⊑ᵖ[ Ψ ] ψ ->
  forall S0, S = pskl_tophole S0 ->
  forall τ, ψ = ptyp_to_uskl_syn τ -> mono_ptyp τ ->
  exists τe,
    a_def_chain Θ τ τe /\ mono_ptyp τe /\
    Θ ⨟ Δ ⊢ S0 ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τe).
Proof.
  intros Θ Δ Ψ S ψ HwfΘ H; induction H; intros S0' HeqS τu Hequ Hmu;
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

Lemma ad_ppre_allsyn_subject_mono_absurd : forall Θ Δ Ψ S ψ,
  a_wf_aenv Θ ->
  Θ ⨟ Δ ⊢ S ⊑ᵖ[ Ψ ] ψ ->
  forall S0, S = pskl_all_syn S0 ->
  forall τ, ψ = ptyp_to_uskl_syn τ -> mono_ptyp τ ->
  False.
Proof.
  intros Θ Δ Ψ S ψ HwfΘ H; induction H; intros S0' HeqS τu Hequ Hmu;
    try discriminate HeqS.
  - (* forall: target all_etag, never a mono paint *)
    eapply ptyp_to_uskl_syn_all_etag_absurd; symmetry; exact Hequ.
  - (* flex_r *)
    symmetry in Hequ. apply ptyp_to_uskl_syn_var_inv in Hequ; subst.
    eapply IHad_partial_precise;
      [ exact HwfΘ | reflexivity | reflexivity
      | eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

Lemma ad_refine_tophole_lhs_chain_inv : forall Θ Δr L Q,
  a_wf_aenv Θ ->
  Θ ⨟ Δr ⊢ᵣᵃ L ⊳ Q ->
  forall Qb, L = bskl_tophole Qb ->
  forall τ, Q = ptyp_to_bskl_syn τ -> mono_ptyp τ ->
  exists τe,
    a_def_chain Θ τ τe /\ mono_ptyp τe /\
    Θ ⨟ Δr ⊢ᵣᵃ Qb ⊳ (ptyp_to_bskl_syn τe).
Proof.
  intros Θ Δr L Q HwfΘ H; induction H; intros Qb' HeqL τu Hequ Hmu;
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

Lemma ad_refine_allinh_lhs_mono_absurd : forall Θ Δr L Q,
  a_wf_aenv Θ ->
  Θ ⨟ Δr ⊢ᵣᵃ L ⊳ Q ->
  forall Qb, L = bskl_all_inh Qb ->
  forall τ, Q = ptyp_to_bskl_syn τ -> mono_ptyp τ ->
  False.
Proof.
  intros Θ Δr L Q HwfΘ H; induction H; intros Qb' HeqL τu Hequ Hmu;
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
(*  Bridge A: a mono-paint LHS (θ-image of a flexible counterpart) is      *)
(*  precise to the target at ANY Δ — paints contain no ghosts, so no       *)
(*  Δ-sensitive rule fires.  Bridge B: an arbitrary inherited-painting     *)
(*  LHS, given the □-precision at the same target (the Pi = □ case);      *)
(*  ghost leaves reuse the □-precision, def-chain hops use Δ-def-freshness.*)
(* ===================================================================== *)

Lemma ad_refine_mono_paint_lhs_ppre : forall Θ Δr L Q,
  a_wf_aenv Θ ->
  Δr [=] empty ->
  Θ ⨟ Δr ⊢ᵣᵃ L ⊳ Q ->
  forall τb τ, L = ptyp_to_bskl_syn τb -> Q = ptyp_to_bskl_syn τ ->
  mono_ptyp τb -> mono_ptyp τ ->
  forall Δ, Θ ⨟ Δ ⊢ (ptyp_to_pskl τb) ⊑ᵖ[ empty ] (ptyp_to_uskl_syn τ).
Proof.
  intros Θ Δr L Q HwfΘ HΔr H; induction H;
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

Lemma ad_refine_inh_hole_ppre : forall Θ Δr L Q,
  a_wf_aenv Θ ->
  Δr [=] empty ->
  Θ ⨟ Δr ⊢ᵣᵃ L ⊳ Q ->
  forall P' τ, L = pskl_to_bskl_inh P' -> Q = ptyp_to_bskl_syn τ ->
  mono_ptyp τ ->
  forall Δ Ψ, delta_def_fresh Δ Θ ->
  Θ ⨟ Δ ⊢ pskl_hole ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τ) ->
  Θ ⨟ Δ ⊢ P' ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τ).
Proof.
  intros Θ Δr L Q HwfΘ HΔr H; induction H;
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

Lemma ad_refine_syn_rigid_var_nonvar_absurd : forall Θ Δr X Q,
  a_wf_aenv Θ ->
  binds X abind_tvar Θ ->
  Θ ⨟ Δr ⊢ᵣᵃ (bskl_var_f X) ⊳ Q ->
  (forall Y, Q <> bskl_var_f Y) ->
  False.
Proof.
  intros Θ Δr X Q HwfΘ Hb H Hnv; inversion H; subst.
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
(*  (τ = X): the target is the painting of a MONO ptyp, the shape all      *)
(*  defined-flex chains stay inside.  Strong induction on                  *)
(*  size Pi + size P0 (⊤◇-stripping both sides); the target's def-chain    *)
(*  unfolding is handled by the Phase-2 chain inversions (which ride the   *)
(*  premise derivations, not the size).                                    *)
(* ===================================================================== *)

Lemma a_solve_eq_cv_mono : forall n Θ0 Θ θ Δ Ψi τ Pi P0,
  size_pskl Pi + size_pskl P0 <= n ->
  a_wf_aenv Θ -> a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ Pi -> Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  θ ∷ Θ0 ⊑ Θ ->
  mono_ptyp τ ->
  delta_def_fresh Δ Θ ->
  Θ ⨟ Δ ⊢ (msubst_pskl θ Pi) ⊑ᵖ[ Ψi ] (ptyp_to_uskl_syn τ) ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl θ P0)) ⊳ (ptyp_to_bskl_syn τ) ->
  exists Pa, Θ0 ⊢ₑ Pi ∼ P0 ⤳ Pa /\
             Θ ⨟ Δ ⊢ (msubst_pskl θ Pa) ⊑ᵖ[ Ψi ] (ptyp_to_uskl_syn τ).
Proof.
  induction n; intros Θ0 Θ θ Δ Ψi τ Pi P0 Hn
    HwfΘ HwfΘ0 HwfPi HwfP0 Hθ Hmτ Hdf Hpre Hrefine.
  { pose proof (size_pskl_min Pi); pose proof (size_pskl_min P0); lia. }
  destruct Pi as [ | nb | X | Pi1 Pi2 | Pib | | Pi' ].
  - (* Pi = unit: resolve the chain to 1, delegate to the Unit case lemma *)
    simpl in Hpre.
    destruct (ad_ppre_unit_subject_chain_inv HwfΘ Hpre eq_refl eq_refl Hmτ)
      as [Hc HΨi].
    pose proof (ad_refine_chain_unfold Hc HwfΘ Hrefine) as Href'.
    simpl in Href'.
    assert (Hpre_u : Θ ⨟ Δ ⊢ (msubst_pskl θ pskl_unit) ⊑ᵖ[ Ψi ] uskl_unit)
      by (simpl; apply ad_ppre__unit; exact HΨi).
    destruct (a_solve_eq_cv_unit (n := S n) (Θ := Θ) (Δ := Δ)
                Hn HwfΘ HwfΘ0 HwfPi HwfP0 Hθ Hpre_u Href')
      as (Pa & Hsolve & Hprec).
    exists Pa; split; [ exact Hsolve | ].
    eapply ad_ppre_chain_fold; [ exact Hc | exact Hprec ].
  - (* Pi = var_b: not wf *) inversion HwfPi.
  - (* Pi = var_f X: SE-Var / SE-FlexL *)
    exists (pskl_var_f X); split; [ apply a_solve_eq__var | exact Hpre ].
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
        assert (Hmid : msubst_pskl θ (pskl_var_f β) = pskl_var_f β)
          by (eapply msubst_pskl_tvar_id; eauto).
        rewrite Hmid in Href'. simpl in Href'.
        eapply ad_refine_syn_rigid_var_nonvar_absurd;
          [ exact HwfΘ | eapply a_inc_binds_tvar; eauto | exact Href'
          | intros Y Hcc; discriminate Hcc ].
      * (* flexible: SE-FlexR, precision via Bridge A *)
        assert (HΨi : Ψi [=] empty)
          by (eapply ad_ppre_mono_tags_empty;
                [ exact HwfΘ | exact Hpre | reflexivity | exact Hmτ ]).
        exists (pskl_var_f β); split.
        -- apply a_solve_eq__flex_r;
             [ exact Hflx
             | split; [ eapply a_wf_pskl_lc; exact HwfPi
                      | intros Hf; inversion Hf ] ].
        -- assert (Hml : mono_ptyp (msubst_lookup θ β))
             by (eapply a_inc_lookup_mono; eauto).
           simpl in Hrefine.
           eapply ad_partial_precise_psi_cong;
             [ eapply ad_refine_mono_paint_lhs_ppre with (Δr := empty);
                 [ exact HwfΘ | clear; fsetdec | exact Hrefine
                 | apply ptyp_to_bskl_inh_syn_eq; exact Hml
                 | reflexivity | exact Hml | exact Hmτ ]
             | clear - HΨi; fsetdec ].
    + (* P0 = arrow P01 P02: SE-Arrow on two IHn calls *)
      assert (HwfP01 : Θ0 ⨟ empty ⊢ₚₛᵃ P01) by (inversion HwfP0; assumption).
      assert (HwfP02 : Θ0 ⨟ empty ⊢ₚₛᵃ P02) by (inversion HwfP0; assumption).
      simpl in Href'.
      inversion Href'; subst.
      match goal with
      | Hr1 : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl θ P01) ⊳ _,
        Hr2 : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl θ P02) ⊳ _ |- _ =>
        destruct (IHn Θ0 Θ θ Δ Ψ1 τ1 Pi1 P01
                    ltac:(simpl in Hn; lia)
                    HwfΘ HwfΘ0 HwfPi1 HwfP01 Hθ Hm1 Hdf Hp1 Hr1)
          as (Pa1 & Hs1 & Hq1);
        destruct (IHn Θ0 Θ θ Δ Ψ2 τ2 Pi2 P02
                    ltac:(simpl in Hn; lia)
                    HwfΘ HwfΘ0 HwfPi2 HwfP02 Hθ Hm2 Hdf Hp2 Hr2)
          as (Pa2 & Hs2 & Hq2)
      end.
      exists (pskl_arrow Pa1 Pa2); split.
      * apply a_solve_eq__arrow; assumption.
      * eapply ad_ppre_chain_fold; [ exact Hc | ].
        simpl. eapply ad_ppre__arrow; [ exact Hq1 | exact Hq2 | exact HΨ ].
    + (* P0 = all_syn: refinement absurd *)
      simpl in Href'.
      exfalso.
      eapply ad_refine_allinh_lhs_mono_absurd;
        [ exact HwfΘ | exact Href' | reflexivity | reflexivity
        | apply mono_ptyp__arrow; assumption ].
    + (* P0 = hole: SE-VacuousR *)
      exists (pskl_arrow Pi1 Pi2); split;
        [ apply a_solve_eq__hole_r | exact Hpre ].
    + (* P0 = tophole P0': GuardedGhost-right, recurse at the resolved arrow *)
      assert (HwfP0' : Θ0 ⨟ empty ⊢ₚₛᵃ P0') by (inversion HwfP0; assumption).
      simpl in Href'.
      inversion Href'; subst.
      assert (Hpre' : Θ ⨟ Δ ⊢ msubst_pskl θ (pskl_arrow Pi1 Pi2) ⊑ᵖ[ Ψi ]
                        (ptyp_to_uskl_syn (ptyp_arrow τ1 τ2)))
        by (simpl; eapply ad_ppre__arrow;
              [ exact Hp1 | exact Hp2 | exact HΨ ]).
      match goal with
      | Hin : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl θ P0') ⊳ _ |- _ =>
        destruct (IHn Θ0 Θ θ Δ Ψi (ptyp_arrow τ1 τ2) (pskl_arrow Pi1 Pi2) P0'
                    ltac:(simpl in Hn; simpl; lia)
                    HwfΘ HwfΘ0 HwfPi HwfP0' Hθ
                    ltac:(apply mono_ptyp__arrow; assumption)
                    Hdf Hpre' Hin)
          as (Pa & Hs & Hq)
      end.
      exists Pa; split.
      * apply a_solve_eq__tophole_r_guarded;
          [ apply guarded_pskl__arrow;
              [ eapply a_wf_pskl_lc; exact HwfPi1
              | eapply a_wf_pskl_lc; exact HwfPi2 ]
          | exact Hs ].
      * eapply ad_ppre_chain_fold; [ exact Hc | exact Hq ].
  - (* Pi = all_syn: precision absurd *)
    simpl in Hpre.
    exfalso.
    eapply ad_ppre_allsyn_subject_mono_absurd;
      [ exact HwfΘ | exact Hpre | reflexivity | reflexivity | exact Hmτ ].
  - (* Pi = □: SE-GhostL, precision via Bridge B *)
    simpl in Hpre.
    exists P0; split; [ apply a_solve_eq__hole_l | ].
    eapply ad_refine_inh_hole_ppre with (Δr := empty);
      [ exact HwfΘ | clear; fsetdec | exact Hrefine | reflexivity | reflexivity
      | exact Hmτ | exact Hdf | exact Hpre ].
  - (* Pi = ⊤◇.Pi' *)
    assert (HgPi' : guarded_pskl Pi') by (inversion HwfPi; assumption).
    assert (HwfPi' : Θ0 ⨟ empty ⊢ₚₛᵃ Pi') by (inversion HwfPi; assumption).
    simpl in Hpre.
    destruct (ad_ppre_tophole_subject_chain_inv HwfΘ Hpre eq_refl eq_refl Hmτ)
      as (τe & Hc & Hme & Hp').
    pose proof (ad_refine_chain_unfold Hc HwfΘ Hrefine) as Href'.
    destruct P0 as [ | nb0 | β | P01 P02 | P0b | | P0' ].
    + (* P0 = unit: GhostGuarded *)
      destruct (IHn Θ0 Θ θ Δ Ψi τe Pi' pskl_unit
                  ltac:(simpl in Hn; simpl; lia)
                  HwfΘ HwfΘ0 HwfPi' HwfP0 Hθ Hme Hdf Hp' Href')
        as (Pa & Hs & Hq).
      exists Pa; split;
        [ apply a_solve_eq__tophole_l_guarded;
            [ apply guarded_pskl__unit | exact Hs ]
        | eapply ad_ppre_chain_fold; [ exact Hc | exact Hq ] ].
    + (* P0 = var_b: not wf *) inversion HwfP0.
    + (* P0 = var β: GhostGuarded (var is guarded) *)
      destruct (IHn Θ0 Θ θ Δ Ψi τe Pi' (pskl_var_f β)
                  ltac:(simpl in Hn; simpl; lia)
                  HwfΘ HwfΘ0 HwfPi' HwfP0 Hθ Hme Hdf Hp' Href')
        as (Pa & Hs & Hq).
      exists Pa; split;
        [ apply a_solve_eq__tophole_l_guarded;
            [ apply guarded_pskl__var | exact Hs ]
        | eapply ad_ppre_chain_fold; [ exact Hc | exact Hq ] ].
    + (* P0 = arrow: GhostGuarded *)
      assert (HwfP01 : Θ0 ⨟ empty ⊢ₚₛᵃ P01) by (inversion HwfP0; assumption).
      assert (HwfP02 : Θ0 ⨟ empty ⊢ₚₛᵃ P02) by (inversion HwfP0; assumption).
      destruct (IHn Θ0 Θ θ Δ Ψi τe Pi' (pskl_arrow P01 P02)
                  ltac:(simpl in Hn; simpl; lia)
                  HwfΘ HwfΘ0 HwfPi' HwfP0 Hθ Hme Hdf Hp' Href')
        as (Pa & Hs & Hq).
      exists Pa; split;
        [ apply a_solve_eq__tophole_l_guarded;
            [ apply guarded_pskl__arrow;
                [ eapply a_wf_pskl_lc; exact HwfP01
                | eapply a_wf_pskl_lc; exact HwfP02 ]
            | exact Hs ]
        | eapply ad_ppre_chain_fold; [ exact Hc | exact Hq ] ].
    + (* P0 = all_syn: refinement absurd *)
      simpl in Href'.
      exfalso.
      eapply ad_refine_allinh_lhs_mono_absurd;
        [ exact HwfΘ | exact Href' | reflexivity | reflexivity | exact Hme ].
    + (* P0 = hole: SE-VacuousR *)
      exists (pskl_tophole Pi'); split;
        [ apply a_solve_eq__hole_r | exact Hpre ].
    + (* P0 = ⊤◇.P0': SE-UnivGhost, second chain hop off the ⊤◇ counterpart *)
      assert (HwfP0' : Θ0 ⨟ empty ⊢ₚₛᵃ P0') by (inversion HwfP0; assumption).
      simpl in Href'.
      destruct (ad_refine_tophole_lhs_chain_inv HwfΘ Href' eq_refl eq_refl Hme)
        as (τf & Hc2 & Hmf & Hin).
      pose proof (ad_ppre_chain_unfold Hc2 HwfΘ Hdf Hp') as Hp''.
      destruct (IHn Θ0 Θ θ Δ Ψi τf Pi' P0'
                  ltac:(simpl in Hn; simpl; lia)
                  HwfΘ HwfΘ0 HwfPi' HwfP0' Hθ Hmf Hdf Hp'' Hin)
        as (Pa & Hs & Hq).
      exists (pskl_tophole Pa); split.
      * apply a_solve_eq__tophole_both; exact Hs.
      * eapply ad_ppre_chain_fold;
          [ eapply a_def_chain_trans; [ exact Hc | exact Hc2 ] | ].
        simpl. apply ad_ppre__tophole_remove. exact Hq.
Qed.

(* ==== the Var consistency case: the τ = X instance ==== *)
Lemma a_solve_eq_cv_var : forall n Θ0 Θ θ Δ Ψi X Pi P0,
  size_pskl Pi + size_pskl P0 <= n ->
  a_wf_aenv Θ -> a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ Pi -> Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  θ ∷ Θ0 ⊑ Θ ->
  delta_def_fresh Δ Θ ->
  Θ ⨟ Δ ⊢ (msubst_pskl θ Pi) ⊑ᵖ[ Ψi ] (uskl_var_f X) ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl θ P0)) ⊳ (bskl_var_f X) ->
  exists Pa, Θ0 ⊢ₑ Pi ∼ P0 ⤳ Pa /\
             Θ ⨟ Δ ⊢ (msubst_pskl θ Pa) ⊑ᵖ[ Ψi ] (uskl_var_f X).
Proof.
  intros n Θ0 Θ θ Δ Ψi X Pi P0 Hn HwfΘ HwfΘ0 HwfPi HwfP0 Hθ Hdf Hpre Hrefine.
  eapply a_solve_eq_cv_mono with (τ := ptyp_var_f X); eauto.
  auto with frost.
Qed.

(* ===================================================================== *)
(*  GhostG case kit: a dotted-ghost target [holeg] / refinement into a    *)
(*  bare [□] admit ONLY a [□] on the other side — mono paints and         *)
(*  guarded shapes have no rule into them.                                 *)
(* ===================================================================== *)

Lemma d_tags_skl_holeg_inv : forall Ψ,
  d_tags_skl Ψ uskl_holeg -> Ψ [=] empty.
Proof. intros Ψ H; inversion H; subst; auto. Qed.

Lemma ad_ppre_mono_paint_holeg_absurd : forall Θ Δ Ψ S ψ,
  a_wf_aenv Θ ->
  Θ ⨟ Δ ⊢ S ⊑ᵖ[ Ψ ] ψ ->
  ψ = uskl_holeg ->
  forall τb, S = ptyp_to_pskl τb -> mono_ptyp τb ->
  False.
Proof.
  intros Θ Δ Ψ S ψ HwfΘ H; induction H; intros Heqψ τb HeqS Hmb;
    try discriminate Heqψ.
  - (* hole: subject □ is never a paint *)
    destruct τb; simpl in HeqS; discriminate HeqS.
  - (* tophole_remove: subject ⊤◇ is never a paint *)
    destruct τb; simpl in HeqS; discriminate HeqS.
  - (* flex_l: unfold the definition, still a mono paint *)
    destruct τb; simpl in HeqS; try discriminate HeqS.
    inversion HeqS; subst.
    eapply IHad_partial_precise;
      [ exact HwfΘ | reflexivity | reflexivity
      | eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

Lemma ad_refine_mono_paint_hole_rhs_absurd : forall Θ Δr L Q,
  a_wf_aenv Θ ->
  Θ ⨟ Δr ⊢ᵣᵃ L ⊳ Q ->
  Q = bskl_hole ->
  forall τb, L = ptyp_to_bskl_syn τb -> mono_ptyp τb ->
  False.
Proof.
  intros Θ Δr L Q HwfΘ H; induction H; intros HeqQ τb HeqL Hmb;
    try discriminate HeqQ.
  - (* hole: LHS □ is never a paint *)
    destruct τb; simpl in HeqL; discriminate HeqL.
  - (* tophole_remove: LHS ⊤◇ is never a paint *)
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
   premise-absurd (a ⊤◇'s guarded body dies one level down). *)
Lemma a_solve_eq_cv_ghostg : forall Θ0 Θ θ Δ Ψi Pi P0,
  a_wf_aenv Θ -> a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ Pi -> Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  θ ∷ Θ0 ⊑ Θ ->
  Θ ⨟ Δ ⊢ (msubst_pskl θ Pi) ⊑ᵖ[ Ψi ] uskl_holeg ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl θ P0)) ⊳ bskl_hole ->
  exists Pa, Θ0 ⊢ₑ Pi ∼ P0 ⤳ Pa /\
             Θ ⨟ Δ ⊢ (msubst_pskl θ Pa) ⊑ᵖ[ Ψi ] uskl_holeg.
Proof.
  intros Θ0 Θ θ Δ Ψi Pi P0 HwfΘ HwfΘ0 HwfPi HwfP0 Hθ Hpre Hrefine.
  assert (Habs_pre_var : forall v Ψ',
            Θ ⨟ Δ ⊢ (msubst_pskl θ (pskl_var_f v)) ⊑ᵖ[ Ψ' ] uskl_holeg ->
            False).
  { intros v Ψ' Hp. simpl in Hp.
    eapply ad_ppre_mono_paint_holeg_absurd;
      [ exact HwfΘ | exact Hp | reflexivity | reflexivity
      | eapply a_inc_lookup_mono; eauto ]. }
  assert (Habs_ref_var : forall v,
            Θ ⨟ empty ⊢ᵣᵃ
              (pskl_to_bskl_inh (msubst_pskl θ (pskl_var_f v))) ⊳ bskl_hole ->
            False).
  { intros v Hr. simpl in Hr.
    assert (Hml : mono_ptyp (msubst_lookup θ v))
      by (eapply a_inc_lookup_mono; eauto).
    rewrite (ptyp_to_bskl_inh_syn_eq Hml) in Hr.
    eapply ad_refine_mono_paint_hole_rhs_absurd;
      [ exact HwfΘ | exact Hr | reflexivity | reflexivity | exact Hml ]. }
  destruct Pi as [ | nb | X | Pi1 Pi2 | Pib | | Pi' ].
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
    + (* P0 = ⊤◇.P0': strip; the guarded body dies *)
      simpl in Hrefine. inversion Hrefine; subst.
      exfalso.
      assert (HgP0' : guarded_pskl P0') by (inversion HwfP0; assumption).
      inversion HgP0'; subst.
      * (* unit *)
        match goal with
        | Hin : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl θ pskl_unit) ⊳ _
          |- _ => simpl in Hin; inversion Hin
        end.
      * (* var *)
        match goal with
        | Hin : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl θ (pskl_var_f _)) ⊳ _
          |- _ => eapply Habs_ref_var; exact Hin
        end.
      * (* arrow *)
        match goal with
        | Hin : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl θ (pskl_arrow _ _)) ⊳ _
          |- _ => simpl in Hin; inversion Hin
        end.
  - (* Pi = ⊤◇.Pi': strip; the guarded body dies *)
    simpl in Hpre. inversion Hpre; subst.
    exfalso.
    assert (HgPi' : guarded_pskl Pi') by (inversion HwfPi; assumption).
    inversion HgPi'; subst.
    + (* unit *)
      match goal with
      | Hp' : _ ⨟ _ ⊢ msubst_pskl θ pskl_unit ⊑ᵖ[ _ ] _ |- _ =>
          simpl in Hp'; inversion Hp'
      end.
    + (* var *)
      match goal with
      | Hp' : _ ⨟ _ ⊢ msubst_pskl θ (pskl_var_f _) ⊑ᵖ[ _ ] _ |- _ =>
          eapply Habs_pre_var; exact Hp'
      end.
    + (* arrow *)
      match goal with
      | Hp' : _ ⨟ _ ⊢ msubst_pskl θ (pskl_arrow _ _) ⊑ᵖ[ _ ] _ |- _ =>
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
(*  absurdities against dotted-⊤◇ targets / plain-⊤◇ refinement RHS.       *)
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

Lemma ad_ppre_mono_paint_topholeg_absurd : forall Θ Δ Ψ S ψ,
  a_wf_aenv Θ ->
  Θ ⨟ Δ ⊢ S ⊑ᵖ[ Ψ ] ψ ->
  forall ψ0, ψ = uskl_topholeg ψ0 ->
  forall τb, S = ptyp_to_pskl τb -> mono_ptyp τb ->
  False.
Proof.
  intros Θ Δ Ψ S ψ HwfΘ H; induction H; intros ψ0' Heqψ τb HeqS Hmb;
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

Lemma ad_refine_mono_paint_tophole_rhs_absurd : forall Θ Δr L Q,
  a_wf_aenv Θ ->
  Θ ⨟ Δr ⊢ᵣᵃ L ⊳ Q ->
  forall Q0, Q = bskl_tophole Q0 ->
  forall τb, L = ptyp_to_bskl_syn τb -> mono_ptyp τb ->
  False.
Proof.
  intros Θ Δr L Q HwfΘ H; induction H; intros Q0' HeqQ τb HeqL Hmb;
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

Inductive flex_apart (Θ0 : aenv) (Δρ : atoms) : pskl -> uskl -> Prop :=
| fa_clean : forall P0 ψa,
    (ftvar_in_uskl ψa) ∩ Δρ [=] empty ->
    flex_apart Θ0 Δρ P0 ψa
| fa_unit : forall ψa, flex_apart Θ0 Δρ pskl_unit ψa
| fa_var_rigid : forall X ψa,
    binds X abind_tvar Θ0 ->
    flex_apart Θ0 Δρ (pskl_var_f X) ψa
| fa_hole : forall ψa, flex_apart Θ0 Δρ pskl_hole ψa
| fa_tophole : forall P0 ψa,
    flex_apart Θ0 Δρ P0 ψa ->
    flex_apart Θ0 Δρ (pskl_tophole P0) ψa
| fa_topholeg_t : forall P0 ψa,
    flex_apart Θ0 Δρ P0 ψa ->
    flex_apart Θ0 Δρ P0 (uskl_topholeg ψa)
| fa_arrow : forall P1 P2 ψ1 ψ2,
    flex_apart Θ0 Δρ P1 ψ1 ->
    flex_apart Θ0 Δρ P2 ψ2 ->
    flex_apart Θ0 Δρ (pskl_arrow P1 P2) (uskl_arrow ψ1 ψ2)
| fa_all_etag : forall L ε P0 ψ,
    (forall X, X `notin` L ->
       flex_apart Θ0 Δρ (open_pskl_wrt_pskl P0 (pskl_var_f X))
                        (open_uskl_wrt_uskl ψ (uskl_var_f X))) ->
    flex_apart Θ0 Δρ (pskl_all_syn P0) (uskl_all_etag ε ψ)
| fa_all_syn : forall L P0 ψ,
    (forall X, X `notin` L ->
       flex_apart Θ0 Δρ (open_pskl_wrt_pskl P0 (pskl_var_f X))
                        (open_uskl_wrt_uskl ψ (uskl_var_f X))) ->
    flex_apart Θ0 Δρ (pskl_all_syn P0) (uskl_all_syn ψ).

(* Inversions used by the ⊤◇/⊤̇◇ congruence cases. *)
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
  - inversion Heqt; subst; assumption.
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
  - apply fa_topholeg_t; auto.
Qed.

(* ===================================================================== *)
(*  Arrow-case flex-subcase discharge (Phase B).                           *)
(*  (B1) On a Δρ-clean target the ρ-relation degenerates to equality;      *)
(*  (B2) a mono paint that refines the consistency counterpart is precise  *)
(*  against the (tag-sorted) consistency subject.                          *)
(* ===================================================================== *)

Lemma uskl_rho_clean_eq : forall NM Θ Δρ Ψρ S R,
  uskl_rho NM Θ Δρ Ψρ S R ->
  (ftvar_in_uskl R) ∩ Δρ [=] empty ->
  S = R /\ Ψρ [=] empty.
Proof.
  intros NM Θ Δρ Ψρ S R H; induction H; intros Hclean.
  - split; [ reflexivity | assumption ].
  - (* leaf: the target variable is IN Δρ — contradiction with cleanliness *)
    exfalso. simpl in Hclean.
    match goal with HX : X `in` Δρ |- _ => clear - HX Hclean; fsetdec end.
  - (* arrow *)
    simpl in Hclean.
    destruct IHuskl_rho1 as [-> HΨ1]; [ clear - Hclean; fsetdec | ].
    destruct IHuskl_rho2 as [-> HΨ2]; [ clear - Hclean; fsetdec | ].
    split; [ reflexivity | ].
    match goal with HΨ : Ψρ [=] union _ _ |- _ =>
      clear - HΨ HΨ1 HΨ2; fsetdec end.
  - (* all_syn *)
    simpl in Hclean.
    pick fresh X for
      (L `union` Δρ `union` ftvar_in_uskl S `union` ftvar_in_uskl R).
    destruct (H0 X ltac:(fsetdec)) as [Heq HΨ].
    { pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R (uskl_var_f X)).
      simpl in *. clear - Hclean H1 Fr. fsetdec. }
    split; [ | exact HΨ ].
    f_equal.
    apply open_uskl_wrt_uskl_inj with (α1 := X);
      [ clear - Fr; fsetdec | clear - Fr; fsetdec | exact Heq ].
  - (* all_etag *)
    simpl in Hclean.
    pick fresh X for
      (L `union` Δρ `union` ftvar_in_uskl S `union` ftvar_in_uskl R).
    destruct (H0 X ltac:(fsetdec)) as [Heq HΨ].
    { pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R (uskl_var_f X)).
      simpl in *. clear - Hclean H1 Fr. fsetdec. }
    split; [ | exact HΨ ].
    f_equal.
    apply open_uskl_wrt_uskl_inj with (α1 := X);
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
Lemma ad_refine_mono_paint_allinh_rhs_absurd : forall Θ Δr L Q,
  a_wf_aenv Θ ->
  Θ ⨟ Δr ⊢ᵣᵃ L ⊳ Q ->
  forall Q0, Q = bskl_all_inh Q0 ->
  forall τb, L = ptyp_to_bskl_syn τb -> mono_ptyp τb ->
  False.
Proof.
  intros Θ Δr L Q HwfΘ H; induction H; intros Q0' HeqQ τb HeqL Hmb;
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

Lemma ad_refine_mono_paint_allsyn_rhs_absurd : forall Θ Δr L Q,
  a_wf_aenv Θ ->
  Θ ⨟ Δr ⊢ᵣᵃ L ⊳ Q ->
  forall Q0, Q = bskl_all_syn Q0 ->
  forall τb, L = ptyp_to_bskl_syn τb -> mono_ptyp τb ->
  False.
Proof.
  intros Θ Δr L Q HwfΘ H; induction H; intros Q0' HeqQ τb HeqL Hmb;
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
| bmi_var : forall X, bskl_monoish (bskl_var_f X)
| bmi_arrow : forall Q1 Q2,
    bskl_monoish Q1 -> bskl_monoish Q2 ->
    bskl_monoish (bskl_arrow Q1 Q2).

Lemma bskl_monoish_paint : forall τ,
  mono_ptyp τ -> bskl_monoish (ptyp_to_bskl_syn τ).
Proof. intros τ Hm; induction Hm; simpl; constructor; auto. Qed.

Lemma ad_refine_mono_paint_rhs_monoish : forall Θ Δr L Q,
  a_wf_aenv Θ ->
  Θ ⨟ Δr ⊢ᵣᵃ L ⊳ Q ->
  forall τb, L = ptyp_to_bskl_syn τb -> mono_ptyp τb ->
  bskl_monoish Q.
Proof.
  intros Θ Δr L Q HwfΘ H; induction H; intros τb HeqL Hmb.
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
    split; [ assumption | exists (ptyp_var_f X); split;
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
Lemma ppre_paint_arrow_chase : forall Θ Δr L Q,
  a_wf_aenv Θ ->
  Θ ⨟ Δr ⊢ᵣᵃ L ⊳ Q ->
  forall Q1 Q2 (ψ1 ψ2 : uskl),
  Q = bskl_arrow Q1 Q2 ->
  (forall Δr' τ1, Δr' [=] empty -> mono_ptyp τ1 ->
     Θ ⨟ Δr' ⊢ᵣᵃ (ptyp_to_bskl_syn τ1) ⊳ Q1 ->
     forall Δ, Θ ⨟ Δ ⊢ (ptyp_to_pskl τ1) ⊑ᵖ[ empty ] ψ1) ->
  (forall Δr' τ2, Δr' [=] empty -> mono_ptyp τ2 ->
     Θ ⨟ Δr' ⊢ᵣᵃ (ptyp_to_bskl_syn τ2) ⊳ Q2 ->
     forall Δ, Θ ⨟ Δ ⊢ (ptyp_to_pskl τ2) ⊑ᵖ[ empty ] ψ2) ->
  forall τb, L = ptyp_to_bskl_syn τb -> mono_ptyp τb ->
  Δr [=] empty ->
  forall Δ, Θ ⨟ Δ ⊢ (ptyp_to_pskl τb) ⊑ᵖ[ empty ] (uskl_arrow ψ1 ψ2).
Proof.
  intros Θ Δr L Q HwfΘ H;
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

Lemma ppre_paint_flexvar_chase : forall Θ Δr L Q,
  a_wf_aenv Θ ->
  Θ ⨟ Δr ⊢ᵣᵃ L ⊳ Q ->
  forall γ τγ (ψa : uskl),
  Q = bskl_var_f γ ->
  binds γ (abind_flex_mono_def τγ) Θ ->
  (forall Δr' τc, Δr' [=] empty -> mono_ptyp τc ->
     Θ ⨟ Δr' ⊢ᵣᵃ (ptyp_to_bskl_syn τc) ⊳ (ptyp_to_bskl_syn τγ) ->
     forall Δ, Θ ⨟ Δ ⊢ (ptyp_to_pskl τc) ⊑ᵖ[ empty ] ψa) ->
  forall τb, L = ptyp_to_bskl_syn τb -> mono_ptyp τb ->
  Δr [=] empty ->
  forall Δ, Θ ⨟ Δ ⊢ (ptyp_to_pskl τb) ⊑ᵖ[ empty ] ψa.
Proof.
  intros Θ Δr L Q HwfΘ H;
    induction H; intros γ τγ ψa HeqQ Hbγ CONT τb HeqL Hmb HΔr Δo;
    try discriminate HeqQ.
  - (* var: the counterpart variable itself *)
    inversion HeqQ; subst.
    symmetry in HeqL; apply ptyp_to_bskl_syn_var_inv in HeqL; subst.
    assert (Hmγ : mono_ptyp τγ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact HwfΘ | exact Hbγ ]).
    assert (Hwfγ : a_wf_ptyp Θ τγ)
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
Lemma mono_paint_paint_refine_consis_ppre : forall Ψs Θ S Q,
  Ψs ⨟ Θ ⊢ₛᵃ S ∼ Q ->
  a_wf_aenv Θ ->
  forall τa, S = ptyp_to_uskl_syn τa -> mono_ptyp τa ->
  forall Δr τb, Δr [=] empty -> mono_ptyp τb ->
  Θ ⨟ Δr ⊢ᵣᵃ (ptyp_to_bskl_syn τb) ⊳ Q ->
  forall Δ, Θ ⨟ Δ ⊢ (ptyp_to_pskl τb) ⊑ᵖ[ empty ] (ptyp_to_uskl_syn τa).
Proof.
  intros Ψs Θ S Q H; induction H;
    intros HwfΘ τa HeqS Hma Δr τb HΔr Hmb Hrefine Δo.
  - (* unit *)
    symmetry in HeqS; apply ptyp_to_uskl_syn_unit_inv in HeqS; subst.
    eapply ad_refine_mono_paint_lhs_ppre with (τ := ptyp_unit);
      [ exact HwfΘ | exact HΔr | exact Hrefine | reflexivity | reflexivity
      | exact Hmb | apply mono_ptyp__unit ].
  - (* var *)
    symmetry in HeqS; apply ptyp_to_uskl_syn_var_inv in HeqS; subst.
    eapply ad_refine_mono_paint_lhs_ppre with (τ := ptyp_var_f X);
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

Lemma ad_refine_arrow_arrow_inv : forall Θ Δr L1 L2 Q1 Q2,
  Θ ⨟ Δr ⊢ᵣᵃ (bskl_arrow L1 L2) ⊳ (bskl_arrow Q1 Q2) ->
  (Θ ⨟ Δr ⊢ᵣᵃ L1 ⊳ Q1) /\ (Θ ⨟ Δr ⊢ᵣᵃ L2 ⊳ Q2).
Proof.
  intros Θ Δr L1 L2 Q1 Q2 H; inversion H; subst; split; assumption.
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
      [ intros X HX; apply (H0 X HX); clear - Heq; fsetdec | assumption ].
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
  forall S,
  S ∩ ftvar_in_uskl ψ [=] empty ->
  delta_def_fresh S Θ ->
  Θ ⨟ (Δ `union` S) ⊢ P ⊑ᵖ[ Ψ ] ψ.
Proof.
  intros Θ Δ Ψ P ψ H; induction H; intros S HS Hdf.
  - apply ad_ppre__unit; assumption.
  - apply ad_ppre__var; [ assumption | ].
    match goal with Hor : _ \/ a_binds_tvar _ _ |- _ =>
      destruct Hor as [HΔ | Hb];
      [ left; clear - HΔ; fsetdec | right; assumption ] end.
  - simpl in HS.
    eapply ad_ppre__arrow;
      [ apply IHad_partial_precise1; [ clear - HS; fsetdec | exact Hdf ]
      | apply IHad_partial_precise2; [ clear - HS; fsetdec | exact Hdf ]
      | assumption ].
  - (* forall *)
    simpl in HS.
    eapply ad_ppre__forall with (L := L `union` S); [ | eassumption ].
    intros X HX.
    assert (HSX : S ∩
              (ftvar_in_uskl (open_uskl_wrt_uskl ψ (uskl_var_f X)))
              [=] empty).
    { pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ (uskl_var_f X))
        as Hup.
      simpl in Hup. clear - HS HX Hup. fsetdec. }
    eapply ad_partial_precise_delta_cong;
      [ apply (H0 X ltac:(clear - HX; fsetdec) S HSX Hdf)
      | clear; fsetdec ].
  - (* hole *)
    apply ad_ppre__hole; [ assumption | ].
    match goal with Hint : _ ∩ _ [=] empty |- _ =>
      clear - Hint HS; fsetdec end.
  - apply ad_ppre__tophole_remove; auto.
  - (* tophole_fill *)
    eapply ad_ppre__tophole_fill with (L := L `union` S).
    intros X HX.
    assert (HSX : S ∩
              (ftvar_in_uskl (open_uskl_wrt_uskl ψ (uskl_var_f X)))
              [=] empty).
    { pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ (uskl_var_f X))
        as Hup.
      simpl in Hup. clear - HS HX Hup. fsetdec. }
    assert (Hdf' : delta_def_fresh S ((X ~ abind_tvar) ++ Θ)).
    { intros Y α τ HY Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
        [ discriminate Hc | exact (Hdf Y α τ HY Hb') ]. }
    apply (H0 X ltac:(clear - HX; fsetdec) S HSX Hdf').
  - (* tophole_keep *)
    simpl in HS.
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
Lemma ad_refine_syn_delta_to_tvar_mid : forall Θfull Δr L Q,
  Θfull ⨟ Δr ⊢ᵣᵃ L ⊳ Q ->
  forall Z Θ1 Θ0 Δr', Θfull = Θ1 ++ Θ0 ->
  Δr [<=] add Z Δr' ->
  (Θ1 ++ (Z ~ abind_tvar) ++ Θ0) ⨟ Δr' ⊢ᵣᵃ L ⊳ Q.
Proof.
  intros Θfull Δr L Q H; induction H;
    intros Z Θ1 Θt Δr' HeqΘ Hsub; subst.
  - apply ad_refine_syn__unit.
  - (* var *)
    apply ad_refine_syn__var.
    match goal with Hor : _ \/ a_binds_tvar ?X _ |- _ =>
      destruct Hor as [HΔ | Hbt];
      [ destruct (X == Z) as [-> | Hne];
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
    intros X HX.
    apply (H0 X HX Z Θ1 Θt (add X Δr') eq_refl).
    clear - Hsub; fsetdec.
  - (* hole *)
    apply ad_refine_syn__hole.
    eapply a_wf_pskl_weaken;
      [ intros x b Hb; apply binds_weaken; exact Hb | eassumption ].
  - apply ad_refine_syn__tophole_remove; auto.
  - (* tophole_fill: the aenv grows on the left *)
    apply ad_refine_syn__tophole_fill with (L := L).
    intros X HX.
    apply (H0 X HX Z ((X ~ abind_tvar) ++ Θ1) Θt Δr' eq_refl Hsub).
  - apply ad_refine_syn__tophole_keep; auto.
  - eapply ad_refine_syn__flex_l;
      [ apply binds_weaken; eassumption | auto ].
  - eapply ad_refine_syn__flex_r;
      [ apply binds_weaken; eassumption | auto ].
Qed.

Lemma ad_refine_syn_delta_to_tvar : forall Θ Δr L Q Z Δr',
  Θ ⨟ Δr ⊢ᵣᵃ L ⊳ Q ->
  Δr [<=] add Z Δr' ->
  ((Z ~ abind_tvar) ++ Θ) ⨟ Δr' ⊢ᵣᵃ L ⊳ Q.
Proof.
  intros Θ Δr L Q Z Δr' H Hsub.
  exact (@ad_refine_syn_delta_to_tvar_mid _ _ _ _ H Z nil Θ Δr'
           eq_refl Hsub).
Qed.

(** Free variables of a consistency SUBJECT are counterpart variables or
    Θ's defined flexibles / their definition images.  (The tight bound —
    rigid tvar entries never pollute it — which is what survives the
    ∀-descent's context extensions.) *)
Lemma ad_pat_consis_ftv_bound : forall Ψ Θ S Q,
  Ψ ⨟ Θ ⊢ₛᵃ S ∼ Q ->
  forall X, X `in` ftvar_in_uskl S ->
  X `in` ftvar_in_bskl Q \/
  (exists α τ, binds α (abind_flex_mono_def τ) Θ /\
     (X = α \/ X `in` ftvar_in_ptyp τ)).
Proof.
  intros Ψ Θ S Q H; induction H; intros X0 HX0; simpl in HX0.
  - (* unit *) exfalso; clear - HX0; fsetdec.
  - (* var *) left; simpl; clear - HX0; fsetdec.
  - (* arrow *)
    apply union_iff in HX0; destruct HX0 as [HX0 | HX0];
      [ destruct (IHad_pat_consis1 X0 HX0) as [Hin | Hdef]
      | destruct (IHad_pat_consis2 X0 HX0) as [Hin | Hdef] ];
      solve [ left; simpl; clear - Hin; fsetdec | right; exact Hdef ].
  - (* forall_inh_tagged *)
    pick fresh Y for
      (L `union` singleton X0 `union` ftvar_in_bskl Q).
    assert (HX0' : X0 `in`
              ftvar_in_uskl (open_uskl_wrt_uskl R (uskl_var_f Y)))
      by (pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R
                        (uskl_var_f Y)) as Hlow; clear - HX0 Hlow; fsetdec).
    destruct (H0 Y ltac:(clear - Fr; fsetdec) X0 HX0')
      as [Hin | (α & τ & Hb & Hor)].
    + left.
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q
                    (bskl_var_f Y)) as Hup.
      simpl in *. clear - Hin Hup Fr. fsetdec.
    + destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
        [ discriminate Hc | right; exists α, τ; auto ].
  - (* forall_inh_untagged *)
    pick fresh Y for
      (L `union` singleton X0 `union` ftvar_in_bskl Q).
    assert (HX0' : X0 `in`
              ftvar_in_uskl (open_uskl_wrt_uskl R (uskl_var_f Y)))
      by (pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R
                        (uskl_var_f Y)) as Hlow; clear - HX0 Hlow; fsetdec).
    destruct (H0 Y ltac:(clear - Fr; fsetdec) X0 HX0')
      as [Hin | (α & τ & Hb & Hor)].
    + left.
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q
                    (bskl_var_f Y)) as Hup.
      simpl in *. clear - Hin Hup Fr. fsetdec.
    + destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
        [ discriminate Hc | right; exists α, τ; auto ].
  - (* forall_syn_tagged *)
    pick fresh Y for
      (L `union` singleton X0 `union` ftvar_in_bskl Q).
    assert (HX0' : X0 `in`
              ftvar_in_uskl (open_uskl_wrt_uskl R (uskl_var_f Y)))
      by (pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R
                        (uskl_var_f Y)) as Hlow; clear - HX0 Hlow; fsetdec).
    destruct (H0 Y ltac:(clear - Fr; fsetdec) X0 HX0')
      as [Hin | (α & τ & Hb & Hor)].
    + left.
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q
                    (bskl_var_f Y)) as Hup.
      simpl in *. clear - Hin Hup Fr. fsetdec.
    + destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
        [ discriminate Hc | right; exists α, τ; auto ].
  - (* forall_syn *)
    pick fresh Y for
      (L `union` singleton X0 `union` ftvar_in_bskl Q).
    assert (HX0' : X0 `in`
              ftvar_in_uskl (open_uskl_wrt_uskl R (uskl_var_f Y)))
      by (pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R
                        (uskl_var_f Y)) as Hlow; clear - HX0 Hlow; fsetdec).
    destruct (H0 Y ltac:(clear - Fr; fsetdec) X0 HX0')
      as [Hin | (α & τ & Hb & Hor)].
    + left.
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q
                    (bskl_var_f Y)) as Hup.
      simpl in *. clear - Hin Hup Fr. fsetdec.
    + destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
        [ discriminate Hc | right; exists α, τ; auto ].
  - (* ghostg *) exfalso; clear - HX0; fsetdec.
  - (* topholeg *)
    destruct (IHad_pat_consis X0 HX0) as [Hin | Hdef];
      [ left; simpl; clear - Hin; fsetdec | right; exact Hdef ].
  - (* hole *) exfalso; clear - HX0; fsetdec.
  - (* tophole *)
    destruct (IHad_pat_consis X0 HX0) as [Hin | Hdef];
      [ left; simpl; clear - Hin; fsetdec | right; exact Hdef ].
  - (* tophole_inh: subject fixed under the counterpart binder *)
    pick fresh Y for
      (L `union` singleton X0 `union` ftvar_in_bskl Q).
    destruct (H0 Y ltac:(clear - Fr; fsetdec) X0 ltac:(simpl; exact HX0))
      as [Hin | (α & τ & Hb & Hor)].
    + left.
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q
                    (bskl_var_f Y)) as Hup.
      simpl in *. clear - Hin Hup Fr. fsetdec.
    + destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
        [ discriminate Hc | right; exists α, τ; auto ].
  - (* tophole_drop *)
    destruct (IHad_pat_consis X0 HX0) as [Hin | Hdef];
      [ left; exact Hin | right; exact Hdef ].
  - (* flex_l: the subject variable is itself a defined flexible *)
    right; exists α, τ; split; [ assumption | left; clear - HX0; fsetdec ].
  - (* flex_r: unfolding the counterpart definition *)
    destruct (IHad_pat_consis X0 HX0) as [Hin | Hdef];
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
Lemma uskl_rho_ftv_target_bound : forall NM Θ Δρ Ψρ S R,
  uskl_rho NM Θ Δρ Ψρ S R ->
  ftvar_in_uskl R [<=] ftvar_in_uskl S `union` Δρ.
Proof.
  intros NM Θ Δρ Ψρ S R H; induction H; simpl; try fsetdec.
  - (* all_syn *)
    pick fresh X for
      (L `union` ftvar_in_uskl S `union` ftvar_in_uskl R).
    pose proof (H0 X ltac:(clear - Fr; fsetdec)) as HX.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f X)).
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper S (uskl_var_f X)).
    simpl in *. clear - HX H1 H2 Fr. fsetdec.
  - (* all_etag *)
    pick fresh X for
      (L `union` ftvar_in_uskl S `union` ftvar_in_uskl R).
    pose proof (H0 X ltac:(clear - Fr; fsetdec)) as HX.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f X)).
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper S (uskl_var_f X)).
    simpl in *. clear - HX H1 H2 Fr. fsetdec.
Qed.

(** Cofinite inversions of the tag-sorting components at a tagged ∀. *)
Lemma is_tskl_all_etag_inv : forall ε ψ,
  is_tskl (uskl_all_etag ε ψ) ->
  exists L, forall X, X `notin` L ->
    is_tskl (open_uskl_wrt_uskl ψ (uskl_var_f X)).
Proof. intros ε ψ H; inversion H; subst. eexists; eassumption. Qed.

Lemma uskl_ghost_free_all_etag_inv : forall ε ψ,
  uskl_ghost_free (uskl_all_etag ε ψ) ->
  exists L, forall X, X `notin` L ->
    uskl_ghost_free (open_uskl_wrt_uskl ψ (uskl_var_f X)).
Proof. intros ε ψ H; inversion H; subst. eexists; eassumption. Qed.

(** [a_tags_sort] inversion at a tagged ∀ (all components cofinite). *)
Lemma a_tags_sort_all_etag_inv : forall NM Ψ ε ψ,
  a_tags_sort NM Ψ (uskl_all_etag ε ψ) ->
  exists L Ψ0,
    (forall X, X `notin` L ->
       a_tags_sort NM Ψ0 (open_uskl_wrt_uskl ψ (uskl_var_f X))) /\
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
    intros X HX; apply a_tags_sort__sk;
      [ apply Hti; clear - HX; fsetdec
      | apply Hd0; clear - HX; fsetdec ].
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
    intros X HX; apply a_tags_sort__ty;
      [ apply Hti; clear - HX; fsetdec
      | apply Hd0; clear - HX; fsetdec
      | apply Hgf; clear - HX; fsetdec ].
Qed.

(** [flex_apart] aenv weakening (binds-monotone). *)
Lemma flex_apart_weaken : forall Θ0 Δρ P ψ,
  flex_apart Θ0 Δρ P ψ ->
  forall Θ0', (forall x b, binds x b Θ0 -> binds x b Θ0') ->
  flex_apart Θ0' Δρ P ψ.
Proof.
  intros Θ0 Δρ P ψ H; induction H; intros Θ0' Hmon.
  - apply fa_clean; assumption.
  - apply fa_unit.
  - apply fa_var_rigid; auto.
  - apply fa_hole.
  - apply fa_tophole; auto.
  - apply fa_topholeg_t; auto.
  - apply fa_arrow; auto.
  - eapply fa_all_etag with (L := L); eauto.
  - eapply fa_all_syn with (L := L); eauto.
Qed.

(** [flex_apart] binder descent at a tagged-∀ target with a ∀-source. *)
Lemma flex_apart_all_etag_forall_inv : forall Θ0 Δρ ε P0 ψ,
  flex_apart Θ0 Δρ (pskl_all_syn P0) (uskl_all_etag ε ψ) ->
  exists L, forall X, X `notin` L ->
    flex_apart Θ0 Δρ (open_pskl_wrt_pskl P0 (pskl_var_f X))
                     (open_uskl_wrt_uskl ψ (uskl_var_f X)).
Proof.
  intros Θ0 Δρ ε P0 ψ H; inversion H; subst.
  - (* fa_clean: bodies stay clean at fresh openings *)
    match goal with Hc : _ ∩ _ [=] empty |- _ =>
      exists Δρ; intros X HX; apply fa_clean;
      pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ
                    (uskl_var_f X)) as Hup;
      simpl in *; clear - Hc Hup HX; fsetdec
    end.
  - (* fa_all_etag: the cofinite family, directly *)
    match goal with
    | Hf : forall X, X `notin` ?L0 -> flex_apart _ _ _ _ |- _ =>
      exists L0; exact Hf
    end.
Qed.


(** Absorb Δr-entries that are rigid tvars of the aenv (the Δr-refinement
    → statement-form transfer, given Δr ⊆ dom Θtv and Θ ⊇ Θtv). *)
Lemma ad_refine_syn_delta_absorb : forall Θ Δr L Q,
  Θ ⨟ Δr ⊢ᵣᵃ L ⊳ Q ->
  forall Δr', (forall Z, Z `in` Δr -> Z `in` Δr' \/ binds Z abind_tvar Θ) ->
  Θ ⨟ Δr' ⊢ᵣᵃ L ⊳ Q.
Proof.
  intros Θ Δr L Q H; induction H; intros Δr' Habs.
  - apply ad_refine_syn__unit.
  - apply ad_refine_syn__var.
    match goal with Hor : _ \/ a_binds_tvar ?X _ |- _ =>
      destruct Hor as [HΔ | Hbt];
      [ destruct (Habs _ HΔ) as [HΔ' | Hb];
        [ left; exact HΔ' | right; left; exact Hb ]
      | right; exact Hbt ] end.
  - apply ad_refine_syn__arrow; auto.
  - apply ad_refine_syn__all with (L := L).
    intros X HX. apply (H0 X HX (add X Δr')).
    intros Z HZ.
    destruct (AtomSetProperties.In_dec Z (add X Δr')) as [Hin | Hnin];
      [ left; exact Hin | ].
    destruct (Habs Z ltac:(clear - HZ Hnin; fsetdec)) as [HΔ' | Hb];
      [ left; clear - HΔ' Hnin; fsetdec | right; exact Hb ].
  - apply ad_refine_syn__hole; assumption.
  - apply ad_refine_syn__tophole_remove; auto.
  - apply ad_refine_syn__tophole_fill with (L := L).
    intros X HX. apply (H0 X HX Δr').
    intros Z HZ.
    destruct (Habs Z HZ) as [HΔ' | Hb];
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

Lemma pskl_no_hole_open_rec : forall P V k,
  pskl_no_hole P -> pskl_no_hole V ->
  pskl_no_hole (open_pskl_wrt_pskl_rec k V P).
Proof.
  induction P; intros V k HP HV; simpl in *; auto.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; auto.
  - destruct HP; split; auto.
Qed.

Lemma pskl_no_hole_open : forall P X,
  pskl_no_hole P ->
  pskl_no_hole (open_pskl_wrt_pskl P (pskl_var_f X)).
Proof.
  intros P X HP. apply pskl_no_hole_open_rec; simpl; auto.
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
    intros X HX.
    apply (H0 X HX); [ apply pskl_no_hole_open; exact Hnh | ].
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
Lemma ad_refine_syn_ftv_rhs_bound : forall Θ Δr Lh Q,
  a_wf_aenv Θ ->
  Θ ⨟ Δr ⊢ᵣᵃ Lh ⊳ Q ->
  ftvar_in_bskl Q [<=] ftvar_in_bskl Lh `union` dom Θ.
Proof.
  intros Θ Δr Lh Q HwfΘ H; induction H; simpl; try (clear; fsetdec).
  - (* arrow *)
    clear - IHad_refine_syn1 IHad_refine_syn2 HwfΘ.
    specialize (IHad_refine_syn1 HwfΘ).
    specialize (IHad_refine_syn2 HwfΘ).
    fsetdec.
  - (* all *)
    pick fresh X for
      (L `union` ftvar_in_bskl Q `union` ftvar_in_bskl P
         `union` dom Θ).
    pose proof (H0 X ltac:(clear - Fr; fsetdec) HwfΘ) as HX.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_lower P (bskl_var_f X))
      as Hlow.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f X))
      as Hup.
    simpl in *. clear - HX Hlow Hup Fr. fsetdec.
  - (* hole: the fill is wf at empty Δ *)
    pose proof (a_wf_pskl_ftv_dom H) as Hd.
    rewrite ftvar_pskl_to_bskl_syn.
    clear - Hd; fsetdec.
  - (* tophole_remove *)
    specialize (IHad_refine_syn HwfΘ). clear - IHad_refine_syn; fsetdec.
  - (* tophole_fill *)
    pick fresh X for
      (L `union` ftvar_in_bskl P `union` ftvar_in_bskl Q
         `union` dom Θ).
    assert (HwfΘ' : a_wf_aenv ((X ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - Fr; fsetdec | exact HwfΘ ]).
    pose proof (H0 X ltac:(clear - Fr; fsetdec) HwfΘ') as HX.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_lower P (bskl_var_f X))
      as Hlow.
    simpl in *. clear - HX Hlow Fr. fsetdec.
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
Lemma refine_primary_to_plain : forall Θtv Θr Δr L Q,
  (forall x b, binds x b Θtv -> b = abind_tvar) ->
  Δr [=] dom Θtv ->
  Θr ⨟ Δr ⊢ᵣᵃ L ⊳ Q ->
  (Θtv ++ Θr) ⨟ empty ⊢ᵣᵃ L ⊳ Q.
Proof.
  intros Θtv Θr Δr L Q Htvs HΔr H.
  eapply ad_refine_syn_delta_absorb with (Δr := Δr).
  - eapply ad_refine_syn_weaken; [ exact H | ].
    intros x b Hb. unfold binds in *. apply in_or_app; right; exact Hb.
  - intros Z HZ. right.
    assert (HZd : Z `in` dom Θtv) by (clear - HZ HΔr; fsetdec).
    apply binds_In_inv in HZd; destruct HZd as [b Hb].
    pose proof (Htvs _ _ Hb) as Heqb; subst b.
    unfold binds in *. apply in_or_app; left; exact Hb.
Qed.

(** no_hole is reflected by opening. *)
Lemma pskl_no_hole_open_rec_inv : forall P V k,
  pskl_no_hole (open_pskl_wrt_pskl_rec k V P) -> pskl_no_hole P.
Proof.
  induction P; intros V k H; simpl in *; auto.
  - destruct H as [H1 H2]; split; eauto.
  - eauto.
  - eauto.
Qed.

Lemma pskl_no_hole_open_inv : forall P V,
  pskl_no_hole (open_pskl_wrt_pskl P V) -> pskl_no_hole P.
Proof.
  intros P V H. eapply pskl_no_hole_open_rec_inv; exact H.
Qed.

(** msubst preserves and reflects no_hole (images are paints). *)
Lemma msubst_pskl_no_hole : forall θ P,
  pskl_no_hole P -> pskl_no_hole (msubst_pskl θ P).
Proof.
  intros θ; induction P; intros H; simpl in *; auto.
  - apply ptyp_to_pskl_no_hole.
  - destruct H; split; auto.
Qed.

Lemma msubst_pskl_no_hole_inv : forall θ P,
  pskl_no_hole (msubst_pskl θ P) -> pskl_no_hole P.
Proof.
  intros θ; induction P; intros H; simpl in *; auto.
  destruct H; split; auto.
Qed.

(** The solve output is hole-free whenever the counterpart is: holes in
    the output only ever come from a □-counterpart (VacuousR). *)
Lemma a_solve_eq_no_hole_p0 : forall Θ Pi P0 Pa,
  Θ ⊢ₑ Pi ∼ P0 ⤳ Pa ->
  pskl_no_hole P0 ->
  pskl_no_hole Pa.
Proof.
  intros Θ Pi P0 Pa H; induction H; intros Hnh; simpl in *; auto.
  - (* hole_r: the counterpart is □ — excluded *) contradiction.
  - (* arrow *) destruct Hnh; split; auto.
  - (* forall *)
    pick fresh β for L.
    apply (pskl_no_hole_open_inv P' (pskl_var_f β)).
    apply H0; [ clear - Fr; fsetdec | ].
    apply pskl_no_hole_open_rec; simpl; auto.
  - (* tophole_l_all (GhostForall) *)
    pick fresh β for L.
    apply (pskl_no_hole_open_inv P' (pskl_var_f β)).
    apply H0; [ clear - Fr; fsetdec | ].
    apply pskl_no_hole_open_rec; simpl; auto.
  - (* all_l_tophole (ForallGhost) *)
    pick fresh β for L.
    apply (pskl_no_hole_open_inv P' (pskl_var_f β)).
    apply H0; [ clear - Fr; fsetdec | exact Hnh ].
Qed.

(** A refinement into a Δr-binder variable (X0 outside the refinement's
    aenv) forces a hole-free source: the □-fill would have to BE that
    variable, which is not Θr-wf; flex hops never reach it. *)
Lemma ad_refine_inh_deltar_var_rhs_no_hole : forall Θr Δr L Q,
  Θr ⨟ Δr ⊢ᵣᵃ L ⊳ Q ->
  forall X0 P', Q = bskl_var_f X0 -> L = pskl_to_bskl_inh P' ->
  X0 `notin` dom Θr ->
  pskl_no_hole P'.
Proof.
  intros Θr Δr L Q H; induction H; intros X0 P' HeqQ HeqL HX0;
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
Lemma consis_subject_ftv_split_bound : forall Ψ Θ S Q Θtv Θr,
  Ψ ⨟ Θ ⊢ₛᵃ S ∼ Q ->
  Θ = Θtv ++ Θr ->
  (forall x b, binds x b Θtv -> b = abind_tvar) ->
  a_wf_aenv Θ ->
  ftvar_in_uskl S [<=] ftvar_in_bskl Q `union` dom Θr.
Proof.
  intros Ψ Θ S Q Θtv Θr H HeqΘ Htvs Hwf.
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
  (forall Y, Q <> bskl_var_f Y) ->
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
  forall NM Θ0 Θ θ Δ Δρ Ψρ Ψ' Ψi Ψa ψsub ψa Pi P0,
  a_wf_aenv Θ ->
  a_tags_sort NM Ψ' ψa ->
  Ψi `union` Ψa [<=] Ψ' ->
  rho_fresh Δρ Θ θ ->
  Δρ [<=] Δ ->
  (forall X, X `in` Δρ -> X `notin` pskl_shielded_ftv (msubst_pskl θ Pi)) ->
  Θ ⨟ Δ ⊢ (msubst_pskl θ Pi) ⊑ᵖ[ Ψi ] ψa ->
  rho_leaf NM Θ Δρ Ψρ ψsub ψa ->
  exists Pa, Θ0 ⊢ₑ Pi ∼ P0 ⤳ Pa /\
    forall Δ', Δ [<=] Δ' ->
    Θ ⨟ Δ' ⊢ (msubst_pskl θ Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa.
Proof.
  intros NM Θ0 Θ θ Δ Δρ Ψρ Ψ' Ψi Ψa ψsub ψa Pi P0
    HwfΘ Htags Hsub Hfresh Hdelta Hshield Hpre Hleaf.
  destruct Hleaf as (X & Ψ'' & Heqψa & HXΔρ & Htagsub & Hwfsub & HΨρ).
  subst ψa.
  pose proof (Hfresh X HXΔρ) as (HXb & Hθav & Hdef).
  assert (HXΔ : X `in` Δ) by (clear - Hdelta HXΔρ; fsetdec).
  pose proof (Hshield X HXΔρ) as Hsh.
  destruct (ad_ppre_delta_var_inv Hpre eq_refl HwfΘ HXΔ HXb Hdef Hsh)
    as (Heqm & HΨie).
  assert (HeqPi : Pi = pskl_var_f X)
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
      | left; clear - HXΔ Hsub'; fsetdec ].
Qed.

(* [wf-side-condition] delta_def_fresh Δ Θ — the paper's implicit wf of the
   Δ-extended precision context: Δ's binders postdate Θ's definition images.
   Discovered NECESSARY at the Var case (P6-Cv): with a defined-flex target
   var X whose definition mentions Y ∈ Δ, the Pi = □ subcase's conclusion
   precision needs the □-rule at the definition's paint, whose Δ-disjointness
   premise fails — a machine-checked counterexample against the Δ-free
   statement (see DESIGN §6(h)).  All call sites satisfy it: ForallInh
   binders are fresh w.r.t. dom Θ ⊇ def-ftvs (a_wf_aenv_def_ftv_dom), Δρ
   carries it in rho_fresh, and the initial Δ obeys the same discipline. *)

(* ===================================================================== *)
(*  PHASE-3 KIT — the precision RENAME (the ∀-cases' cofinite bodies come *)
(*  from renaming the single fresh-X run: the solve is not deterministic, *)
(*  so per-X reruns would return unrelated outputs) + the msubst/subst    *)
(*  commutation.                                                           *)
(* ===================================================================== *)

Lemma msubst_pskl_subst_var : forall θ Q X Y,
  X `notin` dom θ -> Y `notin` dom θ ->
  (forall p, In p θ -> X `notin` ftvar_in_ptyp (snd p)) ->
  subst_pskl_in_pskl (pskl_var_f Y) X (msubst_pskl θ Q)
  = msubst_pskl θ (subst_pskl_in_pskl (pskl_var_f Y) X Q).
Proof.
  intros θ Q X Y HX HY Hav; induction Q; simpl;
    try (f_equal; auto; fail).
  (* var_f *)
  destruct (α == X) as [-> | Hne].
    + rewrite (msubst_lookup_notin_dom _ HX).
      simpl.
      rewrite (msubst_lookup_notin_dom _ HY).
      default_simp.
    + assert (Hfr : X `notin`
                ftvar_in_pskl (ptyp_to_pskl (msubst_lookup θ α))).
      { rewrite ftvar_in_pskl_ptyp_to_pskl.
        intros Hc.
        assert (Heq : α = X)
          by (eapply msubst_lookup_ftv_avoid; [ exact Hav | exact Hc ]).
        auto. }
      rewrite (subst_pskl_in_pskl_fresh_eq _ _ _ Hfr).
      reflexivity.
Qed.

(** Renaming a Δ-variable in a partial-precision derivation.  [X] is a
    Δ-only variable (outside Θ and its definition images), [Y] globally
    fresh; the □-rule survives because its Δ-disjointness already forces
    X out of the local target. *)
Lemma ad_partial_precise_rename : forall Θ Δ Ψ P ψ,
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  forall Xr Yr,
  Xr `in` Δ ->
  Xr `notin` dom Θ ->
  Yr `notin` dom Θ -> Yr `notin` Δ ->
  Yr `notin` ftvar_in_pskl P -> Yr `notin` ftvar_in_uskl ψ ->
  (forall α τ, binds α (abind_flex_mono_def τ) Θ ->
     Xr `notin` ftvar_in_ptyp τ /\ Yr `notin` ftvar_in_ptyp τ) ->
  Θ ⨟ (add Yr (remove Xr Δ)) ⊢
    (subst_pskl_in_pskl (pskl_var_f Yr) Xr P)
    ⊑ᵖ[ Ψ ] (subst_bskl_in_uskl (uskl_var_f Yr) Xr ψ).
Proof.
  intros Θ Δ Ψ P ψ H; induction H;
    intros Xr Yr HXΔ HXΘ HYΘ HYΔ HYP HYψ Hdefs; simpl in *.
  - (* unit *) apply ad_ppre__unit; assumption.
  - (* var *)
    destruct (eq_var X Xr) as [-> | Hne].
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
      with (L := L `union` singleton Xr `union` singleton Yr
                   `union` Δ `union` dom Θ); [ | eassumption ].
    intros Z HZ.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - HZ; fsetdec | apply lc_pskl_var_f ].
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | clear - HZ; fsetdec | apply lc_uskl_var_f ].
    eapply ad_partial_precise_delta_cong;
      [ apply (H0 Z ltac:(clear - HZ; fsetdec) Xr Yr);
        [ clear - HXΔ; fsetdec
        | exact HXΘ | exact HYΘ
        | clear - HYΔ HZ; fsetdec
        | pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P
                        (pskl_var_f Z)) as Hup;
          simpl in Hup; clear - HYP HZ Hup; fsetdec
        | pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ
                        (uskl_var_f Z)) as Hup;
          simpl in Hup; clear - HYψ HZ Hup; fsetdec
        | exact Hdefs ]
      | clear - HZ; fsetdec ].
  - (* hole: X is already out of the local target *)
    match goal with Hint : _ ∩ _ [=] empty |- _ =>
      assert (HXψ : Xr `notin` ftvar_in_uskl ψ)
        by (clear - Hint HXΔ; fsetdec);
      rewrite (subst_bskl_in_uskl_fresh_eq _ _ _ HXψ);
      apply ad_ppre__hole; [ assumption | clear - Hint HYψ; fsetdec ]
    end.
  - (* tophole_remove *)
    apply ad_ppre__tophole_remove.
    apply IHad_partial_precise; auto.
  - (* tophole_fill *)
    eapply ad_ppre__tophole_fill
      with (L := L `union` singleton Xr `union` singleton Yr
                   `union` Δ `union` dom Θ).
    intros Z HZ.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | clear - HZ; fsetdec | apply lc_uskl_var_f ].
    replace (pskl_tophole (subst_pskl_in_pskl (pskl_var_f Yr) Xr P))
      with (subst_pskl_in_pskl (pskl_var_f Yr) Xr (pskl_tophole P))
      by reflexivity.
    apply (H0 Z ltac:(clear - HZ; fsetdec) Xr Yr).
    + exact HXΔ.
    + simpl. clear - HXΘ HZ; fsetdec.
    + simpl. clear - HYΘ HZ; fsetdec.
    + exact HYΔ.
    + simpl. simpl in HYP. exact HYP.
    + pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ
                    (uskl_var_f Z)) as Hup;
      simpl in Hup; clear - HYψ HZ Hup; fsetdec.
    + intros α τ Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
        [ discriminate Hc | exact (Hdefs _ _ Hb') ].
  - (* tophole_keep *)
    apply ad_ppre__tophole_keep.
    apply IHad_partial_precise; auto.
  - (* flex_l *)
    assert (Hne : α <> Xr).
    { intros ->. apply HXΘ. eapply binds_In; eassumption. }
    destruct_if as [Hc | _]; [ exfalso; auto | ].
    destruct (Hdefs _ _ H) as [HXτ HYτ].
    eapply ad_ppre__flex_l; [ eassumption | ].
    assert (Hfr : Xr `notin` ftvar_in_pskl (ptyp_to_pskl τ))
      by (rewrite ftvar_in_pskl_ptyp_to_pskl; exact HXτ).
    rewrite <- (subst_pskl_in_pskl_fresh_eq
                  (ptyp_to_pskl τ) (pskl_var_f Yr) Xr Hfr).
    apply IHad_partial_precise; auto.
    rewrite ftvar_in_pskl_ptyp_to_pskl. exact HYτ.
  - (* flex_r *)
    assert (Hne : α <> Xr).
    { intros ->. apply HXΘ. eapply binds_In; eassumption. }
    destruct_if as [Hc | _]; [ exfalso; auto | ].
    destruct (Hdefs _ _ H) as [HXτ HYτ].
    eapply ad_ppre__flex_r; [ eassumption | ].
    assert (Hfr : Xr `notin` ftvar_in_uskl (ptyp_to_uskl_syn τ))
      by (rewrite ftvar_in_uskl_ptyp_to_uskl_syn; exact HXτ).
    rewrite <- (subst_bskl_in_uskl_fresh_eq
                  (ptyp_to_uskl_syn τ) (uskl_var_f Yr) Xr Hfr).
    apply IHad_partial_precise; auto.
    rewrite ftvar_in_uskl_ptyp_to_uskl_syn. exact HYτ.
Qed.
