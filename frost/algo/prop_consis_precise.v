(** CONSISTENCY SUBJECT-PRECISION METATHEORY (completeness track).

    The consistency-side lemma family behind the paper's
    [lemma:precision-substitution] (subtyping-proofs.tex:1664): in
    [ad_pat_sub] the tag context is consumed by the CONSISTENCY premises, so
    substituting a more-precise (ghostier) [Pa] for a decorated instantiation
    [ψa] in a subtyping subject reduces, on every consistency premise, to
    SUBJECT-precision preserving consistency (docs/
    DESIGN-completeness-subtyping.md §5.2).  This file holds that
    consistency-level metatheory:

    - general tag/wf helpers shared with [prop_sub_complete.v] (the
      [pskl_no_forall] kit, [a_wf_pskl] Δ-narrowing, [d_tags_skl] /
      [a_tags_sort] inversions and congruences);
    - crux (1a) [ad_pat_consis_strip_tags]: strip the decorated subject to
      its plain skeleton (tags → ∅);
    - crux (1b) [ad_pat_consis_subject_refine]: transport the subject DOWN a
      refinement (subject-side mirror of the Qed target-side
      [ad_pat_consis_refine_inh_gen], prop_sub_sound.v), with the
      wf-carrying transporters it needs;
    - crux (1) [ad_pat_consis_subject_precise] = (1a);(1b);
    - step (2) [ad_pat_consis_precise_subst]: the general subject
      SUBSTITUTION [S[ψa/α] ∼ Q  ⇒  S[Pa/α] ∼ Q], by induction on the
      consistency derivation, whose [S = α] case is crux (1).  Its tag
      bookkeeping needs the syntactic-tag reading ([ftag_in_uskl],
      def_extra.v): the tag context is contained in the subject's tags
      ([ad_pat_consis_ftag_sub]), and the paper's [fresh Ψ'] side condition
      is rendered as disjointness from the subject's OTHER tags
      ([inter Ψ' (ftag S) = ∅]).  Consistency has no ForallL, so no new
      tags appear inside a derivation and the syntactic premise suffices —
      unlike the subtyping level (see prop_sub_complete.v §P5b-ii). *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_tags.
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

Set Implicit Arguments.

(* ===================================================================== *)
(*  General tag / wf helpers (shared with prop_sub_complete.v).           *)
(* ===================================================================== *)

(** A pskl with no synthesised quantifier: [inh] and [syn] paintings then
    coincide (they differ only at [pskl_all_syn]). *)
Fixpoint pskl_no_forall (P : pskl) : Prop :=
  match P with
  | pskl_all_syn _ => False
  | pskl_arrow P1 P2 => pskl_no_forall P1 /\ pskl_no_forall P2
  | pskl_tophole P0 => pskl_no_forall P0
  | _ => True
  end.

Lemma pskl_no_forall_inh_eq_syn : forall P,
  pskl_no_forall P -> pskl_to_bskl_inh P = pskl_to_bskl_syn P.
Proof.
  induction P; simpl; intros H; try reflexivity.
  - destruct H as [H1 H2]. rewrite IHP1, IHP2; auto.
  - contradiction.
  - rewrite IHP; auto.
Qed.

(** Empty tags ⇒ the erasure is quantifier-free ([all_etag] always carries a
    tag, so [d_tags_skl empty] excludes it). *)
Lemma d_tags_empty_no_forall : forall Ψ ψ,
  d_tags_skl Ψ ψ -> Ψ [=] empty -> pskl_no_forall (uskl_to_pskl ψ).
Proof.
  intros Ψ ψ H. induction H; intros HΨ; simpl.
  - exact I.
  - exact I.
  - split; [ apply IHd_tags_skl1 | apply IHd_tags_skl2 ]; fsetdec.
  - fsetdec.
  - exact I.
  - apply IHd_tags_skl; assumption.
Qed.

(** Narrow the ghost-binder context [Δ] to any [Δ'] that still contains every
    [Δ]-variable [P] actually uses. *)
Lemma a_wf_pskl_delta_narrow : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  forall Δ', (forall X, X `in` ftvar_in_pskl P -> X `in` Δ -> X `in` Δ') ->
  Θ ⨟ Δ' ⊢ₚₛᵃ P.
Proof.
  intros Θ Δ P H. induction H; intros Δ' Hnar; simpl in *.
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var.
    destruct H as [HΔ | Htv]; [ left; apply Hnar; [ clear; fsetdec | exact HΔ ] | right; exact Htv ].
  - apply a_wf_pskl__arrow;
      [ apply IHa_wf_pskl1 | apply IHa_wf_pskl2 ];
      intros X HX HXΔ; apply Hnar; auto; clear - HX; fsetdec.
  - apply a_wf_pskl__all with (L := L). intros X HX.
    apply H0; [ exact HX | ].
    intros Y HY HYΔ.
    destruct (Y == X) as [-> | Hne]; [ clear; fsetdec | ].
    assert (HYΔ0 : Y `in` Δ) by (clear - HYΔ Hne; fsetdec).
    assert (HYP : Y `in` ftvar_in_pskl P).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f X)) as Hup.
      simpl in Hup. clear - HY Hup Hne. fsetdec. }
    assert (Y `in` Δ') by (apply Hnar; auto). clear - H1; fsetdec.
  - apply a_wf_pskl__hole.
  - apply a_wf_pskl__tophole; [ exact H | ].
    apply IHa_wf_pskl. clear; intros X HX HXe; exact HXe.
Qed.

Lemma a_wf_pskl_delta_strip : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  AtomSetImpl.inter Δ (ftvar_in_pskl P) [=] empty ->
  Θ ⨟ empty ⊢ₚₛᵃ P.
Proof.
  intros Θ Δ P H Hdis.
  eapply a_wf_pskl_delta_narrow; [ exact H | ].
  intros X HX HXΔ. exfalso. clear - Hdis HX HXΔ. fsetdec.
Qed.

(** Clean structural inversions of [d_tags_skl] (name-agnostic). *)
Lemma d_tags_skl_unit_inv : forall Ψ,
  d_tags_skl Ψ uskl_unit -> Ψ [=] empty.
Proof. intros Ψ H. inversion H; subst; auto. Qed.

Lemma d_tags_skl_var_inv : forall Ψ X,
  d_tags_skl Ψ (uskl_var_f X) -> Ψ [=] empty.
Proof. intros Ψ X H. inversion H; subst; auto. Qed.

Lemma d_tags_skl_arrow_inv : forall Ψ ψ1 ψ2,
  d_tags_skl Ψ (uskl_arrow ψ1 ψ2) ->
  exists Ψ1 Ψ2, d_tags_skl Ψ1 ψ1 /\ d_tags_skl Ψ2 ψ2
             /\ AtomSetImpl.inter Ψ1 Ψ2 [=] empty /\ Ψ [=] Ψ1 `union` Ψ2.
Proof. intros Ψ ψ1 ψ2 H. inversion H; subst. eauto 10. Qed.

Lemma d_tags_skl_all_etag_inv : forall Ψ ε ψ,
  d_tags_skl Ψ (uskl_all_etag ε ψ) ->
  exists L Ψ0,
    (forall X, X `notin` L ->
       d_tags_skl Ψ0 (open_uskl_wrt_uskl ψ (uskl_var_f X)))
    /\ ε `notin` Ψ0 /\ Ψ [=] add ε Ψ0.
Proof. intros Ψ ε ψ H. inversion H; subst. eauto 8. Qed.

Lemma d_tags_skl_topholeg_inv : forall Ψ ψ,
  d_tags_skl Ψ (uskl_topholeg ψ) -> d_tags_skl Ψ ψ.
Proof. intros Ψ ψ H. inversion H; subst; auto. Qed.
(** Recover the tag reading / re-tag under set-equality. *)
Lemma a_tags_sort_d_tags : forall NM Ψ ψ,
  a_tags_sort NM Ψ ψ -> d_tags_skl Ψ ψ.
Proof. intros NM Ψ ψ H. inversion H; auto. Qed.

(** [d_tags_skl] respects set-equality (local copy of the lemma in
    prop_decorate_key.v — kept here so completeness does not depend on the
    soundness decoration file). *)
Lemma d_tags_skl_recong : forall Ψ Ψ' ψ,
  d_tags_skl Ψ ψ -> Ψ [=] Ψ' -> d_tags_skl Ψ' ψ.
Proof.
  intros Ψ Ψ' ψ H; revert Ψ'; induction H; intros Ψ' Heq.
  - apply d_tags_skl__unit; fsetdec.
  - apply d_tags_skl__var; fsetdec.
  - eapply d_tags_skl__arrow;
      [ exact H | exact H0 | exact H1 | clear - H2 Heq; fsetdec ].
  - eapply d_tags_skl__all_etag;
      [ exact H | exact H1 | clear - H2 Heq; fsetdec ].
  - apply d_tags_skl__holeg; fsetdec.
  - apply d_tags_skl__topholeg; apply IHd_tags_skl; exact Heq.
Qed.

Lemma a_tags_sort_psi_cong : forall NM Ψ Ψ' ψ,
  a_tags_sort NM Ψ ψ -> Ψ [=] Ψ' -> a_tags_sort NM Ψ' ψ.
Proof.
  intros NM Ψ Ψ' ψ H Heq. inversion H; subst;
    [ apply a_tags_sort__sk | apply a_tags_sort__ty ]; auto;
    eapply d_tags_skl_recong; eauto.
Qed.

(** Structural inversions of [a_tags_sort] (both modes at once), carrying the
    tag decomposition needed to pin the sub-derivations' tag sets. *)
Lemma a_tags_sort_arrow_inv : forall NM Ψ ψ1 ψ2,
  a_tags_sort NM Ψ (uskl_arrow ψ1 ψ2) ->
  exists Ψ1 Ψ2, a_tags_sort NM Ψ1 ψ1 /\ a_tags_sort NM Ψ2 ψ2
             /\ AtomSetImpl.inter Ψ1 Ψ2 [=] empty /\ Ψ [=] Ψ1 `union` Ψ2.
Proof.
  intros NM Ψ ψ1 ψ2 H. inversion H; subst;
    match goal with Ht : is_tskl _ |- _ => inversion Ht; subst end;
    match goal with Hd : d_tags_skl _ (uskl_arrow _ _) |- _ =>
      apply d_tags_skl_arrow_inv in Hd as [Ψa [Ψb [Hd1 [Hd2 [Hdisj Hun]]]]] end.
  - exists Ψa, Ψb. repeat apply conj; try assumption; apply a_tags_sort__sk; auto.
  - match goal with Hg : uskl_ghost_free (uskl_arrow _ _) |- _ =>
      inversion Hg; subst end.
    exists Ψa, Ψb. repeat apply conj; try assumption; apply a_tags_sort__ty; auto.
Qed.

Lemma a_tags_sort_all_etag_inv : forall NM Ψ ε ψ,
  a_tags_sort NM Ψ (uskl_all_etag ε ψ) ->
  exists L Ψ0,
    (forall X, X `notin` L ->
       a_tags_sort NM Ψ0 (open_uskl_wrt_uskl ψ (uskl_var_f X)))
    /\ ε `notin` Ψ0 /\ Ψ [=] add ε Ψ0.
Proof.
  intros NM Ψ ε ψ H. inversion H; subst.
  - (* sk *)
    match goal with Hit : is_tskl (uskl_all_etag _ _) |- _ =>
      inversion Hit; subst end.
    match goal with Hd : d_tags_skl _ (uskl_all_etag _ _) |- _ =>
      apply d_tags_skl_all_etag_inv in Hd as [Ld [Ψ0 [Hd0 [Hεt Hun]]]] end.
    match goal with Hit0 : forall X, X `notin` ?Li -> is_tskl _ |- _ =>
      exists (Li `union` Ld), Ψ0; repeat apply conj; try assumption;
      intros X HX; apply a_tags_sort__sk; [ apply Hit0 | apply Hd0 ]; fsetdec end.
  - (* ty *)
    match goal with Hit : is_tskl (uskl_all_etag _ _) |- _ =>
      inversion Hit; subst end.
    match goal with Hd : d_tags_skl _ (uskl_all_etag _ _) |- _ =>
      apply d_tags_skl_all_etag_inv in Hd as [Ld [Ψ0 [Hd0 [Hεt Hun]]]] end.
    match goal with Hgf : uskl_ghost_free (uskl_all_etag _ _) |- _ =>
      inversion Hgf; subst end.
    match goal with
    | Hit0 : forall X, X `notin` ?Li -> is_tskl _,
      Hgf0 : forall X, X `notin` ?Lg -> uskl_ghost_free _ |- _ =>
      exists (Li `union` Lg `union` Ld), Ψ0; repeat apply conj; try assumption;
      intros X HX;
      apply a_tags_sort__ty; [ apply Hit0 | apply Hd0 | apply Hgf0 ]; fsetdec
    end.
Qed.

(** Clean [a_wf_pskl] inversions (name-agnostic). *)
Lemma a_wf_pskl_all_inv : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ (pskl_all_syn P) ->
  exists L, forall X, X `notin` L ->
    Θ ⨟ (add X Δ) ⊢ₚₛᵃ (open_pskl_wrt_pskl P (pskl_var_f X)).
Proof. intros Θ Δ P H. inversion H; subst. eauto. Qed.

Lemma a_wf_pskl_tophole_inv : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ (pskl_tophole P) ->
  guarded_pskl P /\ Θ ⨟ empty ⊢ₚₛᵃ P.
Proof. intros Θ Δ P H. inversion H; subst. auto. Qed.

(* ===================================================================== *)
(*  P5b-ii — precision-substitution, foundational crux.                    *)
(*  The paper's no-type-mismatch step is, on the consistency premises,       *)
(*  subject-precision preserving consistency.  Built in two steps           *)
(*  consistency.  Built in two steps (DESIGN §5.2): (1a) strip the          *)
(*  decorated subject to plain (tags drop to ∅); (1b) transport the erased  *)
(*  subject along the refinement — the SUBJECT-side mirror of the Qed       *)
(*  target-side [ad_pat_consis_refine_inh_gen] (prop_sub_sound.v).          *)
(* ===================================================================== *)

(** [strip ψ := pskl_to_uskl ⌊ψ⌋ˢ] commutes with opening. *)
Lemma strip_uskl_open : forall ψ X,
  pskl_to_uskl (uskl_to_pskl (open_uskl_wrt_uskl ψ (uskl_var_f X)))
  = open_uskl_wrt_uskl (pskl_to_uskl (uskl_to_pskl ψ)) (uskl_var_f X).
Proof.
  intros ψ X. rewrite uskl_to_pskl_open, pskl_to_uskl_open. reflexivity.
Qed.

(** (1a) Stripping the decorated subject to its plain skeleton preserves
    consistency; the subject is then tag-free so the tag context is [∅]. *)
Lemma ad_pat_consis_strip_tags : forall Ψt Θ ψa Q,
  Ψt ⨟ Θ ⊢ₛᵃ ψa ∼ Q ->
  empty ⨟ Θ ⊢ₛᵃ (pskl_to_uskl (uskl_to_pskl ψa)) ∼ Q.
Proof.
  intros Ψt Θ ψa Q H. induction H; simpl.
  - apply ad_pat_consis__unit. reflexivity.
  - apply ad_pat_consis__var; [ reflexivity | assumption ].
  - eapply ad_pat_consis__arrow;
      [ exact IHad_pat_consis1 | exact IHad_pat_consis2 | fsetdec ].
  - eapply ad_pat_consis__forall_inh_untagged with (L := L).
    intros X HX. rewrite <- strip_uskl_open. exact (H0 X HX).
  - eapply ad_pat_consis__forall_inh_untagged with (L := L).
    intros X HX. rewrite <- strip_uskl_open. exact (H0 X HX).
  - eapply ad_pat_consis__forall_syn with (L := L).
    intros X HX. rewrite <- strip_uskl_open. exact (H0 X HX).
  - eapply ad_pat_consis__forall_syn with (L := L).
    intros X HX. rewrite <- strip_uskl_open. exact (H0 X HX).
  - change bskl_hole with (pskl_to_bskl_inh pskl_hole).
    apply ad_pat_consis__hole; [ reflexivity | apply a_wf_pskl__hole ].
  - (* topholeg: stripping the dotted ghost yields a plain [tophole] *)
    apply ad_pat_consis__tophole. exact IHad_pat_consis.
  - apply ad_pat_consis__hole; [ reflexivity | exact H0 ].
  - apply ad_pat_consis__tophole. exact IHad_pat_consis.
  - eapply ad_pat_consis__tophole_inh with (L := L).
    intros X HX. specialize (H0 X HX). simpl in H0. exact H0.
  - apply ad_pat_consis__tophole_drop. exact IHad_pat_consis.
  - eapply ad_pat_consis__flex_l; [ exact H | ].
    rewrite uskl_to_pskl_ptyp_to_uskl_syn, pskl_to_uskl_ptyp in IHad_pat_consis.
    exact IHad_pat_consis.
  - eapply ad_pat_consis__flex_r; [ exact H | exact IHad_pat_consis ].
Qed.

(** (1b) helpers: SUBJECT-side transport (mirror of [consis_transport_arrow]
    / [consis_transport_all], which transport the target).  Both subjects are
    tag-free ([pskl_to_uskl _]), so the tag context is inert. *)
(** WF-carrying subject transporters.  The transport hypotheses thread a
    [Θ' ⊢ bskl_to_pskl Q'] premise: the reconstruction at a subject HOLE
    ([B = uskl_hole]) needs the erased target well-formed (via
    [consis_concrete_target_inh] + [__hole]).  The wf-less transporters
    ([consis_forall/tophole_subject_transport], prop_consis_complete.v) cannot
    carry it, so these are genuine wf-variants, not duplicates. *)
Lemma consis_subj_transport_arrow_wf : forall Ψ Θ' A1 A2 B1 B2 Q,
  Ψ ⨟ Θ' ⊢ₛᵃ (uskl_arrow A1 A2) ∼ Q ->
  a_wf_aenv Θ' ->
  Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q) ->
  (forall Ψ1 Q1, Ψ1 ⨟ Θ' ⊢ₛᵃ A1 ∼ Q1 -> Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q1) ->
     Ψ1 ⨟ Θ' ⊢ₛᵃ B1 ∼ Q1) ->
  (forall Ψ2 Q2, Ψ2 ⨟ Θ' ⊢ₛᵃ A2 ∼ Q2 -> Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q2) ->
     Ψ2 ⨟ Θ' ⊢ₛᵃ B2 ∼ Q2) ->
  Ψ ⨟ Θ' ⊢ₛᵃ (uskl_arrow B1 B2) ∼ Q.
Proof.
  intros Ψ Θ' A1 A2 B1 B2 Q Hc Hwfa Hwfq Ht1 Ht2.
  remember (uskl_arrow A1 A2) as Ssub eqn:HS.
  revert Hwfq; induction Hc; try discriminate HS; intros Hwfq.
  - (* arrow: Q = bskl_arrow Q1 Q2 *)
    inversion HS; subst.
    simpl in Hwfq.
    inversion Hwfq as [ | | Θz Δz Pw1 Pw2 Hwfq1 Hwfq2 | | | ]; subst.
    apply ad_pat_consis__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2).
    + apply Ht1; assumption.
    + apply Ht2; assumption.
    + assumption.
  - (* flex_r: Q = bskl_var α ≔ τ; recurse at target [syn τ] *)
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    apply IHHc; [ exact HS | exact Hwfa | exact Ht1 | exact Ht2 | ].
    replace (bskl_to_pskl (ptyp_to_bskl_syn τ)) with (ptyp_to_pskl τ)
      by (unfold ptyp_to_bskl_syn; rewrite bskl_to_pskl_pskl_to_bskl_syn;
          reflexivity).
    apply a_wf_pskl_mono_ptyp;
      [ eapply a_wf_aenv_binds_def_mono; eauto
      | eapply a_wf_aenv_binds_def_wf; eauto ].
Qed.

(** WF bridge for a ∀-target: the erased opened body is wf under the ∀-var as
    a TVAR in [Θ] (which the consistency transport needs), from the opened
    body wf with the ∀-var in [Δ] (as [a_wf_pskl__all] gives it) via
    [a_wf_pskl_reassoc] + [a_wf_pskl_delta_narrow]. *)
Lemma wf_open_of_all : forall Θ Δ Q0 X,
  Θ ⨟ (add X Δ) ⊢ₚₛᵃ open_pskl_wrt_pskl (bskl_to_pskl Q0) (pskl_var_f X) ->
  ((X ~ abind_tvar) ++ Θ) ⨟ Δ
    ⊢ₚₛᵃ bskl_to_pskl (open_bskl_wrt_bskl Q0 (bskl_var_f X)).
Proof.
  intros Θ Δ Q0 X Hb.
  rewrite bskl_to_pskl_open.
  eapply a_wf_pskl_delta_narrow with (Δ := remove X (add X Δ)).
  - apply (a_wf_pskl_reassoc Hb X).
  - intros W HW HWin. clear - HWin. fsetdec.
Qed.

Lemma consis_forall_subject_transport_wf : forall Ψ Θ' A0 B0 Q L0,
  Ψ ⨟ Θ' ⊢ₛᵃ (uskl_all_syn A0) ∼ Q ->
  a_wf_aenv Θ' ->
  Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q) ->
  (forall X, X `notin` L0 -> forall Ψ' Q',
     Ψ' ⨟ ((X ~ abind_tvar) ++ Θ') ⊢ₛᵃ
       (open_uskl_wrt_uskl A0 (uskl_var_f X)) ∼ Q' ->
     ((X ~ abind_tvar) ++ Θ') ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q') ->
     Ψ' ⨟ ((X ~ abind_tvar) ++ Θ') ⊢ₛᵃ
       (open_uskl_wrt_uskl B0 (uskl_var_f X)) ∼ Q') ->
  Ψ ⨟ Θ' ⊢ₛᵃ (uskl_all_syn B0) ∼ Q.
Proof.
  intros Ψ Θ' A0 B0 Q L0 Hc Hwfa Hwfq Htr.
  remember (uskl_all_syn A0) as Ssub eqn:HS.
  revert Hwfq; induction Hc; try discriminate HS; intros Hwfq.
  - (* forall_inh_untagged: Q = bskl_all_inh Q0 *)
    inversion HS; subst.
    simpl in Hwfq. destruct (a_wf_pskl_all_inv Hwfq) as [Lw Hbody].
    apply ad_pat_consis__forall_inh_untagged with (L := L `union` L0 `union` Lw).
    intros X HX.
    apply Htr; [ clear - HX; fsetdec | apply H; clear - HX; fsetdec | ].
    apply wf_open_of_all. apply Hbody. clear - HX; fsetdec.
  - (* forall_syn: Q = bskl_all_syn Q0 *)
    inversion HS; subst.
    simpl in Hwfq. destruct (a_wf_pskl_all_inv Hwfq) as [Lw Hbody].
    apply ad_pat_consis__forall_syn with (L := L `union` L0 `union` Lw).
    intros X HX.
    apply Htr; [ clear - HX; fsetdec | apply H; clear - HX; fsetdec | ].
    apply wf_open_of_all. apply Hbody. clear - HX; fsetdec.
  - (* flex_r: Q = bskl_var α ≔ τ *)
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    apply IHHc; [ exact HS | exact Hwfa | exact Htr | ].
    replace (bskl_to_pskl (ptyp_to_bskl_syn τ)) with (ptyp_to_pskl τ)
      by (unfold ptyp_to_bskl_syn; rewrite bskl_to_pskl_pskl_to_bskl_syn;
          reflexivity).
    apply a_wf_pskl_mono_ptyp;
      [ eapply a_wf_aenv_binds_def_mono; eauto
      | eapply a_wf_aenv_binds_def_wf; eauto ].
Qed.

Lemma consis_tophole_subject_transport_wf : forall Ψ Θ' S Q,
  Ψ ⨟ Θ' ⊢ₛᵃ S ∼ Q ->
  a_wf_aenv Θ' ->
  Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q) ->
  forall S0 T0, S = uskl_tophole S0 ->
  (forall Θ'' Ψ' Q',
     a_wf_aenv Θ'' ->
     (forall x b, binds x b Θ' -> binds x b Θ'') ->
     Ψ' ⨟ Θ'' ⊢ₛᵃ S0 ∼ Q' ->
     Θ'' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q') ->
     Ψ' ⨟ Θ'' ⊢ₛᵃ T0 ∼ Q') ->
  Ψ ⨟ Θ' ⊢ₛᵃ (uskl_tophole T0) ∼ Q.
Proof.
  intros Ψ Θ' S Q Hc; induction Hc;
    intros HwfΘ Hwfq S0 T0 HeqS Htr; try discriminate HeqS.
  - (* tophole: Q = bskl_tophole Q0 *)
    inversion HeqS; subst.
    simpl in Hwfq. destruct (a_wf_pskl_tophole_inv Hwfq) as [Hg Hwfb].
    apply ad_pat_consis__tophole.
    apply (Htr Θ); [ exact HwfΘ | intros x b Hb; exact Hb | exact Hc | exact Hwfb ].
  - (* tophole_inh: Q = bskl_all_inh Q0, extended context *)
    inversion HeqS; subst.
    simpl in Hwfq. destruct (a_wf_pskl_all_inv Hwfq) as [Lw Hbody].
    apply ad_pat_consis__tophole_inh with (L := L `union` dom Θ `union` Lw).
    intros X HX.
    assert (HwfX : a_wf_aenv ((X ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - HX; fsetdec | exact HwfΘ ]).
    eapply (H0 X ltac:(clear - HX; fsetdec) HwfX).
    + apply wf_open_of_all. apply Hbody. clear - HX; fsetdec.
    + reflexivity.
    + intros Θ'' Ψ' Q' Hwf' Hincl' Hc' Hwfq'.
      apply (Htr Θ'' Ψ' Q' Hwf'); [ | exact Hc' | exact Hwfq' ].
      intros x b Hb. apply Hincl'. apply binds_cons_3. exact Hb.
  - (* tophole_drop: Q arbitrary *)
    inversion HeqS; subst.
    apply ad_pat_consis__tophole_drop.
    apply (Htr Θ); [ exact HwfΘ | intros x b Hb; exact Hb | exact Hc | exact Hwfq ].
  - (* flex_r: Q = bskl_var α ≔ τ *)
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    eapply IHHc; [ exact HwfΘ | | exact HeqS | exact Htr ].
    replace (bskl_to_pskl (ptyp_to_bskl_syn τ)) with (ptyp_to_pskl τ)
      by (unfold ptyp_to_bskl_syn; rewrite bskl_to_pskl_pskl_to_bskl_syn;
          reflexivity).
    apply a_wf_pskl_mono_ptyp;
      [ eapply a_wf_aenv_binds_def_mono; eauto
      | eapply a_wf_aenv_binds_def_wf; eauto ].
Qed.

(** Monotypes paint to ∀-free plain skeletons. *)
Lemma mono_ptyp_pskl_no_forall : forall τ,
  mono_ptyp τ -> pskl_no_forall (ptyp_to_pskl τ).
Proof. intros τ Hm; induction Hm; simpl; auto. Qed.

(** An inh-painting that equals a syn-painting is ∀-free (paintings differ
    only at [pskl_all_syn]). *)
Lemma inh_eq_syn_no_forall : forall A B,
  pskl_to_bskl_inh A = pskl_to_bskl_syn B -> pskl_no_forall A.
Proof.
  induction A; intros B H; destruct B; simpl in H; try discriminate;
    simpl; auto.
  - inversion H. split; [ eapply IHA1 | eapply IHA2 ]; eauto.
  - inversion H. eapply IHA; eauto.
Qed.

(** (1b) hole-case leaf (EQUATION ONLY): a CONCRETE, ∀-free subject
    [pskl_to_uskl P] consistent with [Q] forces [Q] to be an inh-painting of
    its own erasure — [inh (bskl_to_pskl Q) = Q] — with empty tags.  That is
    ALL the main lemma's hole case needs: combined with a THREADED
    [Θ ⊢ bskl_to_pskl Q] (well-formedness is an INPUT, not a conclusion — cf.
    [ad_pat_consis_refine_inh_gen]'s [Bsrc] premise), [uskl_hole ∼ Q] follows
    by [__hole] with [B := bskl_to_pskl Q].  Proving only the EQUATION avoids
    reconstructing the wf of a ∀-witness under the [Θ↔Δ] tension (which is not
    a general fact — a [⊤◇] body cannot reference a Δ-var). *)
Lemma consis_concrete_target_inh : forall Ψ Θ S Q,
  Ψ ⨟ Θ ⊢ₛᵃ S ∼ Q ->
  a_wf_aenv Θ ->
  forall P, S = pskl_to_uskl P ->
  pskl_no_forall P ->
  Ψ [=] empty /\ pskl_to_bskl_inh (bskl_to_pskl Q) = Q.
Proof.
  intros Ψ Θ S Q Hc; induction Hc; intros Hwfa P0 HS Hnf.
  - (* unit *)  split; [ exact H | reflexivity ].
  - (* var *)   split; [ exact H | reflexivity ].
  - (* arrow *)
    destruct P0 as [ | n | Xv | Pl Pr | Pq | | Pt ];
      simpl in HS; try discriminate HS. inversion HS; subst.
    simpl in Hnf; destruct Hnf as [Hnf1 Hnf2].
    destruct (IHHc1 Hwfa _ eq_refl Hnf1) as [HΨ1 Heq1].
    destruct (IHHc2 Hwfa _ eq_refl Hnf2) as [HΨ2 Heq2].
    split; [ fsetdec | simpl; rewrite Heq1, Heq2; reflexivity ].
  - (* forall_inh_tagged: subject all_etag — impossible *)
    destruct P0 as [ | n | Xv | Pl Pr | Pq | | Pt ]; simpl in HS; discriminate HS.
  - (* forall_inh_untagged: subject all_syn ⇒ ¬nf *)
    destruct P0 as [ | n | Xv | Pl Pr | Pq | | Pt ];
      simpl in HS; try discriminate HS. simpl in Hnf; contradiction.
  - (* forall_syn_tagged *)
    destruct P0 as [ | n | Xv | Pl Pr | Pq | | Pt ]; simpl in HS; discriminate HS.
  - (* forall_syn ⇒ ¬nf *)
    destruct P0 as [ | n | Xv | Pl Pr | Pq | | Pt ];
      simpl in HS; try discriminate HS. simpl in Hnf; contradiction.
  - (* ghostg *)
    destruct P0 as [ | n | Xv | Pl Pr | Pq | | Pt ]; simpl in HS; discriminate HS.
  - (* topholeg *)
    destruct P0 as [ | n | Xv | Pl Pr | Pq | | Pt ]; simpl in HS; discriminate HS.
  - (* hole *)
    split; [ exact H
           | simpl; rewrite bskl_to_pskl_pskl_to_bskl_inh; reflexivity ].
  - (* tophole: bskl_tophole Q0 *)
    destruct P0 as [ | n | Xv | Pl Pr | Pq | | Pt ];
      simpl in HS; try discriminate HS. inversion HS; subst.
    simpl in Hnf.
    destruct (IHHc Hwfa _ eq_refl Hnf) as [HΨ0 Heq0].
    split; [ exact HΨ0 | simpl; rewrite Heq0; reflexivity ].
  - (* tophole_inh: bskl_all_inh Q0 — close the opened equation via open-inj *)
    destruct P0 as [ | n | Xv | Pl Pr | Pq | | Pt ];
      simpl in HS; try discriminate HS. inversion HS; subst.
    simpl in Hnf.
    pick fresh X for (L `union` dom Θ `union` ftvar_in_bskl Q).
    assert (HwfX : a_wf_aenv ((X ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ fsetdec | exact Hwfa ]).
    destruct (H0 X ltac:(fsetdec) HwfX (pskl_tophole Pt) eq_refl Hnf)
      as [HΨX HeqX].
    split; [ exact HΨX | ].
    simpl. f_equal.
    eapply open_bskl_wrt_bskl_inj with (Xbs1 := X).
    + rewrite ftvar_in_bskl_inh, ftvar_in_pskl_bskl_to_pskl. fsetdec.
    + fsetdec.
    + rewrite <- pskl_to_bskl_inh_open, <- bskl_to_pskl_open. exact HeqX.
  - (* tophole_drop: Q arbitrary *)
    destruct P0 as [ | n | Xv | Pl Pr | Pq | | Pt ];
      simpl in HS; try discriminate HS. inversion HS; subst.
    simpl in Hnf.
    destruct (IHHc Hwfa _ eq_refl Hnf) as [HΨ0 Heq0].
    split; [ exact HΨ0 | exact Heq0 ].
  - (* flex_l: subject uskl_var α def; target [Q] unchanged *)
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    assert (Heq : ptyp_to_uskl_syn τ = pskl_to_uskl (ptyp_to_pskl τ))
      by (symmetry; apply pskl_to_uskl_ptyp).
    assert (Hnf' : pskl_no_forall (ptyp_to_pskl τ))
      by (apply mono_ptyp_pskl_no_forall; auto).
    destruct (IHHc Hwfa (ptyp_to_pskl τ) Heq Hnf') as [HΨ Heqq].
    split; [ exact HΨ | exact Heqq ].
  - (* flex_r: Q = bskl_var α *)
    destruct (IHHc Hwfa P0 HS Hnf) as [HΨ _].
    split; [ exact HΨ | reflexivity ].
Qed.


(** Monotonicity of [a_binds_tvar] under context extension. *)
Lemma a_binds_tvar_mono : forall X Θ Θ',
  a_binds_tvar X Θ ->
  (forall x b, binds x b Θ -> binds x b Θ') ->
  a_binds_tvar X Θ'.
Proof.
  intros X Θ Θ' H Hmon. unfold a_binds_tvar in *.
  destruct H as [Hb | [Hb | [τ Hb]]];
    [ left | right; left | right; right; exists τ ]; apply Hmon; exact Hb.
Qed.

(** (1b) — SUBJECT-REFINEMENT preserves consistency.  If [Ptgt] refines to
    [Psrc] ([Psrc] ghostier), then any [Q] consistent with the FILLED subject
    [Ptgt] is consistent with the GHOSTIER subject [Psrc].  Well-formedness of
    the (erased) target is THREADED as an input (the hole reconstruction needs
    it; see [consis_concrete_target_inh]).  Subject-side mirror of the target
    template [ad_pat_consis_refine_inh_gen] (prop_sub_sound.v). *)
Lemma ad_pat_consis_subject_refine : forall Θ Δ Src Tgt,
  ad_refine_syn Θ Δ Src Tgt ->
  forall Psrc Ptgt, Src = pskl_to_bskl_inh Psrc -> Tgt = pskl_to_bskl_inh Ptgt ->
  forall Θ',
  (forall x b, binds x b Θ -> binds x b Θ') ->
  (forall X, X `in` Δ -> a_binds_tvar X Θ') ->
  a_wf_aenv Θ' ->
  forall Ψ Q,
    Ψ ⨟ Θ' ⊢ₛᵃ (pskl_to_uskl Ptgt) ∼ Q ->
    Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q) ->
    Ψ ⨟ Θ' ⊢ₛᵃ (pskl_to_uskl Psrc) ∼ Q.
Proof.
  intros Θ Δ Src Tgt Hr.
  induction Hr; intros Psrc Ptgt HSrc HTgt Θ' Hmon Hrig Hwf' Ψ Qc Hc Hwfq.
  - (* unit *)
    destruct Psrc; simpl in HSrc; try discriminate HSrc.
    destruct Ptgt; simpl in HTgt; try discriminate HTgt. exact Hc.
  - (* var *)
    destruct Psrc; simpl in HSrc; try discriminate HSrc.
    destruct Ptgt; simpl in HTgt; try discriminate HTgt.
    inversion HSrc; inversion HTgt; subst. exact Hc.
  - (* arrow *)
    destruct Psrc as [ | | | Ps1 Ps2 | | | ]; simpl in HSrc; try discriminate HSrc.
    destruct Ptgt as [ | | | Pt1 Pt2 | | | ]; simpl in HTgt; try discriminate HTgt.
    inversion HSrc; inversion HTgt; subst.
    simpl in Hwfq.
    eapply consis_subj_transport_arrow_wf;
      [ exact Hc | exact Hwf' | exact Hwfq | | ].
    + intros Ψ1 Q1 Hc1 Hwfq1.
      eapply IHHr1;
        [ reflexivity | reflexivity | exact Hmon | exact Hrig | exact Hwf'
        | exact Hc1 | exact Hwfq1 ].
    + intros Ψ2 Q2 Hc2 Hwfq2.
      eapply IHHr2;
        [ reflexivity | reflexivity | exact Hmon | exact Hrig | exact Hwf'
        | exact Hc2 | exact Hwfq2 ].
  - (* all: Src = all_inh S0, Tgt = all_inh T0 (Δ grows under the binder) *)
    destruct Psrc as [ | | | | Ps0 | | ]; simpl in HSrc; try discriminate HSrc.
    destruct Ptgt as [ | | | | Pt0 | | ]; simpl in HTgt; try discriminate HTgt.
    inversion HSrc; inversion HTgt; subst.
    simpl. simpl in Hc.
    eapply consis_forall_subject_transport_wf
      with (A0 := pskl_to_uskl Pt0) (B0 := pskl_to_uskl Ps0)
           (L0 := L `union` dom Θ' `union` Δ);
      [ exact Hc | exact Hwf' | exact Hwfq | ].
    intros X HX Ψ' Q' Hc' Hwfq'.
    rewrite <- pskl_to_uskl_open_var.
    rewrite <- pskl_to_uskl_open_var in Hc'.
    eapply (H0 X ltac:(clear - HX; fsetdec)
              (open_pskl_wrt_pskl Ps0 (pskl_var_f X))
              (open_pskl_wrt_pskl Pt0 (pskl_var_f X)));
      [ symmetry; apply pskl_to_bskl_inh_open
      | symmetry; apply pskl_to_bskl_inh_open
      | intros x b Hb; unfold binds; simpl; right; apply Hmon; exact Hb
      | intros Y HYΔ; destruct (Y == X) as [ -> | Hne ];
          [ left; unfold binds; simpl; left; reflexivity
          | apply a_binds_tvar_weaken_cons; apply Hrig;
            clear - HYΔ Hne; fsetdec ]
      | apply a_wf_aenv__tvar; [ clear - HX; fsetdec | exact Hwf' ]
      | exact Hc'
      | exact Hwfq' ].
  - (* hole: Src = bskl_hole, Tgt = syn P (∀-free) *)
    destruct Psrc; simpl in HSrc; try discriminate HSrc.
    assert (Hnf : pskl_no_forall Ptgt)
      by (eapply inh_eq_syn_no_forall; symmetry; exact HTgt).
    destruct (consis_concrete_target_inh Hc Hwf' Ptgt eq_refl Hnf) as [HΨ Heqinh].
    simpl. rewrite <- Heqinh.
    apply ad_pat_consis__hole; [ exact HΨ | exact Hwfq ].
  - (* tophole_remove: Src = ⊤◇ S0, Tgt = P (same); drop the ⊤◇ *)
    destruct Psrc as [ | | | | | | Ps0 ]; simpl in HSrc; try discriminate HSrc.
    inversion HSrc; subst.
    simpl. apply ad_pat_consis__tophole_drop.
    eapply IHHr;
      [ reflexivity | reflexivity | exact Hmon | exact Hrig | exact Hwf'
      | exact Hc | exact Hwfq ].
  - (* tophole_fill: Tgt = all_syn P — impossible for an inh painting *)
    destruct Ptgt; simpl in HTgt; try discriminate HTgt.
  - (* tophole_keep: Src = ⊤◇ S0, Tgt = ⊤◇ T0 *)
    destruct Psrc as [ | | | | | | Ps0 ]; simpl in HSrc; try discriminate HSrc.
    destruct Ptgt as [ | | | | | | Pt0 ]; simpl in HTgt; try discriminate HTgt.
    inversion HSrc; inversion HTgt; subst.
    simpl. simpl in Hc.
    eapply consis_tophole_subject_transport_wf
      with (S0 := pskl_to_uskl Pt0) (T0 := pskl_to_uskl Ps0);
      [ exact Hc | exact Hwf' | exact Hwfq | reflexivity | ].
    intros Θ'' Ψ' Q' Hwf'' Hincl'' Hc'' Hwfq''.
    eapply IHHr with (Ptgt := Pt0);
      [ reflexivity | reflexivity
      | intros x b Hb; apply Hincl''; apply Hmon; exact Hb
      | intros Y HYΔ; eapply a_binds_tvar_mono;
          [ apply Hrig; exact HYΔ | exact Hincl'' ]
      | exact Hwf'' | exact Hc'' | exact Hwfq'' ].
  - (* flex_l: Src = bskl_var α (α ≔ τ), premise syn τ ⊳ Tgt *)
    destruct Psrc as [ | | X | | | | ]; simpl in HSrc; try discriminate HSrc.
    inversion HSrc; subst.
    assert (Hmτ : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf' | apply Hmon; exact H ]).
    simpl. eapply ad_pat_consis__flex_l; [ apply Hmon; exact H | ].
    replace (ptyp_to_uskl_syn τ) with (pskl_to_uskl (ptyp_to_pskl τ))
      by (apply pskl_to_uskl_ptyp).
    eapply IHHr with (Ptgt := Ptgt);
      [ symmetry; apply (mono_inh_eq_syn Hmτ) | reflexivity
      | exact Hmon | exact Hrig | exact Hwf' | exact Hc | exact Hwfq ].
  - (* flex_r: Tgt = bskl_var α (α ≔ τ), premise Src ⊳ syn τ *)
    destruct Ptgt as [ | | X | | | | ]; simpl in HTgt; try discriminate HTgt.
    inversion HTgt; subst.
    assert (Hmτ : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf' | apply Hmon; exact H ]).
    simpl in Hc.
    assert (Hc' : Ψ ⨟ Θ' ⊢ₛᵃ (ptyp_to_uskl_syn τ) ∼ Qc)
      by (eapply consis_unfold_def_subject;
            [ exact Hc | exact Hwf' | reflexivity | apply Hmon; exact H ]).
    replace (ptyp_to_uskl_syn τ) with (pskl_to_uskl (ptyp_to_pskl τ)) in Hc'
      by (apply pskl_to_uskl_ptyp).
    eapply IHHr with (Ptgt := ptyp_to_pskl τ);
      [ reflexivity | symmetry; apply (mono_inh_eq_syn Hmτ)
      | exact Hmon | exact Hrig | exact Hwf' | exact Hc' | exact Hwfq ].
Qed.

(** Crux (1): a plain [ψa]-consistency, composed with a precision
    [Pa ⊑ ⌊ψa⌋], yields a [Pa]-consistency.  This is [(1a) ; (1b)]:
    [ad_pat_consis_strip_tags] erases the decorated subject to
    [⌊ψa⌋] (tags → ∅), then [ad_pat_consis_subject_refine] transports it
    down the precision to [Pa].  The (erased) target's wf is THREADED. *)
Lemma ad_pat_consis_subject_precise : forall Ψt Θ Δ ψa Pa Q,
  Ψt ⨟ Θ ⊢ₛᵃ ψa ∼ Q ->
  Θ ⨟ Δ ⊢ₚᵣᵃ Pa ⊑ (uskl_to_pskl ψa) ->
  a_wf_aenv Θ ->
  (forall X, X `in` Δ -> a_binds_tvar X Θ) ->
  Θ ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q) ->
  empty ⨟ Θ ⊢ₛᵃ (pskl_to_uskl Pa) ∼ Q.
Proof.
  intros Ψt Θ Δ ψa Pa Q Hc Hpre Hwfa Hrig Hwfq.
  unfold ad_precise in Hpre.
  eapply ad_pat_consis_subject_refine with (Δ := Δ);
    [ exact Hpre
    | reflexivity
    | reflexivity
    | intros x b Hb; exact Hb
    | exact Hrig
    | exact Hwfa
    | eapply ad_pat_consis_strip_tags; exact Hc
    | exact Hwfq ].
Qed.

(* ===================================================================== *)
(*  Step (2) infrastructure — syntactic tags [ftag_in_uskl] (def_tags.v). *)
(* ===================================================================== *)

Lemma ftag_in_uskl_open_rec_var : forall X R k,
  ftag_in_uskl (open_uskl_wrt_uskl_rec k (uskl_var_f X) R) [=] ftag_in_uskl R.
Proof.
  intros X R; induction R; intros k; simpl; try fsetdec.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; fsetdec.
  - pose proof (IHR1 k); pose proof (IHR2 k); fsetdec.
  - pose proof (IHR (S k)); fsetdec.
  - pose proof (IHR (S k)); fsetdec.
  - pose proof (IHR k); fsetdec.
  - pose proof (IHR k); fsetdec.
Qed.

Lemma ftag_in_uskl_open_var : forall R X,
  ftag_in_uskl (open_uskl_wrt_uskl R (uskl_var_f X)) [=] ftag_in_uskl R.
Proof.
  intros; unfold open_uskl_wrt_uskl; apply ftag_in_uskl_open_rec_var.
Qed.

(** Paintings of bidirectional skeletons / plain skeletons / types are
    tag-free ([bskl]/[pskl]/[ptyp] have no [all_etag]). *)
Lemma ftag_in_bskl_to_uskl : forall Q,
  ftag_in_uskl (bskl_to_uskl Q) [=] empty.
Proof. induction Q; simpl; fsetdec. Qed.

Lemma ftag_in_uskl_ptyp_syn : forall A,
  ftag_in_uskl (ptyp_to_uskl_syn A) [=] empty.
Proof. intros; unfold ptyp_to_uskl_syn; apply ftag_in_bskl_to_uskl. Qed.

Lemma ftag_in_pskl_to_uskl : forall P,
  ftag_in_uskl (pskl_to_uskl P) [=] empty.
Proof. induction P; simpl; fsetdec. Qed.

(** A decorated skeleton's tag reading is exactly its syntactic tags. *)
Lemma d_tags_skl_ftag : forall Ψ ψ,
  d_tags_skl Ψ ψ -> Ψ [=] ftag_in_uskl ψ.
Proof.
  intros Ψ ψ H; induction H; simpl; try fsetdec.
  - match goal with |- _ [=] add _ (ftag_in_uskl ?R) =>
      pick fresh X for L;
      pose proof (H0 X ltac:(fsetdec)) as HX;
      pose proof (ftag_in_uskl_open_var R X) as Hov
    end; fsetdec.
Qed.

(** The consistency tag context is contained in the SUBJECT's syntactic
    tags — every solved tag is consumed at an [all_etag] node of the
    subject.  (Syntactic counterpart of [ad_partial_precise_tags_sub],
    prop_sub_complete.v; the precision-substitution crux uses it to pin
    the residual tag context of a wholly-[ψa] subject to ∅.) *)
Lemma ad_pat_consis_ftag_sub : forall Ψ Θ S Q,
  Ψ ⨟ Θ ⊢ₛᵃ S ∼ Q ->
  Ψ [<=] ftag_in_uskl S.
Proof.
  intros Ψ Θ S Q H; induction H; simpl; try fsetdec.
  - (* forall_inh_tagged *)
    match goal with |- _ [<=] add _ (ftag_in_uskl ?R) =>
      pick fresh X for L;
      pose proof (H0 X ltac:(fsetdec)) as HX;
      pose proof (ftag_in_uskl_open_var R X) as Hov
    end; fsetdec.
  - (* forall_inh_untagged *)
    match goal with |- _ [<=] ftag_in_uskl ?R =>
      pick fresh X for L;
      pose proof (H0 X ltac:(fsetdec)) as HX;
      pose proof (ftag_in_uskl_open_var R X) as Hov
    end; fsetdec.
  - (* forall_syn_tagged *)
    match goal with |- _ [<=] add _ (ftag_in_uskl ?R) =>
      pick fresh X for L;
      pose proof (H0 X ltac:(fsetdec)) as HX;
      pose proof (ftag_in_uskl_open_var R X) as Hov
    end; fsetdec.
  - (* forall_syn *)
    match goal with |- _ [<=] ftag_in_uskl ?R =>
      pick fresh X for L;
      pose proof (H0 X ltac:(fsetdec)) as HX;
      pose proof (ftag_in_uskl_open_var R X) as Hov
    end; fsetdec.
  - (* tophole_inh: subject fixed under the target binder *)
    pick fresh X for L;
    pose proof (H0 X ltac:(fsetdec)) as HX; simpl in HX; fsetdec.
  - (* flex_l: the unfolded def is a painted monotype — tag-free *)
    match goal with H0 : _ [<=] ftag_in_uskl (ptyp_to_uskl_syn ?t) |- _ =>
      pose proof (ftag_in_uskl_ptyp_syn t) end; fsetdec.
Qed.

(* ===================================================================== *)
(*  Step (2) — the [S = α] crux case, packaged: a wholly-[ψa] subject      *)
(*  transports to [Pa] with residual tag context ∅ (= Ψ).                  *)
(* ===================================================================== *)

Lemma ad_pat_consis_precise_var_case : forall NM Ψ' Θb Δ ψa Pa,
  a_tags_sort NM Ψ' ψa ->
  Θb ⨟ Δ ⊢ₚᵣᵃ Pa ⊑ (uskl_to_pskl ψa) ->
  forall Ψfull Θ' Qc Ψ Ψa,
  Ψfull ⨟ Θ' ⊢ₛᵃ ψa ∼ Qc ->
  (forall x b, binds x b Θb -> binds x b Θ') ->
  (forall X, X `in` Δ -> a_binds_tvar X Θ') ->
  a_wf_aenv Θ' ->
  Ψfull [=] Ψ `union` Ψa ->
  AtomSetImpl.inter Ψ' Ψ [=] empty ->
  Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Qc) ->
  Ψ ⨟ Θ' ⊢ₛᵃ (pskl_to_uskl Pa) ∼ Qc.
Proof.
  intros NM Ψ' Θb Δ ψa Pa Htags Hpre Ψfull Θ' Qc Ψ Ψa
    Hnode Hmon Hrig Hwf HΨf Hdisj Hwfq.
  assert (HΨe : Ψ [=] empty).
  { pose proof (ad_pat_consis_ftag_sub Hnode) as Hsub.
    pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags)) as Htg.
    clear - Hsub Htg HΨf Hdisj. fsetdec. }
  unfold ad_precise in Hpre.
  eapply ad_pat_consis_psi_cong with (Ψ := empty); [ | clear - HΨe; fsetdec ].
  eapply ad_pat_consis_subject_refine with (Δ := Δ) (Ptgt := uskl_to_pskl ψa);
    [ exact Hpre | reflexivity | reflexivity | exact Hmon | exact Hrig
    | exact Hwf | eapply ad_pat_consis_strip_tags; exact Hnode | exact Hwfq ].
Qed.

(* ===================================================================== *)
(*  Step (2) — [ad_pat_consis_precise_subst]: substituting the more        *)
(*  precise [Pa] for the decorated instantiation [ψa] in a consistency     *)
(*  SUBJECT preserves consistency; the tag context drops by [ψa]'s solved  *)
(*  tags [Ψa].  Paper: the consistency face of                             *)
(*  [lemma:precision-substitution] (subtyping-proofs.tex:1664).            *)
(*                                                                         *)
(*  Freshness reading (the paper's [fresh Ψ'], DESIGN §5.2/§5.4): [ψa]'s   *)
(*  tags [Ψ'] are disjoint from BOTH the residual tag context [Ψ] and the  *)
(*  subject's other syntactic tags [ftag_in_uskl S] — without the latter,  *)
(*  a tag shared between an [all_etag] of [S] and one of [ψa] makes the    *)
(*  conclusion underivable (the [S]-node is forced to re-consume a tag     *)
(*  that substitution removed).  Consistency derivations introduce no new  *)
(*  tags (no ForallL), so the syntactic premise is stable under the        *)
(*  induction.                                                             *)
(* ===================================================================== *)

Lemma ad_pat_consis_precise_subst : forall Θb Δ α ψa Pa Ψ' NM,
  lc_uskl ψa ->
  lc_pskl Pa ->
  a_tags_sort NM Ψ' ψa ->
  Θb ⨟ Δ ⊢ₚᵣᵃ Pa ⊑ (uskl_to_pskl ψa) ->
  forall Ψfull Θ' Ssub Qc,
  Ψfull ⨟ Θ' ⊢ₛᵃ Ssub ∼ Qc ->
  forall S Ψ Ψa,
  Ssub = subst_bskl_in_uskl ψa α S ->
  (forall x b, binds x b Θb -> binds x b Θ') ->
  (forall X, X `in` Δ -> a_binds_tvar X Θ') ->
  a_wf_aenv Θ' ->
  α `notin` dom Θ' ->
  Ψfull [=] Ψ `union` Ψa ->
  Ψa [<=] Ψ' ->
  AtomSetImpl.inter Ψ' Ψ [=] empty ->
  AtomSetImpl.inter Ψ' (ftag_in_uskl S) [=] empty ->
  Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Qc) ->
  Ψ ⨟ Θ' ⊢ₛᵃ (subst_bskl_in_uskl (pskl_to_uskl Pa) α S) ∼ Qc.
Proof.
  intros Θb Δ α ψa Pa Ψ' NM Hlcψa HlcPa Htags Hpre.
  intros Ψfull Θ' Ssub Qc Hc.
  induction Hc;
    intros S0 Ψn Ψna HeqS Hmon Hrig Hwf Hαd HΨfull HΨa Hdisj Hftag Hwfq.
  - (* unit *)
    destruct S0 as [ | nb | β | S1 S2 | S9 | ε9 S9 | | S9 | | S9 ];
      simpl in HeqS |- *; try discriminate HeqS.
    + apply ad_pat_consis__unit. clear - H HΨfull; fsetdec.
    + destruct (β == α) as [-> | Hneq]; [ | discriminate HeqS ].
      eapply ad_pat_consis_precise_var_case with
        (Ψfull := Ψ) (Ψa := Ψna) (Δ := Δ);
        [ exact Htags | exact Hpre
        | rewrite <- HeqS; apply ad_pat_consis__unit; exact H
        | exact Hmon | exact Hrig | exact Hwf
        | exact HΨfull | exact Hdisj | exact Hwfq ].
  - (* var *)
    destruct S0 as [ | nb | β | S1 S2 | S9 | ε9 S9 | | S9 | | S9 ];
      simpl in HeqS |- *; try discriminate HeqS.
    destruct (β == α) as [-> | Hneq].
    + eapply ad_pat_consis_precise_var_case with
        (Ψfull := Ψ) (Ψa := Ψna) (Δ := Δ);
        [ exact Htags | exact Hpre
        | rewrite <- HeqS; apply ad_pat_consis__var; [ exact H | exact H0 ]
        | exact Hmon | exact Hrig | exact Hwf
        | exact HΨfull | exact Hdisj | exact Hwfq ].
    + inversion HeqS; subst.
      apply ad_pat_consis__var;
        [ clear - H HΨfull; fsetdec | exact H0 ].
  - (* arrow *)
    destruct S0 as [ | nb | β | S1 S2 | S9 | ε9 S9 | | S9 | | S9 ];
      simpl in HeqS |- *; try discriminate HeqS.
    + destruct (β == α) as [-> | Hneq]; [ | discriminate HeqS ].
      eapply ad_pat_consis_precise_var_case with
        (Ψfull := Ψ) (Ψa := Ψna) (Δ := Δ);
        [ exact Htags | exact Hpre
        | rewrite <- HeqS;
          eapply ad_pat_consis__arrow; [ exact Hc1 | exact Hc2 | exact H ]
        | exact Hmon | exact Hrig | exact Hwf
        | exact HΨfull | exact Hdisj | exact Hwfq ].
    + inversion HeqS; subst.
      simpl in Hftag.
      simpl in Hwfq.
      inversion Hwfq as [ | | Θz Δz Pw1 Pw2 Hwfq1 Hwfq2 | | | ]; subst.
      eapply ad_pat_consis__arrow with
        (Ψ1 := AtomSetImpl.diff Ψ1 Ψ') (Ψ2 := AtomSetImpl.diff Ψ2 Ψ').
      * eapply IHHc1 with (S := S1) (Ψa := AtomSetImpl.inter Ψ1 Ψ');
          [ reflexivity | exact Hmon | exact Hrig | exact Hwf | exact Hαd
          | clear - Hdisj; fsetdec | clear - Hdisj; fsetdec
          | clear - Hdisj; fsetdec
          | clear - Hftag; fsetdec | exact Hwfq1 ].
      * eapply IHHc2 with (S := S2) (Ψa := AtomSetImpl.inter Ψ2 Ψ');
          [ reflexivity | exact Hmon | exact Hrig | exact Hwf | exact Hαd
          | clear - Hdisj; fsetdec | clear - Hdisj; fsetdec
          | clear - Hdisj; fsetdec
          | clear - Hftag; fsetdec | exact Hwfq2 ].
      * clear - H HΨfull HΨa Hdisj; fsetdec.
  - (* forall_inh_tagged *)
    destruct S0 as [ | nb | β | S1 S2 | S9 | ε9 S9 | | S9 | | S9 ];
      simpl in HeqS |- *; try discriminate HeqS.
    + destruct (β == α) as [-> | Hneq]; [ | discriminate HeqS ].
      eapply ad_pat_consis_precise_var_case with
        (Ψfull := Ψ) (Ψa := Ψna) (Δ := Δ);
        [ exact Htags | exact Hpre
        | rewrite <- HeqS;
          eapply ad_pat_consis__forall_inh_tagged with (L := L);
          [ exact H | exact H1 ]
        | exact Hmon | exact Hrig | exact Hwf
        | exact HΨfull | exact Hdisj | exact Hwfq ].
    + inversion HeqS; subst.
      simpl in Hftag.
      simpl in Hwfq. destruct (a_wf_pskl_all_inv Hwfq) as [Lw Hwbody].
      assert (Hεout : ε9 `notin` Ψ') by (clear - Hftag; fsetdec).
      assert (HεΨn : ε9 `in` Ψn)
        by (clear - H1 HΨfull HΨa Hεout; fsetdec).
      eapply ad_pat_consis__forall_inh_tagged with
        (L := L `union` Lw `union` dom Θ `union` singleton α)
        (Ψ0 := AtomSetImpl.diff Ψ0 Ψ').
      * intros X HX.
        assert (HXα : α <> X) by (clear - HX; fsetdec).
        rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
          [ | exact HXα | apply pskl_to_uskl_lc; exact HlcPa ].
        specialize (H0 X ltac:(clear - HX; fsetdec)).
        eapply H0 with (S := open_uskl_wrt_uskl S9 (uskl_var_f X))
                       (Ψa := AtomSetImpl.inter Ψ0 Ψ');
          [ apply subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
              [ exact HXα | exact Hlcψa ]
          | intros x b Hb; unfold binds; simpl; right; apply Hmon; exact Hb
          | intros Y HY; apply a_binds_tvar_weaken_cons; apply Hrig; exact HY
          | apply a_wf_aenv__tvar; [ clear - HX; fsetdec | exact Hwf ]
          | simpl; clear - Hαd HX; fsetdec
          | clear - Hdisj; fsetdec | clear - Hdisj; fsetdec
          | clear - Hdisj; fsetdec
          | pose proof (ftag_in_uskl_open_var S9 X) as Hov;
            clear - Hftag Hov; fsetdec
          | apply wf_open_of_all; apply Hwbody; clear - HX; fsetdec ].
      * clear - H1 HΨfull HΨa Hdisj HεΨn Hεout; fsetdec.
  - (* forall_inh_untagged *)
    destruct S0 as [ | nb | β | S1 S2 | S9 | ε9 S9 | | S9 | | S9 ];
      simpl in HeqS |- *; try discriminate HeqS.
    + destruct (β == α) as [-> | Hneq]; [ | discriminate HeqS ].
      eapply ad_pat_consis_precise_var_case with
        (Ψfull := Ψ) (Ψa := Ψna) (Δ := Δ);
        [ exact Htags | exact Hpre
        | rewrite <- HeqS;
          eapply ad_pat_consis__forall_inh_untagged with (L := L); exact H
        | exact Hmon | exact Hrig | exact Hwf
        | exact HΨfull | exact Hdisj | exact Hwfq ].
    + inversion HeqS; subst.
      simpl in Hftag.
      simpl in Hwfq. destruct (a_wf_pskl_all_inv Hwfq) as [Lw Hwbody].
      eapply ad_pat_consis__forall_inh_untagged with
        (L := L `union` Lw `union` dom Θ `union` singleton α).
      intros X HX.
      assert (HXα : α <> X) by (clear - HX; fsetdec).
      rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
        [ | exact HXα | apply pskl_to_uskl_lc; exact HlcPa ].
      specialize (H0 X ltac:(clear - HX; fsetdec)).
      eapply H0 with (S := open_uskl_wrt_uskl S9 (uskl_var_f X)) (Ψa := Ψna);
        [ apply subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
            [ exact HXα | exact Hlcψa ]
        | intros x b Hb; unfold binds; simpl; right; apply Hmon; exact Hb
        | intros Y HY; apply a_binds_tvar_weaken_cons; apply Hrig; exact HY
        | apply a_wf_aenv__tvar; [ clear - HX; fsetdec | exact Hwf ]
        | simpl; clear - Hαd HX; fsetdec
        | exact HΨfull | exact HΨa | exact Hdisj
        | pose proof (ftag_in_uskl_open_var S9 X) as Hov;
          clear - Hftag Hov; fsetdec
        | apply wf_open_of_all; apply Hwbody; clear - HX; fsetdec ].
  - (* forall_syn_tagged *)
    destruct S0 as [ | nb | β | S1 S2 | S9 | ε9 S9 | | S9 | | S9 ];
      simpl in HeqS |- *; try discriminate HeqS.
    + destruct (β == α) as [-> | Hneq]; [ | discriminate HeqS ].
      eapply ad_pat_consis_precise_var_case with
        (Ψfull := Ψ) (Ψa := Ψna) (Δ := Δ);
        [ exact Htags | exact Hpre
        | rewrite <- HeqS;
          eapply ad_pat_consis__forall_syn_tagged with (L := L); exact H
        | exact Hmon | exact Hrig | exact Hwf
        | exact HΨfull | exact Hdisj | exact Hwfq ].
    + inversion HeqS; subst.
      simpl in Hftag.
      simpl in Hwfq. destruct (a_wf_pskl_all_inv Hwfq) as [Lw Hwbody].
      eapply ad_pat_consis__forall_syn_tagged with
        (L := L `union` Lw `union` dom Θ `union` singleton α).
      intros X HX.
      assert (HXα : α <> X) by (clear - HX; fsetdec).
      rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
        [ | exact HXα | apply pskl_to_uskl_lc; exact HlcPa ].
      specialize (H0 X ltac:(clear - HX; fsetdec)).
      eapply H0 with (S := open_uskl_wrt_uskl S9 (uskl_var_f X)) (Ψa := Ψna);
        [ apply subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
            [ exact HXα | exact Hlcψa ]
        | intros x b Hb; unfold binds; simpl; right; apply Hmon; exact Hb
        | intros Y HY; apply a_binds_tvar_weaken_cons; apply Hrig; exact HY
        | apply a_wf_aenv__tvar; [ clear - HX; fsetdec | exact Hwf ]
        | simpl; clear - Hαd HX; fsetdec
        | exact HΨfull | exact HΨa | exact Hdisj
        | pose proof (ftag_in_uskl_open_var S9 X) as Hov;
          clear - Hftag Hov; fsetdec
        | apply wf_open_of_all; apply Hwbody; clear - HX; fsetdec ].
  - (* forall_syn *)
    destruct S0 as [ | nb | β | S1 S2 | S9 | ε9 S9 | | S9 | | S9 ];
      simpl in HeqS |- *; try discriminate HeqS.
    + destruct (β == α) as [-> | Hneq]; [ | discriminate HeqS ].
      eapply ad_pat_consis_precise_var_case with
        (Ψfull := Ψ) (Ψa := Ψna) (Δ := Δ);
        [ exact Htags | exact Hpre
        | rewrite <- HeqS;
          eapply ad_pat_consis__forall_syn with (L := L); exact H
        | exact Hmon | exact Hrig | exact Hwf
        | exact HΨfull | exact Hdisj | exact Hwfq ].
    + inversion HeqS; subst.
      simpl in Hftag.
      simpl in Hwfq. destruct (a_wf_pskl_all_inv Hwfq) as [Lw Hwbody].
      eapply ad_pat_consis__forall_syn with
        (L := L `union` Lw `union` dom Θ `union` singleton α).
      intros X HX.
      assert (HXα : α <> X) by (clear - HX; fsetdec).
      rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
        [ | exact HXα | apply pskl_to_uskl_lc; exact HlcPa ].
      specialize (H0 X ltac:(clear - HX; fsetdec)).
      eapply H0 with (S := open_uskl_wrt_uskl S9 (uskl_var_f X)) (Ψa := Ψna);
        [ apply subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
            [ exact HXα | exact Hlcψa ]
        | intros x b Hb; unfold binds; simpl; right; apply Hmon; exact Hb
        | intros Y HY; apply a_binds_tvar_weaken_cons; apply Hrig; exact HY
        | apply a_wf_aenv__tvar; [ clear - HX; fsetdec | exact Hwf ]
        | simpl; clear - Hαd HX; fsetdec
        | exact HΨfull | exact HΨa | exact Hdisj
        | pose proof (ftag_in_uskl_open_var S9 X) as Hov;
          clear - Hftag Hov; fsetdec
        | apply wf_open_of_all; apply Hwbody; clear - HX; fsetdec ].
  - (* ghostg *)
    destruct S0 as [ | nb | β | S1 S2 | S9 | ε9 S9 | | S9 | | S9 ];
      simpl in HeqS |- *; try discriminate HeqS.
    + destruct (β == α) as [-> | Hneq]; [ | discriminate HeqS ].
      eapply ad_pat_consis_precise_var_case with
        (Ψfull := Ψ) (Ψa := Ψna) (Δ := Δ);
        [ exact Htags | exact Hpre
        | rewrite <- HeqS; apply ad_pat_consis__ghostg; exact H
        | exact Hmon | exact Hrig | exact Hwf
        | exact HΨfull | exact Hdisj | exact Hwfq ].
    + apply ad_pat_consis__ghostg. clear - H HΨfull; fsetdec.
  - (* topholeg *)
    destruct S0 as [ | nb | β | S1 S2 | S9 | ε9 S9 | | S9 | | S9 ];
      simpl in HeqS |- *; try discriminate HeqS.
    + destruct (β == α) as [-> | Hneq]; [ | discriminate HeqS ].
      eapply ad_pat_consis_precise_var_case with
        (Ψfull := Ψ) (Ψa := Ψna) (Δ := Δ);
        [ exact Htags | exact Hpre
        | rewrite <- HeqS; apply ad_pat_consis__topholeg; exact Hc
        | exact Hmon | exact Hrig | exact Hwf
        | exact HΨfull | exact Hdisj | exact Hwfq ].
    + inversion HeqS; subst.
      simpl in Hftag.
      simpl in Hwfq. destruct (a_wf_pskl_tophole_inv Hwfq) as [Hg Hwb].
      apply ad_pat_consis__topholeg.
      eapply IHHc with (S := S9) (Ψa := Ψna);
        [ reflexivity | exact Hmon | exact Hrig | exact Hwf | exact Hαd
        | exact HΨfull | exact HΨa | exact Hdisj
        | clear - Hftag; fsetdec | exact Hwb ].
  - (* hole *)
    destruct S0 as [ | nb | β | S1 S2 | S9 | ε9 S9 | | S9 | | S9 ];
      simpl in HeqS |- *; try discriminate HeqS.
    + destruct (β == α) as [-> | Hneq]; [ | discriminate HeqS ].
      eapply ad_pat_consis_precise_var_case with
        (Ψfull := Ψ) (Ψa := Ψna) (Δ := Δ);
        [ exact Htags | exact Hpre
        | rewrite <- HeqS; apply ad_pat_consis__hole; [ exact H | exact H0 ]
        | exact Hmon | exact Hrig | exact Hwf
        | exact HΨfull | exact Hdisj | exact Hwfq ].
    + apply ad_pat_consis__hole;
        [ clear - H HΨfull; fsetdec | exact H0 ].
  - (* tophole *)
    destruct S0 as [ | nb | β | S1 S2 | S9 | ε9 S9 | | S9 | | S9 ];
      simpl in HeqS |- *; try discriminate HeqS.
    + destruct (β == α) as [-> | Hneq]; [ | discriminate HeqS ].
      eapply ad_pat_consis_precise_var_case with
        (Ψfull := Ψ) (Ψa := Ψna) (Δ := Δ);
        [ exact Htags | exact Hpre
        | rewrite <- HeqS; apply ad_pat_consis__tophole; exact Hc
        | exact Hmon | exact Hrig | exact Hwf
        | exact HΨfull | exact Hdisj | exact Hwfq ].
    + inversion HeqS; subst.
      simpl in Hftag.
      simpl in Hwfq. destruct (a_wf_pskl_tophole_inv Hwfq) as [Hg Hwb].
      apply ad_pat_consis__tophole.
      eapply IHHc with (S := S9) (Ψa := Ψna);
        [ reflexivity | exact Hmon | exact Hrig | exact Hwf | exact Hαd
        | exact HΨfull | exact HΨa | exact Hdisj
        | clear - Hftag; fsetdec | exact Hwb ].
  - (* tophole_inh *)
    destruct S0 as [ | nb | β | S1 S2 | S9 | ε9 S9 | | S9 | | S9 ];
      simpl in HeqS |- *; try discriminate HeqS.
    + destruct (β == α) as [-> | Hneq]; [ | discriminate HeqS ].
      eapply ad_pat_consis_precise_var_case with
        (Ψfull := Ψ) (Ψa := Ψna) (Δ := Δ);
        [ exact Htags | exact Hpre
        | rewrite <- HeqS;
          eapply ad_pat_consis__tophole_inh with (L := L); exact H
        | exact Hmon | exact Hrig | exact Hwf
        | exact HΨfull | exact Hdisj | exact Hwfq ].
    + inversion HeqS; subst.
      simpl in Hftag.
      simpl in Hwfq. destruct (a_wf_pskl_all_inv Hwfq) as [Lw Hwbody].
      eapply ad_pat_consis__tophole_inh with
        (L := L `union` Lw `union` dom Θ `union` singleton α).
      intros X HX.
      specialize (H0 X ltac:(clear - HX; fsetdec)).
      change (uskl_tophole (subst_bskl_in_uskl (pskl_to_uskl Pa) α S9))
        with (subst_bskl_in_uskl (pskl_to_uskl Pa) α (uskl_tophole S9)).
      eapply H0 with (S := uskl_tophole S9) (Ψa := Ψna);
        [ reflexivity
        | intros x b Hb; unfold binds; simpl; right; apply Hmon; exact Hb
        | intros Y HY; apply a_binds_tvar_weaken_cons; apply Hrig; exact HY
        | apply a_wf_aenv__tvar; [ clear - HX; fsetdec | exact Hwf ]
        | simpl; clear - Hαd HX; fsetdec
        | exact HΨfull | exact HΨa | exact Hdisj
        | clear - Hftag; simpl; fsetdec
        | apply wf_open_of_all; apply Hwbody; clear - HX; fsetdec ].
  - (* tophole_drop *)
    destruct S0 as [ | nb | β | S1 S2 | S9 | ε9 S9 | | S9 | | S9 ];
      simpl in HeqS |- *; try discriminate HeqS.
    + destruct (β == α) as [-> | Hneq]; [ | discriminate HeqS ].
      eapply ad_pat_consis_precise_var_case with
        (Ψfull := Ψ) (Ψa := Ψna) (Δ := Δ);
        [ exact Htags | exact Hpre
        | rewrite <- HeqS; apply ad_pat_consis__tophole_drop; exact Hc
        | exact Hmon | exact Hrig | exact Hwf
        | exact HΨfull | exact Hdisj | exact Hwfq ].
    + inversion HeqS; subst.
      simpl in Hftag.
      apply ad_pat_consis__tophole_drop.
      eapply IHHc with (S := S9) (Ψa := Ψna);
        [ reflexivity | exact Hmon | exact Hrig | exact Hwf | exact Hαd
        | exact HΨfull | exact HΨa | exact Hdisj
        | clear - Hftag; fsetdec | exact Hwfq ].
  - (* flex_l *)
    destruct S0 as [ | nb | β | S1 S2 | S9 | ε9 S9 | | S9 | | S9 ];
      simpl in HeqS |- *; try discriminate HeqS.
    destruct (β == α) as [-> | Hneq].
    + eapply ad_pat_consis_precise_var_case with
        (Ψfull := Ψ) (Ψa := Ψna) (Δ := Δ);
        [ exact Htags | exact Hpre
        | rewrite <- HeqS;
          eapply ad_pat_consis__flex_l; [ exact H | exact Hc ]
        | exact Hmon | exact Hrig | exact Hwf
        | exact HΨfull | exact Hdisj | exact Hwfq ].
    + inversion HeqS; subst.
      assert (Hfr : α `notin` ftvar_in_uskl (ptyp_to_uskl_syn τ)).
      { rewrite ftvar_in_uskl_ptyp_syn.
        assert (Hsc : ftvar_in_ptyp τ [<=] dom Θ)
          by (eapply a_wf_aenv_def_ftv_dom; [ exact Hwf | exact H ]).
        clear - Hαd Hsc; fsetdec. }
      eapply ad_pat_consis__flex_l; [ exact H | ].
      replace (ptyp_to_uskl_syn τ)
         with (subst_bskl_in_uskl (pskl_to_uskl Pa) α (ptyp_to_uskl_syn τ))
           by (apply subst_bskl_in_uskl_fresh_eq; exact Hfr).
      eapply IHHc with (S := ptyp_to_uskl_syn τ) (Ψa := Ψna);
        [ symmetry; apply subst_bskl_in_uskl_fresh_eq; exact Hfr
        | exact Hmon | exact Hrig | exact Hwf | exact Hαd
        | exact HΨfull | exact HΨa | exact Hdisj
        | pose proof (ftag_in_uskl_ptyp_syn τ) as Hpt; clear - Hpt; fsetdec
        | exact Hwfq ].
  - (* flex_r *)
    eapply ad_pat_consis__flex_r; [ exact H | ].
    eapply IHHc with (S := S0) (Ψa := Ψna);
      [ exact HeqS | exact Hmon | exact Hrig | exact Hwf | exact Hαd
      | exact HΨfull | exact HΨa | exact Hdisj | exact Hftag
      | replace (bskl_to_pskl (ptyp_to_bskl_syn τ)) with (ptyp_to_pskl τ)
          by (unfold ptyp_to_bskl_syn; rewrite bskl_to_pskl_pskl_to_bskl_syn;
              reflexivity);
        apply a_wf_pskl_mono_ptyp;
          [ eapply a_wf_aenv_binds_def_mono; eauto
          | eapply a_wf_aenv_binds_def_wf; eauto ] ].
Qed.
