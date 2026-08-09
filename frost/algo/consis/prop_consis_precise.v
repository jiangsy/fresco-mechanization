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
      [ad_pat_consis_refine_inh_gen], prop_soundness_sub.v), with the
      wf-carrying transporters it needs;
    - crux (1) [ad_pat_consis_subject_precise] = (1a);(1b);
    - step (2) [ad_pat_consis_precise_subst]: the general subject
      SUBSTITUTION [R[ψa/α] ∼ Q  ⇒  R[Pa/α] ∼ Q], by induction on the
      consistency derivation, whose [R = α] case is crux (1).  Its tag
      bookkeeping needs the syntactic-tag reading ([ftag_in_uskl],
      def_extra.v): the tag context is contained in the subject's tags
      ([ad_pat_consis_ftag_sub]), and the paper's [fresh Ψ'] side condition
      is rendered as disjointness from the subject's OTHER tags
      ([inter Ψ' (ftag R) = ∅]).  Consistency has no ForallL, so no new
      tags appear inside a derivation and the syntactic premise suffices —
      unlike the subtyping level (see prop_sub_complete.v §P5b-ii). *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.def_extra.
Require Import src.frost.coercions.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_skeleton.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.decorated_algo.def_decl_algo.
Require Import src.frost.decorated_algo.def_decorated.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.consis.prop_soundness_consis.
Require Import src.frost.algo.consis.prop_completeness_consis.
Require Import src.frost.algo.prop_mono_bridge.
Require Import src.frost.algo.prop_precise.
Require Import src.frost.decorated_algo.prop_decorate.
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
  forall Δ', (forall α, α `in` ftvar_in_pskl P -> α `in` Δ -> α `in` Δ') ->
  Θ ⨟ Δ' ⊢ₚₛᵃ P.
Proof.
  intros Θ Δ P H. induction H; intros Δ' Hnar; simpl in *.
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var.
    destruct H as [HΔ | Htv]; [ left; apply Hnar; [ clear; fsetdec | exact HΔ ] | right; exact Htv ].
  - apply a_wf_pskl__arrow;
      [ apply IHa_wf_pskl1 | apply IHa_wf_pskl2 ];
      intros α Hα HαΔ; apply Hnar; auto; clear - Hα; fsetdec.
  - apply a_wf_pskl__all with (L := L). intros α Hα.
    apply H0; [ exact Hα | ].
    intros β Hβ HβΔ.
    destruct (β == α) as [-> | Hne]; [ clear; fsetdec | ].
    assert (HβΔ0 : β `in` Δ) by (clear - HβΔ Hne; fsetdec).
    assert (HYP : β `in` ftvar_in_pskl P).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f α)) as Hup.
      simpl in Hup. clear - Hβ Hup Hne. fsetdec. }
    assert (β `in` Δ') by (apply Hnar; auto). clear - H1; fsetdec.
  - apply a_wf_pskl__hole.
  - apply a_wf_pskl__tophole; [ exact H | ].
    apply IHa_wf_pskl. clear; intros α Hα HXe; exact HXe.
Qed.

Lemma a_wf_pskl_delta_strip : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  Δ ∩ ftvar_in_pskl P [=] empty ->
  Θ ⨟ empty ⊢ₚₛᵃ P.
Proof.
  intros Θ Δ P H Hdis.
  eapply a_wf_pskl_delta_narrow; [ exact H | ].
  intros α Hα HαΔ. exfalso. clear - Hdis Hα HαΔ. fsetdec.
Qed.

(** Clean structural inversions of [d_tags_skl] (name-agnostic). *)
Lemma d_tags_skl_unit_inv : forall Ψ,
  d_tags_skl Ψ uskl_unit -> Ψ [=] empty.
Proof. intros Ψ H. inversion H; subst; auto. Qed.

Lemma d_tags_skl_var_inv : forall Ψ α,
  d_tags_skl Ψ (uskl_var_f α) -> Ψ [=] empty.
Proof. intros Ψ α H. inversion H; subst; auto. Qed.

Lemma d_tags_skl_arrow_inv : forall Ψ ψ1 ψ2,
  d_tags_skl Ψ (uskl_arrow ψ1 ψ2) ->
  exists Ψ1 Ψ2, d_tags_skl Ψ1 ψ1 /\ d_tags_skl Ψ2 ψ2
             /\ Ψ1 ∩ Ψ2 [=] empty /\ Ψ [=] Ψ1 `union` Ψ2.
Proof. intros Ψ ψ1 ψ2 H. inversion H; subst. eauto 10. Qed.

Lemma d_tags_skl_all_etag_inv : forall Ψ ε ψ,
  d_tags_skl Ψ (uskl_all_etag ε ψ) ->
  exists L Ψ0,
    (forall α, α `notin` L ->
       d_tags_skl Ψ0 (open_uskl_wrt_uskl ψ (uskl_var_f α)))
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
             /\ Ψ1 ∩ Ψ2 [=] empty /\ Ψ [=] Ψ1 `union` Ψ2.
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
    (forall α, α `notin` L ->
       a_tags_sort NM Ψ0 (open_uskl_wrt_uskl ψ (uskl_var_f α)))
    /\ ε `notin` Ψ0 /\ Ψ [=] add ε Ψ0.
Proof.
  intros NM Ψ ε ψ H. inversion H; subst.
  - (* sk *)
    match goal with Hit : is_tskl (uskl_all_etag _ _) |- _ =>
      inversion Hit; subst end.
    match goal with Hd : d_tags_skl _ (uskl_all_etag _ _) |- _ =>
      apply d_tags_skl_all_etag_inv in Hd as [Ld [Ψ0 [Hd0 [Hεt Hun]]]] end.
    match goal with Hit0 : forall α, α `notin` ?Li -> is_tskl _ |- _ =>
      exists (Li `union` Ld), Ψ0; repeat apply conj; try assumption;
      intros α Hα; apply a_tags_sort__sk; [ apply Hit0 | apply Hd0 ]; fsetdec end.
  - (* ty *)
    match goal with Hit : is_tskl (uskl_all_etag _ _) |- _ =>
      inversion Hit; subst end.
    match goal with Hd : d_tags_skl _ (uskl_all_etag _ _) |- _ =>
      apply d_tags_skl_all_etag_inv in Hd as [Ld [Ψ0 [Hd0 [Hεt Hun]]]] end.
    match goal with Hgf : uskl_ghost_free (uskl_all_etag _ _) |- _ =>
      inversion Hgf; subst end.
    match goal with
    | Hit0 : forall α, α `notin` ?Li -> is_tskl _,
      Hgf0 : forall α, α `notin` ?Lg -> uskl_ghost_free _ |- _ =>
      exists (Li `union` Lg `union` Ld), Ψ0; repeat apply conj; try assumption;
      intros α Hα;
      apply a_tags_sort__ty; [ apply Hit0 | apply Hd0 | apply Hgf0 ]; fsetdec
    end.
Qed.

(** Clean [a_wf_pskl] inversions (name-agnostic). *)
Lemma a_wf_pskl_all_inv : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ (pskl_all_syn P) ->
  exists L, forall α, α `notin` L ->
    Θ ⨟ (add α Δ) ⊢ₚₛᵃ (open_pskl_wrt_pskl P (pskl_var_f α)).
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
(*  target-side [ad_pat_consis_refine_inh_gen] (prop_soundness_sub.v).          *)
(* ===================================================================== *)

(** [strip ψ := pskl_to_uskl ⌊ψ⌋ˢ] commutes with opening. *)
Lemma strip_uskl_open : forall ψ α,
  pskl_to_uskl (uskl_to_pskl (open_uskl_wrt_uskl ψ (uskl_var_f α)))
  = open_uskl_wrt_uskl (pskl_to_uskl (uskl_to_pskl ψ)) (uskl_var_f α).
Proof.
  intros ψ α. rewrite uskl_to_pskl_open, pskl_to_uskl_open. reflexivity.
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
    intros α Hα. rewrite <- strip_uskl_open. exact (H0 α Hα).
  - eapply ad_pat_consis__forall_inh_untagged with (L := L).
    intros α Hα. rewrite <- strip_uskl_open. exact (H0 α Hα).
  - eapply ad_pat_consis__forall_syn with (L := L).
    intros α Hα. rewrite <- strip_uskl_open. exact (H0 α Hα).
  - eapply ad_pat_consis__forall_syn with (L := L).
    intros α Hα. rewrite <- strip_uskl_open. exact (H0 α Hα).
  - change bskl_hole with (pskl_to_bskl_inh pskl_hole).
    apply ad_pat_consis__hole; [ reflexivity | apply a_wf_pskl__hole ].
  - (* topholeg: stripping the dotted ghost yields a plain [tophole] *)
    apply ad_pat_consis__tophole. exact IHad_pat_consis.
  - apply ad_pat_consis__hole; [ reflexivity | exact H0 ].
  - apply ad_pat_consis__tophole. exact IHad_pat_consis.
  - eapply ad_pat_consis__tophole_inh with (L := L).
    intros α Hα. specialize (H0 α Hα). simpl in H0. exact H0.
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
    ([consis_forall/tophole_subject_transport], prop_completeness_consis.v (PART B)) cannot
    carry it, so these are genuine wf-variants, not duplicates. *)
Lemma consis_subj_transport_arrow_wf : forall Ψ Θ' R1 R2 R1' R2' Q,
  Ψ ⨟ Θ' ⊢ₛᵃ (uskl_arrow R1 R2) ∼ Q ->
  a_wf_aenv Θ' ->
  Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q) ->
  (forall Ψ1 Q1, Ψ1 ⨟ Θ' ⊢ₛᵃ R1 ∼ Q1 -> Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q1) ->
     Ψ1 ⨟ Θ' ⊢ₛᵃ R1' ∼ Q1) ->
  (forall Ψ2 Q2, Ψ2 ⨟ Θ' ⊢ₛᵃ R2 ∼ Q2 -> Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q2) ->
     Ψ2 ⨟ Θ' ⊢ₛᵃ R2' ∼ Q2) ->
  Ψ ⨟ Θ' ⊢ₛᵃ (uskl_arrow R1' R2') ∼ Q.
Proof.
  intros Ψ Θ' R1 R2 R1' R2' Q Hc Hwfa Hwfq Ht1 Ht2.
  remember (uskl_arrow R1 R2) as Ssub eqn:HR.
  revert Hwfq; induction Hc; try discriminate HR; intros Hwfq.
  - (* arrow: Q = bskl_arrow Q1 Q2 *)
    inversion HR; subst.
    simpl in Hwfq.
    inversion Hwfq as [ | | Θz Δz Pw1 Pw2 Hwfq1 Hwfq2 | | | ]; subst.
    apply ad_pat_consis__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2).
    + apply Ht1; assumption.
    + apply Ht2; assumption.
    + assumption.
  - (* flex_r: Q = bskl_var α ≔ τ; recurse at target [syn τ] *)
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    apply IHHc; [ exact HR | exact Hwfa | exact Ht1 | exact Ht2 | ].
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
Lemma wf_open_of_all : forall Θ Δ Q0 α,
  Θ ⨟ (add α Δ) ⊢ₚₛᵃ open_pskl_wrt_pskl (bskl_to_pskl Q0) (pskl_var_f α) ->
  ((α ~ abind_tvar) ++ Θ) ⨟ Δ
    ⊢ₚₛᵃ bskl_to_pskl (open_bskl_wrt_bskl Q0 (bskl_var_f α)).
Proof.
  intros Θ Δ Q0 α Hb.
  rewrite bskl_to_pskl_open.
  eapply a_wf_pskl_delta_narrow with (Δ := remove α (add α Δ)).
  - apply (a_wf_pskl_reassoc Hb α).
  - intros β2 Hβ2 HWin. clear - HWin. fsetdec.
Qed.

Lemma consis_forall_subject_transport_wf : forall Ψ Θ' R0 R0' Q L0,
  Ψ ⨟ Θ' ⊢ₛᵃ (uskl_all_syn R0) ∼ Q ->
  a_wf_aenv Θ' ->
  Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q) ->
  (forall α, α `notin` L0 -> forall Ψ' Q',
     Ψ' ⨟ ((α ~ abind_tvar) ++ Θ') ⊢ₛᵃ
       (open_uskl_wrt_uskl R0 (uskl_var_f α)) ∼ Q' ->
     ((α ~ abind_tvar) ++ Θ') ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q') ->
     Ψ' ⨟ ((α ~ abind_tvar) ++ Θ') ⊢ₛᵃ
       (open_uskl_wrt_uskl R0' (uskl_var_f α)) ∼ Q') ->
  Ψ ⨟ Θ' ⊢ₛᵃ (uskl_all_syn R0') ∼ Q.
Proof.
  intros Ψ Θ' R0 R0' Q L0 Hc Hwfa Hwfq Htr.
  remember (uskl_all_syn R0) as Ssub eqn:HR.
  revert Hwfq; induction Hc; try discriminate HR; intros Hwfq.
  - (* forall_inh_untagged: Q = bskl_all_inh Q0 *)
    inversion HR; subst.
    simpl in Hwfq. destruct (a_wf_pskl_all_inv Hwfq) as [Lw Hbody].
    apply ad_pat_consis__forall_inh_untagged with (L := L `union` L0 `union` Lw).
    intros α Hα.
    apply Htr; [ clear - Hα; fsetdec | apply H; clear - Hα; fsetdec | ].
    apply wf_open_of_all. apply Hbody. clear - Hα; fsetdec.
  - (* forall_syn: Q = bskl_all_syn Q0 *)
    inversion HR; subst.
    simpl in Hwfq. destruct (a_wf_pskl_all_inv Hwfq) as [Lw Hbody].
    apply ad_pat_consis__forall_syn with (L := L `union` L0 `union` Lw).
    intros α Hα.
    apply Htr; [ clear - Hα; fsetdec | apply H; clear - Hα; fsetdec | ].
    apply wf_open_of_all. apply Hbody. clear - Hα; fsetdec.
  - (* flex_r: Q = bskl_var α ≔ τ *)
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    apply IHHc; [ exact HR | exact Hwfa | exact Htr | ].
    replace (bskl_to_pskl (ptyp_to_bskl_syn τ)) with (ptyp_to_pskl τ)
      by (unfold ptyp_to_bskl_syn; rewrite bskl_to_pskl_pskl_to_bskl_syn;
          reflexivity).
    apply a_wf_pskl_mono_ptyp;
      [ eapply a_wf_aenv_binds_def_mono; eauto
      | eapply a_wf_aenv_binds_def_wf; eauto ].
Qed.

Lemma consis_tophole_subject_transport_wf : forall Ψ Θ' R Q,
  Ψ ⨟ Θ' ⊢ₛᵃ R ∼ Q ->
  a_wf_aenv Θ' ->
  Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q) ->
  forall R0 R0', R = uskl_tophole R0 ->
  (forall Θ'' Ψ' Q',
     a_wf_aenv Θ'' ->
     (forall x b, binds x b Θ' -> binds x b Θ'') ->
     Ψ' ⨟ Θ'' ⊢ₛᵃ R0 ∼ Q' ->
     Θ'' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q') ->
     Ψ' ⨟ Θ'' ⊢ₛᵃ R0' ∼ Q') ->
  Ψ ⨟ Θ' ⊢ₛᵃ (uskl_tophole R0') ∼ Q.
Proof.
  intros Ψ Θ' R Q Hc; induction Hc;
    intros HwfΘ Hwfq R0 R0' HeqS Htr; try discriminate HeqS.
  - (* tophole: Q = bskl_tophole Q0 *)
    inversion HeqS; subst.
    simpl in Hwfq. destruct (a_wf_pskl_tophole_inv Hwfq) as [Hg Hwfb].
    apply ad_pat_consis__tophole.
    apply (Htr Θ); [ exact HwfΘ | intros x b Hb; exact Hb | exact Hc | exact Hwfb ].
  - (* tophole_inh: Q = bskl_all_inh Q0, extended context *)
    inversion HeqS; subst.
    simpl in Hwfq. destruct (a_wf_pskl_all_inv Hwfq) as [Lw Hbody].
    apply ad_pat_consis__tophole_inh with (L := L `union` dom Θ `union` Lw).
    intros α Hα.
    assert (HwfX : a_wf_aenv ((α ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact HwfΘ ]).
    eapply (H0 α ltac:(clear - Hα; solve_notin_auto) HwfX).
    + apply wf_open_of_all. apply Hbody. clear - Hα; fsetdec.
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
    a general fact — a [∀◇] body cannot reference a Δ-var). *)
Lemma consis_concrete_target_inh : forall Ψ Θ R Q,
  Ψ ⨟ Θ ⊢ₛᵃ R ∼ Q ->
  a_wf_aenv Θ ->
  forall P, R = pskl_to_uskl P ->
  pskl_no_forall P ->
  Ψ [=] empty /\ pskl_to_bskl_inh (bskl_to_pskl Q) = Q.
Proof.
  intros Ψ Θ R Q Hc; induction Hc; intros Hwfa P0 HR Hnf.
  - (* unit *)  split; [ exact H | reflexivity ].
  - (* var *)   split; [ exact H | reflexivity ].
  - (* arrow *)
    destruct P0 as [ | n | αv | Pl Pr | Pq | | Pt ];
      simpl in HR; try discriminate HR. inversion HR; subst.
    simpl in Hnf; destruct Hnf as [Hnf1 Hnf2].
    destruct (IHHc1 Hwfa _ eq_refl Hnf1) as [HΨ1 Heq1].
    destruct (IHHc2 Hwfa _ eq_refl Hnf2) as [HΨ2 Heq2].
    split; [ fsetdec | simpl; rewrite Heq1, Heq2; reflexivity ].
  - (* forall_inh_tagged: subject all_etag — impossible *)
    destruct P0 as [ | n | αv | Pl Pr | Pq | | Pt ]; simpl in HR; discriminate HR.
  - (* forall_inh_untagged: subject all_syn ⇒ ¬nf *)
    destruct P0 as [ | n | αv | Pl Pr | Pq | | Pt ];
      simpl in HR; try discriminate HR. simpl in Hnf; contradiction.
  - (* forall_syn_tagged *)
    destruct P0 as [ | n | αv | Pl Pr | Pq | | Pt ]; simpl in HR; discriminate HR.
  - (* forall_syn ⇒ ¬nf *)
    destruct P0 as [ | n | αv | Pl Pr | Pq | | Pt ];
      simpl in HR; try discriminate HR. simpl in Hnf; contradiction.
  - (* ghostg *)
    destruct P0 as [ | n | αv | Pl Pr | Pq | | Pt ]; simpl in HR; discriminate HR.
  - (* topholeg *)
    destruct P0 as [ | n | αv | Pl Pr | Pq | | Pt ]; simpl in HR; discriminate HR.
  - (* hole *)
    split; [ exact H
           | simpl; rewrite bskl_to_pskl_pskl_to_bskl_inh; reflexivity ].
  - (* tophole: bskl_tophole Q0 *)
    destruct P0 as [ | n | αv | Pl Pr | Pq | | Pt ];
      simpl in HR; try discriminate HR. inversion HR; subst.
    simpl in Hnf.
    destruct (IHHc Hwfa _ eq_refl Hnf) as [HΨ0 Heq0].
    split; [ exact HΨ0 | simpl; rewrite Heq0; reflexivity ].
  - (* tophole_inh: bskl_all_inh Q0 — close the opened equation via open-inj *)
    destruct P0 as [ | n | αv | Pl Pr | Pq | | Pt ];
      simpl in HR; try discriminate HR. inversion HR; subst.
    simpl in Hnf.
    pick fresh α for (L `union` dom Θ `union` ftvar_in_bskl Q).
    assert (HwfX : a_wf_aenv ((α ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ fsetdec | exact Hwfa ]).
    destruct (H0 α ltac:(solve_notin_auto) HwfX (pskl_tophole Pt) eq_refl Hnf)
      as [HΨα HeqX].
    split; [ exact HΨα | ].
    simpl. f_equal.
    eapply open_bskl_wrt_bskl_inj with (α1 := α).
    + rewrite ftvar_in_bskl_inh, ftvar_bskl_to_pskl. fsetdec.
    + fsetdec.
    + rewrite <- pskl_to_bskl_inh_open, <- bskl_to_pskl_open. exact HeqX.
  - (* tophole_drop: Q arbitrary *)
    destruct P0 as [ | n | αv | Pl Pr | Pq | | Pt ];
      simpl in HR; try discriminate HR. inversion HR; subst.
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
    destruct (IHHc Hwfa P0 HR Hnf) as [HΨ _].
    split; [ exact HΨ | reflexivity ].
Qed.


(** Monotonicity of [a_binds_tvar] under context extension. *)
Lemma a_binds_tvar_mono : forall α Θ Θ',
  a_binds_tvar α Θ ->
  (forall x b, binds x b Θ -> binds x b Θ') ->
  a_binds_tvar α Θ'.
Proof.
  intros α Θ Θ' H Hmon. unfold a_binds_tvar in *.
  destruct H as [Hb | [Hb | [τ Hb]]];
    [ left | right; left | right; right; exists τ ]; apply Hmon; exact Hb.
Qed.

(** (1b) — SUBJECT-REFINEMENT preserves consistency.  If [Ptgt] refines to
    [Psrc] ([Psrc] ghostier), then any [Q] consistent with the FILLED subject
    [Ptgt] is consistent with the GHOSTIER subject [Psrc].  Well-formedness of
    the (erased) target is THREADED as an input (the hole reconstruction needs
    it; see [consis_concrete_target_inh]).  Subject-side mirror of the target
    template [ad_pat_consis_refine_inh_gen] (prop_soundness_sub.v). *)
Lemma ad_pat_consis_subject_refine : forall Θ Δ Qsrc Qtgt,
  ad_refine_syn Θ Δ Qsrc Qtgt ->
  forall Psrc Ptgt, Qsrc = pskl_to_bskl_inh Psrc -> Qtgt = pskl_to_bskl_inh Ptgt ->
  forall Θ',
  (forall x b, binds x b Θ -> binds x b Θ') ->
  (forall α0, α0 `in` Δ -> a_binds_tvar α0 Θ') ->
  a_wf_aenv Θ' ->
  forall Ψ Q,
    Ψ ⨟ Θ' ⊢ₛᵃ (pskl_to_uskl Ptgt) ∼ Q ->
    Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q) ->
    Ψ ⨟ Θ' ⊢ₛᵃ (pskl_to_uskl Psrc) ∼ Q.
Proof.
  intros Θ Δ Qsrc Qtgt Hr.
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
  - (* all: Qsrc = all_inh R0, Qtgt = all_inh T0 (Δ grows under the binder) *)
    destruct Psrc as [ | | | | Ps0 | | ]; simpl in HSrc; try discriminate HSrc.
    destruct Ptgt as [ | | | | Pt0 | | ]; simpl in HTgt; try discriminate HTgt.
    inversion HSrc; inversion HTgt; subst.
    simpl. simpl in Hc.
    eapply consis_forall_subject_transport_wf
      with (R0 := pskl_to_uskl Pt0) (R0' := pskl_to_uskl Ps0)
           (L0 := L `union` dom Θ' `union` Δ);
      [ exact Hc | exact Hwf' | exact Hwfq | ].
    intros α0 Hα0 Ψ' Q' Hc' Hwfq'.
    rewrite <- pskl_to_uskl_open_var.
    rewrite <- pskl_to_uskl_open_var in Hc'.
    eapply (H0 α0 ltac:(clear - Hα0; solve_notin_auto)
              (open_pskl_wrt_pskl Ps0 (pskl_var_f α0))
              (open_pskl_wrt_pskl Pt0 (pskl_var_f α0)));
      [ symmetry; apply pskl_to_bskl_inh_open
      | symmetry; apply pskl_to_bskl_inh_open
      | intros x b Hb; unfold binds; simpl; right; apply Hmon; exact Hb
      | intros β HβΔ; destruct (β == α0) as [ -> | Hne ];
          [ left; unfold binds; simpl; left; reflexivity
          | apply a_binds_tvar_weaken_cons; apply Hrig;
            clear - HβΔ Hne; fsetdec ]
      | apply a_wf_aenv__tvar; [ clear - Hα0; fsetdec | exact Hwf' ]
      | exact Hc'
      | exact Hwfq' ].
  - (* hole: Qsrc = bskl_hole, Qtgt = syn P (∀-free) *)
    destruct Psrc; simpl in HSrc; try discriminate HSrc.
    assert (Hnf : pskl_no_forall Ptgt)
      by (eapply inh_eq_syn_no_forall; symmetry; exact HTgt).
    destruct (consis_concrete_target_inh Hc Hwf' Ptgt eq_refl Hnf) as [HΨ Heqinh].
    simpl. rewrite <- Heqinh.
    apply ad_pat_consis__hole; [ exact HΨ | exact Hwfq ].
  - (* tophole_remove: Qsrc = ∀◇ R0, Qtgt = P (same); drop the ∀◇ *)
    destruct Psrc as [ | | | | | | Ps0 ]; simpl in HSrc; try discriminate HSrc.
    inversion HSrc; subst.
    simpl. apply ad_pat_consis__tophole_drop.
    eapply IHHr;
      [ reflexivity | reflexivity | exact Hmon | exact Hrig | exact Hwf'
      | exact Hc | exact Hwfq ].
  - (* tophole_fill: Qtgt = all_syn P — impossible for an inh painting *)
    destruct Ptgt; simpl in HTgt; try discriminate HTgt.
  - (* tophole_keep: Qsrc = ∀◇ R0, Qtgt = ∀◇ T0 *)
    destruct Psrc as [ | | | | | | Ps0 ]; simpl in HSrc; try discriminate HSrc.
    destruct Ptgt as [ | | | | | | Pt0 ]; simpl in HTgt; try discriminate HTgt.
    inversion HSrc; inversion HTgt; subst.
    simpl. simpl in Hc.
    eapply consis_tophole_subject_transport_wf
      with (R0 := pskl_to_uskl Pt0) (R0' := pskl_to_uskl Ps0);
      [ exact Hc | exact Hwf' | exact Hwfq | reflexivity | ].
    intros Θ'' Ψ' Q' Hwf'' Hincl'' Hc'' Hwfq''.
    eapply IHHr with (Ptgt := Pt0);
      [ reflexivity | reflexivity
      | intros x b Hb; apply Hincl''; apply Hmon; exact Hb
      | intros β HβΔ; eapply a_binds_tvar_mono;
          [ apply Hrig; exact HβΔ | exact Hincl'' ]
      | exact Hwf'' | exact Hc'' | exact Hwfq'' ].
  - (* flex_l: Qsrc = bskl_var α (α ≔ τ), premise syn τ ⊳ Qtgt *)
    destruct Psrc as [ | | α0 | | | | ]; simpl in HSrc; try discriminate HSrc.
    inversion HSrc; subst.
    assert (Hmτ : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf' | apply Hmon; exact H ]).
    simpl. eapply ad_pat_consis__flex_l; [ apply Hmon; exact H | ].
    replace (ptyp_to_uskl_syn τ) with (pskl_to_uskl (ptyp_to_pskl τ))
      by (apply pskl_to_uskl_ptyp).
    eapply IHHr with (Ptgt := Ptgt);
      [ symmetry; apply (mono_inh_eq_syn Hmτ) | reflexivity
      | exact Hmon | exact Hrig | exact Hwf' | exact Hc | exact Hwfq ].
  - (* flex_r: Qtgt = bskl_var α (α ≔ τ), premise Qsrc ⊳ syn τ *)
    destruct Ptgt as [ | | α0 | | | | ]; simpl in HTgt; try discriminate HTgt.
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
  (forall α, α `in` Δ -> a_binds_tvar α Θ) ->
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
(*  Step (2) infrastructure — syntactic tags [ftag_in_uskl] (def_extra.v). *)
(* ===================================================================== *)

Lemma ftag_in_uskl_open_rec_var : forall α' R k,
  ftag_in_uskl (open_uskl_wrt_uskl_rec k (uskl_var_f α') R) [=] ftag_in_uskl R.
Proof.
  intros α' R; induction R; intros k; simpl; try fsetdec.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; fsetdec.
  - pose proof (IHR1 k); pose proof (IHR2 k); fsetdec.
  - pose proof (IHR (S k)); fsetdec.
  - pose proof (IHR (S k)); fsetdec.
  - pose proof (IHR k); fsetdec.
  - pose proof (IHR k); fsetdec.
Qed.

Lemma ftag_in_uskl_open_var : forall R α,
  ftag_in_uskl (open_uskl_wrt_uskl R (uskl_var_f α)) [=] ftag_in_uskl R.
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
      pick fresh α for L;
      pose proof (H0 α ltac:(solve_notin_auto)) as Hα;
      pose proof (ftag_in_uskl_open_var R α) as Hov
    end; fsetdec.
Qed.

(** The consistency tag context is contained in the SUBJECT's syntactic
    tags — every solved tag is consumed at an [all_etag] node of the
    subject.  (Syntactic counterpart of [ad_partial_precise_tags_sub],
    prop_sub_complete.v; the precision-substitution crux uses it to pin
    the residual tag context of a wholly-[ψa] subject to ∅.) *)
Lemma ad_pat_consis_ftag_sub : forall Ψ Θ R' Q,
  Ψ ⨟ Θ ⊢ₛᵃ R' ∼ Q ->
  Ψ [<=] ftag_in_uskl R'.
Proof.
  intros Ψ Θ R' Q H; induction H; simpl; try fsetdec.
  - (* forall_inh_tagged *)
    match goal with |- _ [<=] add _ (ftag_in_uskl ?R) =>
      pick fresh α for L;
      pose proof (H0 α ltac:(solve_notin_auto)) as Hα;
      pose proof (ftag_in_uskl_open_var R α) as Hov
    end; fsetdec.
  - (* forall_inh_untagged *)
    match goal with |- _ [<=] ftag_in_uskl ?R =>
      pick fresh α for L;
      pose proof (H0 α ltac:(solve_notin_auto)) as Hα;
      pose proof (ftag_in_uskl_open_var R α) as Hov
    end; fsetdec.
  - (* forall_syn_tagged *)
    match goal with |- _ [<=] add _ (ftag_in_uskl ?R) =>
      pick fresh α for L;
      pose proof (H0 α ltac:(solve_notin_auto)) as Hα;
      pose proof (ftag_in_uskl_open_var R α) as Hov
    end; fsetdec.
  - (* forall_syn *)
    match goal with |- _ [<=] ftag_in_uskl ?R =>
      pick fresh α for L;
      pose proof (H0 α ltac:(solve_notin_auto)) as Hα;
      pose proof (ftag_in_uskl_open_var R α) as Hov
    end; fsetdec.
  - (* tophole_inh: subject fixed under the target binder *)
    pick fresh α for L;
    pose proof (H0 α ltac:(solve_notin_auto)) as Hα; simpl in Hα; fsetdec.
  - (* flex_l: the unfolded def is a painted monotype — tag-free *)
    match goal with H0 : _ [<=] ftag_in_uskl (ptyp_to_uskl_syn ?t) |- _ =>
      pose proof (ftag_in_uskl_ptyp_syn t) end; fsetdec.
Qed.

(* ===================================================================== *)
(*  Step (2) — the [R = α] crux case, packaged: a wholly-[ψa] subject      *)
(*  transports to [Pa] with residual tag context ∅ (= Ψ).                  *)
(* ===================================================================== *)

Lemma ad_pat_consis_precise_var_case : forall NM Ψ' Θb Δ ψa Pa,
  a_tags_sort NM Ψ' ψa ->
  Θb ⨟ Δ ⊢ₚᵣᵃ Pa ⊑ (uskl_to_pskl ψa) ->
  forall Ψfull Θ' Qc Ψ Ψa,
  Ψfull ⨟ Θ' ⊢ₛᵃ ψa ∼ Qc ->
  (forall x b, binds x b Θb -> binds x b Θ') ->
  (forall α, α `in` Δ -> a_binds_tvar α Θ') ->
  a_wf_aenv Θ' ->
  Ψfull [=] Ψ `union` Ψa ->
  Ψ' ∩ Ψ [=] empty ->
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
(*  subject's other syntactic tags [ftag_in_uskl R] — without the latter,  *)
(*  a tag shared between an [all_etag] of [R] and one of [ψa] makes the    *)
(*  conclusion underivable (the [R]-node is forced to re-consume a tag     *)
(*  that substitution removed).  Consistency derivations introduce no new  *)
(*  tags (no ForallL), so the syntactic premise is stable under the        *)
(*  induction.                                                             *)
(* ===================================================================== *)

Lemma ad_pat_consis_precise_subst : forall Θb Δ α ψa Pa Ψ' NM,
  lc_uskl ψa ->
  lc_pskl Pa ->
  a_tags_sort NM Ψ' ψa ->
  Θb ⨟ Δ ⊢ₚᵣᵃ Pa ⊑ (uskl_to_pskl ψa) ->
  forall Ψfull Θ' Rsub Qc,
  Ψfull ⨟ Θ' ⊢ₛᵃ Rsub ∼ Qc ->
  forall R Ψ Ψa,
  Rsub = subst_uskl_in_uskl ψa α R ->
  (forall x b, binds x b Θb -> binds x b Θ') ->
  (forall α0, α0 `in` Δ -> a_binds_tvar α0 Θ') ->
  a_wf_aenv Θ' ->
  α `notin` dom Θ' ->
  Ψfull [=] Ψ `union` Ψa ->
  Ψa [<=] Ψ' ->
  Ψ' ∩ Ψ [=] empty ->
  Ψ' ∩ ftag_in_uskl R [=] empty ->
  Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Qc) ->
  Ψ ⨟ Θ' ⊢ₛᵃ (subst_uskl_in_uskl (pskl_to_uskl Pa) α R) ∼ Qc.
Proof.
  intros Θb Δ α ψa Pa Ψ' NM Hlcψa HlcPa Htags Hpre.
  intros Ψfull Θ' Rsub Qc Hc.
  induction Hc;
    intros R00 Ψn Ψna HeqS Hmon Hrig Hwf Hαd HΨfull HΨa Hdisj Hftag Hwfq.
  - (* unit *)
    destruct R00 as [ | nb | β | R01 R02 | R09 | ε9 R09 | | R09 | | R09 ];
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
    destruct R00 as [ | nb | β | R01 R02 | R09 | ε9 R09 | | R09 | | R09 ];
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
    destruct R00 as [ | nb | β | R01 R02 | R09 | ε9 R09 | | R09 | | R09 ];
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
        (Ψ1 := Ψ1 ∖ Ψ') (Ψ2 := Ψ2 ∖ Ψ').
      * eapply IHHc1 with (R := R01) (Ψa := Ψ1 ∩ Ψ');
          [ reflexivity | exact Hmon | exact Hrig | exact Hwf | exact Hαd
          | clear - Hdisj; fsetdec | clear - Hdisj; fsetdec
          | clear - Hdisj; fsetdec
          | clear - Hftag; fsetdec | exact Hwfq1 ].
      * eapply IHHc2 with (R := R02) (Ψa := Ψ2 ∩ Ψ');
          [ reflexivity | exact Hmon | exact Hrig | exact Hwf | exact Hαd
          | clear - Hdisj; fsetdec | clear - Hdisj; fsetdec
          | clear - Hdisj; fsetdec
          | clear - Hftag; fsetdec | exact Hwfq2 ].
      * clear - H HΨfull HΨa Hdisj; fsetdec.
  - (* forall_inh_tagged *)
    destruct R00 as [ | nb | β | R01 R02 | R09 | ε9 R09 | | R09 | | R09 ];
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
        (Ψ0 := Ψ0 ∖ Ψ').
      * intros α0 Hα0.
        assert (Hα0α : α <> α0) by (clear - Hα0; fsetdec).
        rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
          [ | exact Hα0α | apply pskl_to_uskl_lc; exact HlcPa ].
        specialize (H0 α0 ltac:(clear - Hα0; solve_notin_auto)).
        eapply H0 with (R := open_uskl_wrt_uskl R09 (uskl_var_f α0))
                       (Ψa := Ψ0 ∩ Ψ');
          [ apply subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
              [ exact Hα0α | exact Hlcψa ]
          | intros x b Hb; unfold binds; simpl; right; apply Hmon; exact Hb
          | intros β Hβ; apply a_binds_tvar_weaken_cons; apply Hrig; exact Hβ
          | apply a_wf_aenv__tvar; [ clear - Hα0; fsetdec | exact Hwf ]
          | simpl; clear - Hαd Hα0; fsetdec
          | clear - Hdisj; fsetdec | clear - Hdisj; fsetdec
          | clear - Hdisj; fsetdec
          | pose proof (ftag_in_uskl_open_var R09 α0) as Hov;
            clear - Hftag Hov; fsetdec
          | apply wf_open_of_all; apply Hwbody; clear - Hα0; fsetdec ].
      * clear - H1 HΨfull HΨa Hdisj HεΨn Hεout; fsetdec.
  - (* forall_inh_untagged *)
    destruct R00 as [ | nb | β | R01 R02 | R09 | ε9 R09 | | R09 | | R09 ];
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
      intros α0 Hα0.
      assert (Hα0α : α <> α0) by (clear - Hα0; fsetdec).
      rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
        [ | exact Hα0α | apply pskl_to_uskl_lc; exact HlcPa ].
      specialize (H0 α0 ltac:(clear - Hα0; solve_notin_auto)).
      eapply H0 with (R := open_uskl_wrt_uskl R09 (uskl_var_f α0)) (Ψa := Ψna);
        [ apply subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
            [ exact Hα0α | exact Hlcψa ]
        | intros x b Hb; unfold binds; simpl; right; apply Hmon; exact Hb
        | intros β Hβ; apply a_binds_tvar_weaken_cons; apply Hrig; exact Hβ
        | apply a_wf_aenv__tvar; [ clear - Hα0; fsetdec | exact Hwf ]
        | simpl; clear - Hαd Hα0; fsetdec
        | exact HΨfull | exact HΨa | exact Hdisj
        | pose proof (ftag_in_uskl_open_var R09 α0) as Hov;
          clear - Hftag Hov; fsetdec
        | apply wf_open_of_all; apply Hwbody; clear - Hα0; fsetdec ].
  - (* forall_syn_tagged *)
    destruct R00 as [ | nb | β | R01 R02 | R09 | ε9 R09 | | R09 | | R09 ];
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
      intros α0 Hα0.
      assert (Hα0α : α <> α0) by (clear - Hα0; fsetdec).
      rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
        [ | exact Hα0α | apply pskl_to_uskl_lc; exact HlcPa ].
      specialize (H0 α0 ltac:(clear - Hα0; solve_notin_auto)).
      eapply H0 with (R := open_uskl_wrt_uskl R09 (uskl_var_f α0)) (Ψa := Ψna);
        [ apply subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
            [ exact Hα0α | exact Hlcψa ]
        | intros x b Hb; unfold binds; simpl; right; apply Hmon; exact Hb
        | intros β Hβ; apply a_binds_tvar_weaken_cons; apply Hrig; exact Hβ
        | apply a_wf_aenv__tvar; [ clear - Hα0; fsetdec | exact Hwf ]
        | simpl; clear - Hαd Hα0; fsetdec
        | exact HΨfull | exact HΨa | exact Hdisj
        | pose proof (ftag_in_uskl_open_var R09 α0) as Hov;
          clear - Hftag Hov; fsetdec
        | apply wf_open_of_all; apply Hwbody; clear - Hα0; fsetdec ].
  - (* forall_syn *)
    destruct R00 as [ | nb | β | R01 R02 | R09 | ε9 R09 | | R09 | | R09 ];
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
      intros α0 Hα0.
      assert (Hα0α : α <> α0) by (clear - Hα0; fsetdec).
      rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
        [ | exact Hα0α | apply pskl_to_uskl_lc; exact HlcPa ].
      specialize (H0 α0 ltac:(clear - Hα0; solve_notin_auto)).
      eapply H0 with (R := open_uskl_wrt_uskl R09 (uskl_var_f α0)) (Ψa := Ψna);
        [ apply subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
            [ exact Hα0α | exact Hlcψa ]
        | intros x b Hb; unfold binds; simpl; right; apply Hmon; exact Hb
        | intros β Hβ; apply a_binds_tvar_weaken_cons; apply Hrig; exact Hβ
        | apply a_wf_aenv__tvar; [ clear - Hα0; fsetdec | exact Hwf ]
        | simpl; clear - Hαd Hα0; fsetdec
        | exact HΨfull | exact HΨa | exact Hdisj
        | pose proof (ftag_in_uskl_open_var R09 α0) as Hov;
          clear - Hftag Hov; fsetdec
        | apply wf_open_of_all; apply Hwbody; clear - Hα0; fsetdec ].
  - (* ghostg *)
    destruct R00 as [ | nb | β | R01 R02 | R09 | ε9 R09 | | R09 | | R09 ];
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
    destruct R00 as [ | nb | β | R01 R02 | R09 | ε9 R09 | | R09 | | R09 ];
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
      eapply IHHc with (R := R09) (Ψa := Ψna);
        [ reflexivity | exact Hmon | exact Hrig | exact Hwf | exact Hαd
        | exact HΨfull | exact HΨa | exact Hdisj
        | clear - Hftag; fsetdec | exact Hwb ].
  - (* hole *)
    destruct R00 as [ | nb | β | R01 R02 | R09 | ε9 R09 | | R09 | | R09 ];
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
    destruct R00 as [ | nb | β | R01 R02 | R09 | ε9 R09 | | R09 | | R09 ];
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
      eapply IHHc with (R := R09) (Ψa := Ψna);
        [ reflexivity | exact Hmon | exact Hrig | exact Hwf | exact Hαd
        | exact HΨfull | exact HΨa | exact Hdisj
        | clear - Hftag; fsetdec | exact Hwb ].
  - (* tophole_inh *)
    destruct R00 as [ | nb | β | R01 R02 | R09 | ε9 R09 | | R09 | | R09 ];
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
      intros α0 Hα0.
      specialize (H0 α0 ltac:(clear - Hα0; solve_notin_auto)).
      change (uskl_tophole (subst_uskl_in_uskl (pskl_to_uskl Pa) α R09))
        with (subst_uskl_in_uskl (pskl_to_uskl Pa) α (uskl_tophole R09)).
      eapply H0 with (R := uskl_tophole R09) (Ψa := Ψna);
        [ reflexivity
        | intros x b Hb; unfold binds; simpl; right; apply Hmon; exact Hb
        | intros β Hβ; apply a_binds_tvar_weaken_cons; apply Hrig; exact Hβ
        | apply a_wf_aenv__tvar; [ clear - Hα0; fsetdec | exact Hwf ]
        | simpl; clear - Hαd Hα0; fsetdec
        | exact HΨfull | exact HΨa | exact Hdisj
        | clear - Hftag; simpl; fsetdec
        | apply wf_open_of_all; apply Hwbody; clear - Hα0; fsetdec ].
  - (* tophole_drop *)
    destruct R00 as [ | nb | β | R01 R02 | R09 | ε9 R09 | | R09 | | R09 ];
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
      eapply IHHc with (R := R09) (Ψa := Ψna);
        [ reflexivity | exact Hmon | exact Hrig | exact Hwf | exact Hαd
        | exact HΨfull | exact HΨa | exact Hdisj
        | clear - Hftag; fsetdec | exact Hwfq ].
  - (* flex_l *)
    destruct R00 as [ | nb | β | R01 R02 | R09 | ε9 R09 | | R09 | | R09 ];
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
         with (subst_uskl_in_uskl (pskl_to_uskl Pa) α (ptyp_to_uskl_syn τ))
           by (apply subst_uskl_in_uskl_fresh_eq; exact Hfr).
      eapply IHHc with (R := ptyp_to_uskl_syn τ) (Ψa := Ψna);
        [ symmetry; apply subst_uskl_in_uskl_fresh_eq; exact Hfr
        | exact Hmon | exact Hrig | exact Hwf | exact Hαd
        | exact HΨfull | exact HΨa | exact Hdisj
        | pose proof (ftag_in_uskl_ptyp_syn τ) as Hpt; clear - Hpt; fsetdec
        | exact Hwfq ].
  - (* flex_r *)
    eapply ad_pat_consis__flex_r; [ exact H | ].
    eapply IHHc with (R := R00) (Ψa := Ψna);
      [ exact HeqS | exact Hmon | exact Hrig | exact Hwf | exact Hαd
      | exact HΨfull | exact HΨa | exact Hdisj | exact Hftag
      | replace (bskl_to_pskl (ptyp_to_bskl_syn τ)) with (ptyp_to_pskl τ)
          by (unfold ptyp_to_bskl_syn; rewrite bskl_to_pskl_pskl_to_bskl_syn;
              reflexivity);
        apply a_wf_pskl_mono_ptyp;
          [ eapply a_wf_aenv_binds_def_mono; eauto
          | eapply a_wf_aenv_binds_def_wf; eauto ] ].
Qed.

(* ===================================================================== *)
(*  ⊑ᵤ — decorated subject-precision [uskl_precise] (DESIGN §5.4).        *)
(*                                                                         *)
(*  Relates a GHOSTIER subject [R'] to a subject [R] whose decorated       *)
(*  fragments it replaces by (paintings of) more-precise plain skeletons.  *)
(*  This is the induction-ready generalization of the subst-form           *)
(*  [R[Pa/α] vs R[ψa/α]]: the subst-form is too weak for its own ForallL   *)
(*  crux (the instantiated body changes wholesale, not at var positions),  *)
(*  while ⊑ᵤ is closed under instantiation ([uskl_precise_subst]).         *)
(*                                                                         *)
(*  The index [Ψrep] collects the tags of the REPLACED decorated parts —   *)
(*  exactly the tags that vanish from the subject, hence the amount by     *)
(*  which the consistency/subtyping tag context drops.                     *)
(*                                                                         *)
(*  Rule design mirrors the refinement ([ad_refine_syn] on inh-paintings)  *)
(*  re-matched against DECORATED structure, plus a REFL rule for the       *)
(*  identical decorated fragments (previous instantiations) that           *)
(*  substitution leaves on both sides.  [tophole_fill] has NO mirror: the  *)
(*  ⊑-target is an inh-painting, whose head is never [all_syn], so fill    *)
(*  cannot occur in a precision derivation.                                *)
(* ===================================================================== *)

Inductive uskl_precise (Θ : aenv) : atoms -> uskl -> uskl -> Prop :=
| upre__refl : forall Ψrep R,
    lc_uskl R ->
    Ψrep [=] empty ->
    uskl_precise Θ Ψrep R R
| upre__arrow : forall Ψrep Ψ1 Ψ2 R1' R2' R1 R2,
    uskl_precise Θ Ψ1 R1' R1 ->
    uskl_precise Θ Ψ2 R2' R2 ->
    Ψrep [=] Ψ1 `union` Ψ2 ->
    uskl_precise Θ Ψrep (uskl_arrow R1' R2') (uskl_arrow R1 R2)
| upre__all_syn : forall L Ψrep R' R,
    (forall α, α `notin` L ->
       uskl_precise Θ Ψrep
         (open_uskl_wrt_uskl R' (uskl_var_f α))
         (open_uskl_wrt_uskl R (uskl_var_f α))) ->
    uskl_precise Θ Ψrep (uskl_all_syn R') (uskl_all_syn R)
| upre__all_etag : forall L Ψrep ε R' R,
    (forall α, α `notin` L ->
       uskl_precise Θ Ψrep
         (open_uskl_wrt_uskl R' (uskl_var_f α))
         (open_uskl_wrt_uskl R (uskl_var_f α))) ->
    uskl_precise Θ Ψrep (uskl_all_etag ε R') (uskl_all_etag ε R)
| upre__all_inst : forall L Ψrep Ψ0 ε R' R,
    (forall α, α `notin` L ->
       uskl_precise Θ Ψ0
         (open_uskl_wrt_uskl R' (uskl_var_f α))
         (open_uskl_wrt_uskl R (uskl_var_f α))) ->
    Ψrep [=] add ε Ψ0 ->
    uskl_precise Θ Ψrep (uskl_all_syn R') (uskl_all_etag ε R)
| upre__tophole : forall Ψrep R' R,
    uskl_precise Θ Ψrep R' R ->
    uskl_precise Θ Ψrep (uskl_tophole R') (uskl_tophole R)
| upre__topholeg : forall Ψrep R' R,
    uskl_precise Θ Ψrep R' R ->
    uskl_precise Θ Ψrep (uskl_topholeg R') (uskl_topholeg R)
| upre__tophole_keepg : forall Ψrep R' R,
    uskl_precise Θ Ψrep R' R ->
    uskl_precise Θ Ψrep (uskl_tophole R') (uskl_topholeg R)
| upre__hole : forall Ψrep R,
    Ψrep [=] empty ->
    pskl_no_forall (uskl_to_pskl R) ->
    Θ ⨟ empty ⊢ₚₛᵃ (uskl_to_pskl R) ->
    uskl_precise Θ Ψrep uskl_hole R
| upre__tophole_remove : forall Ψrep R' R,
    uskl_precise Θ Ψrep R' R ->
    uskl_precise Θ Ψrep (uskl_tophole R') R
| upre__flex_l : forall Ψrep α τ R,
    binds α (abind_flex_mono_def τ) Θ ->
    uskl_precise Θ Ψrep (ptyp_to_uskl_syn τ) R ->
    uskl_precise Θ Ψrep (uskl_var_f α) R
| upre__flex_r : forall Ψrep α τ R',
    binds α (abind_flex_mono_def τ) Θ ->
    uskl_precise Θ Ψrep R' (ptyp_to_uskl_syn τ) ->
    uskl_precise Θ Ψrep R' (uskl_var_f α).

(** Re-tag under set equality. *)
Lemma uskl_precise_psi_cong : forall Θ Ψrep R' R,
  uskl_precise Θ Ψrep R' R ->
  forall Ψrep', Ψrep [=] Ψrep' ->
  uskl_precise Θ Ψrep' R' R.
Proof.
  intros Θ Ψrep R' R H; induction H; intros Ψrep' Heq.
  - apply upre__refl; [ assumption | fsetdec ].
  - eapply upre__arrow; [ exact H | exact H0 | fsetdec ].
  - eapply upre__all_syn with (L := L); intros α Hα; eauto.
  - eapply upre__all_etag with (L := L); intros α Hα; eauto.
  - eapply upre__all_inst with (L := L) (Ψ0 := Ψ0);
      [ intros α Hα; eauto | fsetdec ].
  - apply upre__tophole; eauto.
  - apply upre__topholeg; eauto.
  - apply upre__tophole_keepg; eauto.
  - apply upre__hole; [ fsetdec | assumption | assumption ].
  - apply upre__tophole_remove; eauto.
  - eapply upre__flex_l; eauto.
  - eapply upre__flex_r; eauto.
Qed.

(** The ghostier side has no more tags. *)
Lemma uskl_precise_ftag_sub : forall Θ Ψrep R' R,
  uskl_precise Θ Ψrep R' R ->
  ftag_in_uskl R' [<=] ftag_in_uskl R.
Proof.
  intros Θ Ψrep R' R H; induction H; simpl; try fsetdec.
  - (* all_syn cong *)
    pick fresh α for L.
    pose proof (H0 α ltac:(solve_notin_auto)) as Hα.
    pose proof (ftag_in_uskl_open_var R' α).
    pose proof (ftag_in_uskl_open_var R α).
    fsetdec.
  - (* all_etag cong *)
    pick fresh α for L.
    pose proof (H0 α ltac:(solve_notin_auto)) as Hα.
    pose proof (ftag_in_uskl_open_var R' α).
    pose proof (ftag_in_uskl_open_var R α).
    fsetdec.
  - (* all_inst *)
    pick fresh α for L.
    pose proof (H0 α ltac:(solve_notin_auto)) as Hα.
    pose proof (ftag_in_uskl_open_var R' α).
    pose proof (ftag_in_uskl_open_var R α).
    fsetdec.
  - (* flex_r *)
    pose proof (ftag_in_uskl_ptyp_syn τ). fsetdec.
Qed.

(** ∀-free erasure ⇒ no tags (all_etag erases to a quantifier). *)
Lemma no_forall_uskl_ftag : forall ψ,
  pskl_no_forall (uskl_to_pskl ψ) ->
  ftag_in_uskl ψ [=] empty.
Proof.
  induction ψ; simpl; intros H; try fsetdec.
  - destruct H as [H1 H2].
    pose proof (IHψ1 H1); pose proof (IHψ2 H2); fsetdec.
  - pose proof (IHψ H); fsetdec.
  - pose proof (IHψ H); fsetdec.
Qed.

(** Syn-painting is injective. *)
Lemma pskl_to_bskl_syn_inj : forall P Q,
  pskl_to_bskl_syn P = pskl_to_bskl_syn Q -> P = Q.
Proof.
  induction P; intros Q Heq; destruct Q; simpl in Heq;
    try discriminate Heq; inversion Heq; subst; f_equal; auto.
Qed.

(** ⊑ᵤ is closed under instantiating a rigid variable by a (decorated)
    skeleton on BOTH sides — the ForallL-crux enabler.  The hole rule
    survives because its target is wf in the EMPTY Δ, hence [α]-free. *)
Lemma uskl_precise_subst : forall Θ Ψrep R' R,
  uskl_precise Θ Ψrep R' R ->
  forall α' ψs,
  lc_uskl ψs ->
  a_wf_aenv Θ ->
  α' `notin` dom Θ ->
  uskl_precise Θ Ψrep
    (subst_uskl_in_uskl ψs α' R') (subst_uskl_in_uskl ψs α' R).
Proof.
  intros Θ Ψrep R' R Hup; induction Hup; intros α0 ψs Hlc Hwf Hα; simpl.
  - (* refl *)
    apply upre__refl;
      [ apply subst_uskl_in_uskl_lc_uskl; assumption | assumption ].
  - (* arrow *)
    eapply upre__arrow;
      [ apply IHHup1; assumption | apply IHHup2; assumption | assumption ].
  - (* all_syn cong *)
    apply upre__all_syn with (L := L `union` singleton α0).
    intros β Hβ.
    assert (HYX : α0 <> β) by (clear - Hβ; fsetdec).
    rewrite (subst_uskl_in_uskl_open_uskl_wrt_uskl_var R' ψs α0 β HYX Hlc).
    rewrite (subst_uskl_in_uskl_open_uskl_wrt_uskl_var R ψs α0 β HYX Hlc).
    apply H0; [ clear - Hβ; fsetdec | exact Hlc | exact Hwf | exact Hα ].
  - (* all_etag cong *)
    apply upre__all_etag with (L := L `union` singleton α0).
    intros β Hβ.
    assert (HYX : α0 <> β) by (clear - Hβ; fsetdec).
    rewrite (subst_uskl_in_uskl_open_uskl_wrt_uskl_var R' ψs α0 β HYX Hlc).
    rewrite (subst_uskl_in_uskl_open_uskl_wrt_uskl_var R ψs α0 β HYX Hlc).
    apply H0; [ clear - Hβ; fsetdec | exact Hlc | exact Hwf | exact Hα ].
  - (* all_inst *)
    apply upre__all_inst with (L := L `union` singleton α0) (Ψ0 := Ψ0);
      [ | assumption ].
    intros β Hβ.
    assert (HYX : α0 <> β) by (clear - Hβ; fsetdec).
    rewrite (subst_uskl_in_uskl_open_uskl_wrt_uskl_var R' ψs α0 β HYX Hlc).
    rewrite (subst_uskl_in_uskl_open_uskl_wrt_uskl_var R ψs α0 β HYX Hlc).
    apply H0; [ clear - Hβ; fsetdec | exact Hlc | exact Hwf | exact Hα ].
  - (* tophole cong *)
    apply upre__tophole; apply IHHup; assumption.
  - (* topholeg cong *)
    apply upre__topholeg; apply IHHup; assumption.
  - (* tophole_keepg *)
    apply upre__tophole_keepg; apply IHHup; assumption.
  - (* hole *)
    assert (Hfr : α0 `notin` ftvar_in_uskl R).
    { pose proof (a_wf_pskl_ftv_dom H1) as Hsc.
      rewrite ftvar_in_pskl_uskl_to_pskl in Hsc.
      clear - Hsc Hα. fsetdec. }
    rewrite (subst_uskl_in_uskl_fresh_eq R ψs α0 Hfr).
    apply upre__hole; assumption.
  - (* tophole_remove *)
    apply upre__tophole_remove; apply IHHup; assumption.
  - (* flex_l *)
    assert (Hdom : α `in` dom Θ) by (eapply binds_In; exact H).
    destruct_if as [-> | Hne]; [ exfalso; clear - Hdom Hα; fsetdec | ].
    eapply upre__flex_l; [ exact H | ].
    assert (Hfrτ : α0 `notin` ftvar_in_uskl (ptyp_to_uskl_syn τ)).
    { rewrite ftvar_in_uskl_ptyp_syn.
      assert (Hsc : ftvar_in_ptyp τ [<=] dom Θ)
        by (eapply a_wf_aenv_def_ftv_dom; [ exact Hwf | exact H ]).
      clear - Hsc Hα; fsetdec. }
    pose proof (IHHup α0 ψs Hlc Hwf Hα) as Hrec.
    rewrite (subst_uskl_in_uskl_fresh_eq (ptyp_to_uskl_syn τ) ψs α0 Hfrτ)
      in Hrec.
    exact Hrec.
  - (* flex_r *)
    assert (Hdom : α `in` dom Θ) by (eapply binds_In; exact H).
    destruct_if as [-> | Hne]; [ exfalso; clear - Hdom Hα; fsetdec | ].
    eapply upre__flex_r; [ exact H | ].
    assert (Hfrτ : α0 `notin` ftvar_in_uskl (ptyp_to_uskl_syn τ)).
    { rewrite ftvar_in_uskl_ptyp_syn.
      assert (Hsc : ftvar_in_ptyp τ [<=] dom Θ)
        by (eapply a_wf_aenv_def_ftv_dom; [ exact Hwf | exact H ]).
      clear - Hsc Hα; fsetdec. }
    pose proof (IHHup α0 ψs Hlc Hwf Hα) as Hrec.
    rewrite (subst_uskl_in_uskl_fresh_eq (ptyp_to_uskl_syn τ) ψs α0 Hfrτ)
      in Hrec.
    exact Hrec.
Qed.


(** EMBEDDING: plain precision [Pa ⊑ ⌊ψ⌋] against a DECORATED [ψ] lifts to
    ⊑ᵤ, with [Ψrep] = ψ's tag reading (all of ψ's decorations are replaced
    by the painting).  Induction on the refinement derivation, re-matching
    erasure structure against decorated structure ([all_syn]↔[all_etag],
    [tophole]↔[topholeg]); [tophole_fill] cannot occur (the ⊑-target is an
    inh-painting, never [all_syn]-headed). *)
Lemma uskl_precise_of_precise : forall Θ Δ Qsrc Qtgt,
  ad_refine_syn Θ Δ Qsrc Qtgt ->
  a_wf_aenv Θ ->
  forall Pa ψt Ψt,
  Qsrc = pskl_to_bskl_inh Pa ->
  Qtgt = pskl_to_bskl_inh (uskl_to_pskl ψt) ->
  is_tskl ψt ->
  d_tags_skl Ψt ψt ->
  uskl_precise Θ Ψt (pskl_to_uskl Pa) ψt.
Proof.
  intros Θ Δ Qsrc Qtgt Hr; induction Hr;
    intros Hwf Pa ψt Ψt HSrc HTgt Htsk Hdt.
  - (* unit *)
    destruct Pa; simpl in HSrc; try discriminate HSrc.
    destruct ψt; simpl in HTgt; try discriminate HTgt.
    simpl. apply upre__refl;
      [ auto | exact (d_tags_skl_unit_inv Hdt) ].
  - (* var *)
    destruct Pa; simpl in HSrc; try discriminate HSrc.
    destruct ψt; simpl in HTgt; try discriminate HTgt.
    inversion HSrc; inversion HTgt; subst.
    simpl. apply upre__refl;
      [ auto | exact (d_tags_skl_var_inv Hdt) ].
  - (* arrow *)
    destruct Pa as [ | n | α0 | Pa1 Pa2 | Pa0 | | Pa0 ];
      simpl in HSrc; try discriminate HSrc.
    destruct ψt; simpl in HTgt; try discriminate HTgt.
    inversion HSrc; inversion HTgt; subst.
    inversion Htsk; subst.
    apply d_tags_skl_arrow_inv in Hdt
      as [Ψa1 [Ψa2 [Hd1 [Hd2 [Hdisj Hun]]]]].
    simpl.
    eapply upre__arrow;
      [ eapply IHHr1; try reflexivity; try eassumption
      | eapply IHHr2; try reflexivity; try eassumption
      | exact Hun ].
  - (* all: Pa = all_syn Pa0, ψt = all_etag ε ψ0 *)
    destruct Pa as [ | n | α0 | Pa1 Pa2 | Pa0 | | Pa0 ];
      simpl in HSrc; try discriminate HSrc.
    destruct ψt as [ | n | α0 | ψ1 ψ2 | ψ0 | ε ψ0 | | ψ0 | | ψ0 ];
      simpl in HTgt; try discriminate HTgt;
      [ inversion Htsk | ].
    inversion HSrc; inversion HTgt; subst.
    inversion Htsk as [ | | | Lt ε' ψ0' Ht0 | | ]; subst.
    apply d_tags_skl_all_etag_inv in Hdt
      as [Ld [Ψ0d [Hd0 [Hε Hun]]]].
    simpl.
    apply upre__all_inst with (L := L `union` Lt `union` Ld) (Ψ0 := Ψ0d);
      [ | exact Hun ].
    intros α Hα.
    rewrite <- pskl_to_uskl_open_var.
    specialize (H0 α ltac:(clear - Hα; solve_notin_auto) Hwf).
    eapply H0 with (ψt := open_uskl_wrt_uskl ψ0 (uskl_var_f α));
      [ symmetry; apply pskl_to_bskl_inh_open
      | rewrite uskl_to_pskl_open; symmetry; apply pskl_to_bskl_inh_open
      | apply Ht0; clear - Hα; fsetdec
      | apply Hd0; clear - Hα; fsetdec ].
  - (* hole *)
    destruct Pa; simpl in HSrc; try discriminate HSrc.
    assert (Hnf : pskl_no_forall (uskl_to_pskl ψt))
      by (eapply inh_eq_syn_no_forall; symmetry; exact HTgt).
    assert (HeqP : P = uskl_to_pskl ψt).
    { apply pskl_to_bskl_syn_inj.
      rewrite HTgt.
      apply pskl_no_forall_inh_eq_syn. exact Hnf. }
    simpl. apply upre__hole.
    + pose proof (d_tags_skl_ftag Hdt) as Htg.
      pose proof (no_forall_uskl_ftag _ Hnf) as Hfe.
      clear - Htg Hfe; fsetdec.
    + exact Hnf.
    + rewrite HeqP in H. exact H.
  - (* tophole_remove *)
    destruct Pa as [ | n | α0 | Pa1 Pa2 | Pa0 | | Pa0 ];
      simpl in HSrc; try discriminate HSrc.
    inversion HSrc; subst.
    simpl. apply upre__tophole_remove.
    eapply IHHr; try reflexivity; try eassumption.
  - (* tophole_fill: an inh-painting is never all_syn-headed *)
    destruct ψt; simpl in HTgt; discriminate HTgt.
  - (* tophole_keep: ψt = topholeg ψ0 *)
    destruct Pa as [ | n | α0 | Pa1 Pa2 | Pa0 | | Pa0 ];
      simpl in HSrc; try discriminate HSrc.
    destruct ψt as [ | n | α0 | ψ1 ψ2 | ψ0 | ε ψ0 | | ψ0 | | ψ0 ];
      simpl in HTgt; try discriminate HTgt;
      [ inversion Htsk | ].
    inversion HSrc; inversion HTgt; subst.
    inversion Htsk; subst.
    apply d_tags_skl_topholeg_inv in Hdt.
    simpl. apply upre__tophole_keepg.
    eapply IHHr; try reflexivity; try eassumption.
  - (* flex_l *)
    destruct Pa as [ | n | α0 | Pa1 Pa2 | Pa0 | | Pa0 ];
      simpl in HSrc; try discriminate HSrc.
    inversion HSrc; subst.
    assert (Hm : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf | exact H ]).
    simpl. eapply upre__flex_l; [ exact H | ].
    rewrite <- pskl_to_uskl_ptyp.
    eapply IHHr;
      [ exact Hwf
      | symmetry; apply (mono_inh_eq_syn Hm)
      | reflexivity | exact Htsk | exact Hdt ].
  - (* flex_r: ψt = var α *)
    destruct ψt as [ | n | α0 | ψ1 ψ2 | ψ0 | ε ψ0 | | ψ0 | | ψ0 ];
      simpl in HTgt; try discriminate HTgt.
    inversion HTgt; subst.
    assert (Hm : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf | exact H ]).
    eapply uskl_precise_psi_cong with (Ψrep := empty);
      [ | pose proof (d_tags_skl_var_inv Hdt); fsetdec ].
    eapply upre__flex_r; [ exact H | ].
    eapply IHHr;
      [ exact Hwf
      | reflexivity
      | rewrite uskl_to_pskl_ptyp_to_uskl_syn;
        symmetry; apply (mono_inh_eq_syn Hm)
      | apply mono_ptyp_to_uskl_syn_is_tskl; exact Hm
      | apply (mono_ptyp_to_uskl_syn_tags Hm); reflexivity ].
Qed.

(* ===================================================================== *)
(*  (2') — consistency transport over ⊑ᵤ.                                 *)
(*                                                                         *)
(*  [consis_split_transport Θb Ψsup A B] packages: any consistency of the  *)
(*  subject A transports to B, with the tag context dropping by its        *)
(*  Ψsup-portion.  The per-shape transporters below run the inner          *)
(*  induction on the consistency derivation (handling the subject-         *)
(*  preserving rules [flex_r]/[tophole_inh]); the main lemma               *)
(*  [ad_pat_consis_precise_upre] inducts on ⊑ᵤ and packages its IHs into   *)
(*  the functional.  [Ψsup] over-approximates the replaced tags UNIFORMLY  *)
(*  (it is fixed across congruences), which is what makes the arrow case   *)
(*  compositional.                                                         *)
(* ===================================================================== *)

Definition consis_split_transport (Θb : aenv) (Ψsup : atoms) (A B : uskl) :=
  forall Θ' Ψfull Ψn Ψna Q,
    Ψfull ⨟ Θ' ⊢ₛᵃ A ∼ Q ->
    (forall x b, binds x b Θb -> binds x b Θ') ->
    a_wf_aenv Θ' ->
    Ψfull [=] Ψn `union` Ψna ->
    Ψna [<=] Ψsup ->
    Ψsup ∩ Ψn [=] empty ->
    Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q) ->
    Ψn ⨟ Θ' ⊢ₛᵃ B ∼ Q.

Lemma consis_split_transport_arrow : forall Θb Ψsup R1 R2 R1' R2',
  consis_split_transport Θb Ψsup R1 R1' ->
  consis_split_transport Θb Ψsup R2 R2' ->
  consis_split_transport Θb Ψsup (uskl_arrow R1 R2) (uskl_arrow R1' R2').
Proof.
  intros Θb Ψsup R1 R2 R1' R2' Ht1 Ht2.
  intros Θ' Ψfull Ψn Ψna Q Hc Hmon Hwf HΨf HΨa Hdisj Hwfq.
  remember (uskl_arrow R1 R2) as Ssub eqn:HeqS.
  revert Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  induction Hc; try discriminate HeqS;
    intros Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  - (* arrow *)
    inversion HeqS; subst.
    simpl in Hwfq.
    inversion Hwfq as [ | | Θz Δz Pw1 Pw2 Hwfq1 Hwfq2 | | | ]; subst.
    eapply ad_pat_consis__arrow with
      (Ψ1 := Ψ1 ∖ Ψsup) (Ψ2 := Ψ2 ∖ Ψsup).
    + eapply Ht1 with (Ψna := Ψ1 ∩ Ψsup);
        [ exact Hc1 | exact Hmon | exact Hwf
        | clear - Hdisj; fsetdec | clear - Hdisj; fsetdec
        | clear - Hdisj; fsetdec | exact Hwfq1 ].
    + eapply Ht2 with (Ψna := Ψ2 ∩ Ψsup);
        [ exact Hc2 | exact Hmon | exact Hwf
        | clear - Hdisj; fsetdec | clear - Hdisj; fsetdec
        | clear - Hdisj; fsetdec | exact Hwfq2 ].
    + clear - H HΨf HΨa Hdisj; fsetdec.
  - (* flex_r: the target unfolds a flexible definition *)
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    apply (IHHc HeqS Ψn Ψna HΨf HΨa Hdisj Hmon Hwf).
    replace (bskl_to_pskl (ptyp_to_bskl_syn τ)) with (ptyp_to_pskl τ)
      by (unfold ptyp_to_bskl_syn; rewrite bskl_to_pskl_pskl_to_bskl_syn;
          reflexivity).
    apply a_wf_pskl_mono_ptyp;
      [ eapply a_wf_aenv_binds_def_mono; eauto
      | eapply a_wf_aenv_binds_def_wf; eauto ].
Qed.

Lemma consis_split_transport_all_syn : forall Θb Ψsup R0 R0' L0,
  (forall α, α `notin` L0 ->
     consis_split_transport Θb Ψsup
       (open_uskl_wrt_uskl R0 (uskl_var_f α))
       (open_uskl_wrt_uskl R0' (uskl_var_f α))) ->
  consis_split_transport Θb Ψsup (uskl_all_syn R0) (uskl_all_syn R0').
Proof.
  intros Θb Ψsup R0 R0' L0 Ht.
  intros Θ' Ψfull Ψn Ψna Q Hc Hmon Hwf HΨf HΨa Hdisj Hwfq.
  remember (uskl_all_syn R0) as Ssub eqn:HeqS.
  revert Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  induction Hc; try discriminate HeqS;
    intros Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  - (* forall_inh_untagged: target all_inh, context unchanged *)
    inversion HeqS; subst.
    simpl in Hwfq. destruct (a_wf_pskl_all_inv Hwfq) as [Lw Hwbody].
    eapply ad_pat_consis__forall_inh_untagged with
      (L := L `union` L0 `union` Lw `union` dom Θ).
    intros α Hα.
    eapply (Ht α ltac:(clear - Hα; solve_notin_auto)) with (Ψna := Ψna);
      [ apply H; clear - Hα; fsetdec
      | intros x b Hb; unfold binds; simpl; right; apply Hmon; exact Hb
      | apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ]
      | exact HΨf | exact HΨa | exact Hdisj
      | apply wf_open_of_all; apply Hwbody; clear - Hα; fsetdec ].
  - (* forall_syn: target all_syn, context unchanged *)
    inversion HeqS; subst.
    simpl in Hwfq. destruct (a_wf_pskl_all_inv Hwfq) as [Lw Hwbody].
    eapply ad_pat_consis__forall_syn with
      (L := L `union` L0 `union` Lw `union` dom Θ).
    intros α Hα.
    eapply (Ht α ltac:(clear - Hα; solve_notin_auto)) with (Ψna := Ψna);
      [ apply H; clear - Hα; fsetdec
      | intros x b Hb; unfold binds; simpl; right; apply Hmon; exact Hb
      | apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ]
      | exact HΨf | exact HΨa | exact Hdisj
      | apply wf_open_of_all; apply Hwbody; clear - Hα; fsetdec ].
  - (* flex_r *)
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    apply (IHHc HeqS Ψn Ψna HΨf HΨa Hdisj Hmon Hwf).
    replace (bskl_to_pskl (ptyp_to_bskl_syn τ)) with (ptyp_to_pskl τ)
      by (unfold ptyp_to_bskl_syn; rewrite bskl_to_pskl_pskl_to_bskl_syn;
          reflexivity).
    apply a_wf_pskl_mono_ptyp;
      [ eapply a_wf_aenv_binds_def_mono; eauto
      | eapply a_wf_aenv_binds_def_wf; eauto ].
Qed.

Lemma consis_split_transport_all_etag_cong : forall Θb Ψsup ε R0 R0' L0,
  ε `notin` Ψsup ->
  (forall α, α `notin` L0 ->
     consis_split_transport Θb Ψsup
       (open_uskl_wrt_uskl R0 (uskl_var_f α))
       (open_uskl_wrt_uskl R0' (uskl_var_f α))) ->
  consis_split_transport Θb Ψsup (uskl_all_etag ε R0) (uskl_all_etag ε R0').
Proof.
  intros Θb Ψsup ε R0 R0' L0 Hεout Ht.
  intros Θ' Ψfull Ψn Ψna Q Hc Hmon Hwf HΨf HΨa Hdisj Hwfq.
  remember (uskl_all_etag ε R0) as Ssub eqn:HeqS.
  revert Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  induction Hc; try discriminate HeqS;
    intros Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  - (* forall_inh_tagged: consumes ε *)
    inversion HeqS; subst.
    simpl in Hwfq. destruct (a_wf_pskl_all_inv Hwfq) as [Lw Hwbody].
    assert (HεΨn : ε `in` Ψn)
      by (clear - H1 HΨf HΨa Hεout; fsetdec).
    eapply ad_pat_consis__forall_inh_tagged with
      (L := L `union` L0 `union` Lw `union` dom Θ)
      (Ψ0 := Ψ0 ∖ Ψsup).
    + intros α Hα.
      eapply (Ht α ltac:(clear - Hα; solve_notin_auto))
        with (Ψna := Ψ0 ∩ Ψsup);
        [ apply H; clear - Hα; fsetdec
        | intros x b Hb; unfold binds; simpl; right; apply Hmon; exact Hb
        | apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ]
        | clear - Hdisj; fsetdec | clear - Hdisj; fsetdec
        | clear - Hdisj; fsetdec
        | apply wf_open_of_all; apply Hwbody; clear - Hα; fsetdec ].
    + clear - H1 HΨf HΨa Hdisj HεΨn Hεout; fsetdec.
  - (* forall_syn_tagged: context passes through *)
    inversion HeqS; subst.
    simpl in Hwfq. destruct (a_wf_pskl_all_inv Hwfq) as [Lw Hwbody].
    eapply ad_pat_consis__forall_syn_tagged with
      (L := L `union` L0 `union` Lw `union` dom Θ).
    intros α Hα.
    eapply (Ht α ltac:(clear - Hα; solve_notin_auto)) with (Ψna := Ψna);
      [ apply H; clear - Hα; fsetdec
      | intros x b Hb; unfold binds; simpl; right; apply Hmon; exact Hb
      | apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ]
      | exact HΨf | exact HΨa | exact Hdisj
      | apply wf_open_of_all; apply Hwbody; clear - Hα; fsetdec ].
  - (* flex_r *)
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    apply (IHHc HeqS Ψn Ψna HΨf HΨa Hdisj Hmon Hwf).
    replace (bskl_to_pskl (ptyp_to_bskl_syn τ)) with (ptyp_to_pskl τ)
      by (unfold ptyp_to_bskl_syn; rewrite bskl_to_pskl_pskl_to_bskl_syn;
          reflexivity).
    apply a_wf_pskl_mono_ptyp;
      [ eapply a_wf_aenv_binds_def_mono; eauto
      | eapply a_wf_aenv_binds_def_wf; eauto ].
Qed.

Lemma consis_split_transport_all_inst : forall Θb Ψsup ε R0 R0' L0,
  ε `in` Ψsup ->
  (forall α, α `notin` L0 ->
     consis_split_transport Θb Ψsup
       (open_uskl_wrt_uskl R0 (uskl_var_f α))
       (open_uskl_wrt_uskl R0' (uskl_var_f α))) ->
  consis_split_transport Θb Ψsup (uskl_all_etag ε R0) (uskl_all_syn R0').
Proof.
  intros Θb Ψsup ε R0 R0' L0 Hεin Ht.
  intros Θ' Ψfull Ψn Ψna Q Hc Hmon Hwf HΨf HΨa Hdisj Hwfq.
  remember (uskl_all_etag ε R0) as Ssub eqn:HeqS.
  revert Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  induction Hc; try discriminate HeqS;
    intros Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  - (* forall_inh_tagged → forall_inh_untagged (ε vanishes into Ψna) *)
    inversion HeqS; subst.
    simpl in Hwfq. destruct (a_wf_pskl_all_inv Hwfq) as [Lw Hwbody].
    eapply ad_pat_consis__forall_inh_untagged with
      (L := L `union` L0 `union` Lw `union` dom Θ).
    intros α Hα.
    eapply (Ht α ltac:(clear - Hα; solve_notin_auto))
      with (Ψna := Ψ0 ∩ Ψsup);
      [ apply H; clear - Hα; fsetdec
      | intros x b Hb; unfold binds; simpl; right; apply Hmon; exact Hb
      | apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ]
      | clear - H1 HΨf HΨa Hdisj Hεin; fsetdec
      | clear - Hdisj; fsetdec
      | clear - Hdisj; fsetdec
      | apply wf_open_of_all; apply Hwbody; clear - Hα; fsetdec ].
  - (* forall_syn_tagged → forall_syn (context passes through) *)
    inversion HeqS; subst.
    simpl in Hwfq. destruct (a_wf_pskl_all_inv Hwfq) as [Lw Hwbody].
    eapply ad_pat_consis__forall_syn with
      (L := L `union` L0 `union` Lw `union` dom Θ).
    intros α Hα.
    eapply (Ht α ltac:(clear - Hα; solve_notin_auto)) with (Ψna := Ψna);
      [ apply H; clear - Hα; fsetdec
      | intros x b Hb; unfold binds; simpl; right; apply Hmon; exact Hb
      | apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ]
      | exact HΨf | exact HΨa | exact Hdisj
      | apply wf_open_of_all; apply Hwbody; clear - Hα; fsetdec ].
  - (* flex_r *)
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    apply (IHHc HeqS Ψn Ψna HΨf HΨa Hdisj Hmon Hwf).
    replace (bskl_to_pskl (ptyp_to_bskl_syn τ)) with (ptyp_to_pskl τ)
      by (unfold ptyp_to_bskl_syn; rewrite bskl_to_pskl_pskl_to_bskl_syn;
          reflexivity).
    apply a_wf_pskl_mono_ptyp;
      [ eapply a_wf_aenv_binds_def_mono; eauto
      | eapply a_wf_aenv_binds_def_wf; eauto ].
Qed.

Lemma consis_split_transport_tophole : forall Θb Ψsup R0 R0',
  consis_split_transport Θb Ψsup R0 R0' ->
  consis_split_transport Θb Ψsup (uskl_tophole R0) (uskl_tophole R0').
Proof.
  intros Θb Ψsup R0 R0' Ht.
  intros Θ' Ψfull Ψn Ψna Q Hc Hmon Hwf HΨf HΨa Hdisj Hwfq.
  remember (uskl_tophole R0) as Ssub eqn:HeqS.
  revert Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  induction Hc; try discriminate HeqS;
    intros Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  - (* tophole: target ∀◇ *)
    inversion HeqS; subst.
    simpl in Hwfq. destruct (a_wf_pskl_tophole_inv Hwfq) as [Hg Hwb].
    apply ad_pat_consis__tophole.
    eapply Ht with (Ψna := Ψna);
      [ exact Hc | exact Hmon | exact Hwf
      | exact HΨf | exact HΨa | exact Hdisj | exact Hwb ].
  - (* tophole_inh: subject fixed, target opens under an extended context *)
    inversion HeqS; subst.
    simpl in Hwfq. destruct (a_wf_pskl_all_inv Hwfq) as [Lw Hwbody].
    eapply ad_pat_consis__tophole_inh with
      (L := L `union` Lw `union` dom Θ).
    intros α Hα.
    eapply (H0 α ltac:(clear - Hα; solve_notin_auto) eq_refl Ψn Ψna HΨf HΨa Hdisj);
      [ intros x b Hb; unfold binds; simpl; right; apply Hmon; exact Hb
      | apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ]
      | apply wf_open_of_all; apply Hwbody; clear - Hα; fsetdec ].
  - (* tophole_drop *)
    inversion HeqS; subst.
    apply ad_pat_consis__tophole_drop.
    eapply Ht with (Ψna := Ψna);
      [ exact Hc | exact Hmon | exact Hwf
      | exact HΨf | exact HΨa | exact Hdisj | exact Hwfq ].
  - (* flex_r *)
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    apply (IHHc HeqS Ψn Ψna HΨf HΨa Hdisj Hmon Hwf).
    replace (bskl_to_pskl (ptyp_to_bskl_syn τ)) with (ptyp_to_pskl τ)
      by (unfold ptyp_to_bskl_syn; rewrite bskl_to_pskl_pskl_to_bskl_syn;
          reflexivity).
    apply a_wf_pskl_mono_ptyp;
      [ eapply a_wf_aenv_binds_def_mono; eauto
      | eapply a_wf_aenv_binds_def_wf; eauto ].
Qed.

(** Both dotted (topholeg-vs-topholeg) and mixed (tophole-vs-topholeg)
    ∀◇-transporters; the DERIVATION's subject is the dotted one. *)
Lemma consis_split_transport_topholeg : forall Θb Ψsup R0 R0',
  consis_split_transport Θb Ψsup R0 R0' ->
  consis_split_transport Θb Ψsup (uskl_topholeg R0) (uskl_topholeg R0').
Proof.
  intros Θb Ψsup R0 R0' Ht.
  intros Θ' Ψfull Ψn Ψna Q Hc Hmon Hwf HΨf HΨa Hdisj Hwfq.
  remember (uskl_topholeg R0) as Ssub eqn:HeqS.
  revert Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  induction Hc; try discriminate HeqS;
    intros Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  - (* topholeg *)
    inversion HeqS; subst.
    simpl in Hwfq. destruct (a_wf_pskl_tophole_inv Hwfq) as [Hg Hwb].
    apply ad_pat_consis__topholeg.
    eapply Ht with (Ψna := Ψna);
      [ exact Hc | exact Hmon | exact Hwf
      | exact HΨf | exact HΨa | exact Hdisj | exact Hwb ].
  - (* flex_r *)
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    apply (IHHc HeqS Ψn Ψna HΨf HΨa Hdisj Hmon Hwf).
    replace (bskl_to_pskl (ptyp_to_bskl_syn τ)) with (ptyp_to_pskl τ)
      by (unfold ptyp_to_bskl_syn; rewrite bskl_to_pskl_pskl_to_bskl_syn;
          reflexivity).
    apply a_wf_pskl_mono_ptyp;
      [ eapply a_wf_aenv_binds_def_mono; eauto
      | eapply a_wf_aenv_binds_def_wf; eauto ].
Qed.

Lemma consis_split_transport_keepg : forall Θb Ψsup R0 R0',
  consis_split_transport Θb Ψsup R0 R0' ->
  consis_split_transport Θb Ψsup (uskl_topholeg R0) (uskl_tophole R0').
Proof.
  intros Θb Ψsup R0 R0' Ht.
  intros Θ' Ψfull Ψn Ψna Q Hc Hmon Hwf HΨf HΨa Hdisj Hwfq.
  remember (uskl_topholeg R0) as Ssub eqn:HeqS.
  revert Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  induction Hc; try discriminate HeqS;
    intros Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  - (* topholeg → tophole (plain keep) *)
    inversion HeqS; subst.
    simpl in Hwfq. destruct (a_wf_pskl_tophole_inv Hwfq) as [Hg Hwb].
    apply ad_pat_consis__tophole.
    eapply Ht with (Ψna := Ψna);
      [ exact Hc | exact Hmon | exact Hwf
      | exact HΨf | exact HΨa | exact Hdisj | exact Hwb ].
  - (* flex_r *)
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    apply (IHHc HeqS Ψn Ψna HΨf HΨa Hdisj Hmon Hwf).
    replace (bskl_to_pskl (ptyp_to_bskl_syn τ)) with (ptyp_to_pskl τ)
      by (unfold ptyp_to_bskl_syn; rewrite bskl_to_pskl_pskl_to_bskl_syn;
          reflexivity).
    apply a_wf_pskl_mono_ptyp;
      [ eapply a_wf_aenv_binds_def_mono; eauto
      | eapply a_wf_aenv_binds_def_wf; eauto ].
Qed.

Lemma consis_split_transport_flexvar : forall Θb Ψsup α τ R,
  binds α (abind_flex_mono_def τ) Θb ->
  consis_split_transport Θb Ψsup (ptyp_to_uskl_syn τ) R ->
  consis_split_transport Θb Ψsup (uskl_var_f α) R.
Proof.
  intros Θb Ψsup α τ R Hb Ht.
  intros Θ' Ψfull Ψn Ψna Q Hc Hmon Hwf HΨf HΨa Hdisj Hwfq.
  remember (uskl_var_f α) as Ssub eqn:HeqS.
  revert Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  induction Hc; try discriminate HeqS;
    intros Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  - (* var: the target is the same variable — unfold it on the right *)
    inversion HeqS; subst.
    assert (Hb' : binds α (abind_flex_mono_def τ) Θ) by (apply Hmon; exact Hb).
    assert (Hm : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf | exact Hb' ]).
    assert (Hwfτ : a_wf_ptyp Θ τ)
      by (eapply a_wf_aenv_binds_def_wf; [ exact Hwf | exact Hb' ]).
    eapply ad_pat_consis__flex_r; [ exact Hb' | ].
    eapply Ht with (Ψfull := empty) (Ψna := Ψna);
      [ apply consis_mono_refl;
        [ exact Hm
        | intros β Hβ; eapply a_wf_ptyp_ftv_tvarish; [ exact Hwfτ | exact Hβ ] ]
      | exact Hmon | exact Hwf
      | clear - H HΨf; fsetdec | exact HΨa | exact Hdisj
      | replace (bskl_to_pskl (ptyp_to_bskl_syn τ)) with (ptyp_to_pskl τ)
          by (unfold ptyp_to_bskl_syn; rewrite bskl_to_pskl_pskl_to_bskl_syn;
              reflexivity);
        apply a_wf_pskl_mono_ptyp; [ exact Hm | exact Hwfτ ] ].
  - (* flex_l: the subject unfolds — its definition agrees by uniqueness *)
    inversion HeqS; subst.
    assert (Hb' : binds α (abind_flex_mono_def τ) Θ) by (apply Hmon; exact Hb).
    assert (Hu : uniq Θ) by (apply a_wf_aenv_uniq; exact Hwf).
    pose proof (binds_unique _ _ _ _ _ H Hb' Hu) as He; inversion He; subst.
    eapply Ht with (Ψna := Ψna);
      [ exact Hc | exact Hmon | exact Hwf
      | exact HΨf | exact HΨa | exact Hdisj | exact Hwfq ].
  - (* flex_r: the target unfolds *)
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    apply (IHHc HeqS Ψn Ψna HΨf HΨa Hdisj Hmon Hwf).
    replace (bskl_to_pskl (ptyp_to_bskl_syn τ0)) with (ptyp_to_pskl τ0)
      by (unfold ptyp_to_bskl_syn; rewrite bskl_to_pskl_pskl_to_bskl_syn;
          reflexivity).
    apply a_wf_pskl_mono_ptyp;
      [ eapply a_wf_aenv_binds_def_mono; eauto
      | eapply a_wf_aenv_binds_def_wf; eauto ].
Qed.

(** (2') — the consistency face of precision-substitution, over ⊑ᵤ:
    a consistency of the subject [R] transports to the ghostier [R'],
    the tag context dropping by its Ψsup-portion (Ψsup ⊇ the replaced
    tags Ψrep, disjoint from [R']'s remaining tags). *)
Lemma ad_pat_consis_precise_upre : forall Θb Ψrep R' R,
  uskl_precise Θb Ψrep R' R ->
  forall Ψsup,
  Ψrep [<=] Ψsup ->
  Ψsup ∩ ftag_in_uskl R' [=] empty ->
  consis_split_transport Θb Ψsup R R'.
Proof.
  intros Θb Ψrep R' R Hup; induction Hup;
    intros Ψsup HΨsup Hftag; simpl in Hftag.
  - (* refl *)
    intros Θ' Ψfull Ψn Ψna Q Hc Hmon Hwf HΨf HΨa Hdisj Hwfq.
    assert (Ha0 : Ψna [<=] empty).
    { pose proof (ad_pat_consis_ftag_sub Hc) as Hfs.
      clear - Hfs HΨf HΨa Hftag; fsetdec. }
    eapply ad_pat_consis_psi_cong;
      [ exact Hc | clear - HΨf Ha0; fsetdec ].
  - (* arrow *)
    apply consis_split_transport_arrow.
    + apply IHHup1; [ clear - HΨsup H; fsetdec | clear - Hftag; fsetdec ].
    + apply IHHup2; [ clear - HΨsup H; fsetdec | clear - Hftag; fsetdec ].
  - (* all_syn cong *)
    apply consis_split_transport_all_syn with (L0 := L).
    intros α Hα.
    apply (H0 α Hα);
      [ exact HΨsup
      | match goal with
        | |- _ ∩
               (ftag_in_uskl (open_uskl_wrt_uskl ?B _)) [=] _ =>
            pose proof (ftag_in_uskl_open_var B α) as Hov
        end; clear - Hftag Hov; fsetdec ].
  - (* all_etag cong *)
    assert (Hεout : ε `notin` Ψsup) by (clear - Hftag; fsetdec).
    apply consis_split_transport_all_etag_cong with (L0 := L);
      [ exact Hεout | ].
    intros α Hα.
    apply (H0 α Hα);
      [ exact HΨsup
      | match goal with
        | |- _ ∩
               (ftag_in_uskl (open_uskl_wrt_uskl ?B _)) [=] _ =>
            pose proof (ftag_in_uskl_open_var B α) as Hov
        end; clear - Hftag Hov; fsetdec ].
  - (* all_inst *)
    assert (Hεin : ε `in` Ψsup) by (clear - HΨsup H1; fsetdec).
    apply consis_split_transport_all_inst with (L0 := L);
      [ exact Hεin | ].
    intros α Hα.
    apply (H0 α Hα);
      [ clear - HΨsup H1; fsetdec
      | match goal with
        | |- _ ∩
               (ftag_in_uskl (open_uskl_wrt_uskl ?B _)) [=] _ =>
            pose proof (ftag_in_uskl_open_var B α) as Hov
        end; clear - Hftag Hov; fsetdec ].
  - (* tophole cong *)
    apply consis_split_transport_tophole.
    apply IHHup; [ exact HΨsup | clear - Hftag; fsetdec ].
  - (* topholeg cong *)
    apply consis_split_transport_topholeg.
    apply IHHup; [ exact HΨsup | clear - Hftag; fsetdec ].
  - (* tophole_keepg *)
    apply consis_split_transport_keepg.
    apply IHHup; [ exact HΨsup | clear - Hftag; fsetdec ].
  - (* hole *)
    intros Θ' Ψfull Ψn Ψna Q Hc Hmon Hwf HΨf HΨa Hdisj Hwfq.
    assert (HΨe : Ψn [=] empty).
    { pose proof (ad_pat_consis_ftag_sub Hc) as Hfs.
      pose proof (no_forall_uskl_ftag _ H0) as Hfe.
      clear - Hfs Hfe HΨf; fsetdec. }
    pose proof (ad_pat_consis_strip_tags Hc) as Hstr.
    destruct (consis_concrete_target_inh Hstr Hwf (uskl_to_pskl R) eq_refl H0)
      as [_ Heqinh].
    rewrite <- Heqinh.
    apply ad_pat_consis__hole; [ exact HΨe | exact Hwfq ].
  - (* tophole_remove *)
    intros Θ' Ψfull Ψn Ψna Q Hc Hmon Hwf HΨf HΨa Hdisj Hwfq.
    apply ad_pat_consis__tophole_drop.
    assert (Hftag' : Ψsup ∩ ftag_in_uskl R' [=] empty)
      by (clear - Hftag; fsetdec).
    exact (IHHup Ψsup HΨsup Hftag' Θ' Ψfull Ψn Ψna Q
             Hc Hmon Hwf HΨf HΨa Hdisj Hwfq).
  - (* flex_l *)
    intros Θ' Ψfull Ψn Ψna Q Hc Hmon Hwf HΨf HΨa Hdisj Hwfq.
    eapply ad_pat_consis__flex_l; [ apply Hmon; exact H | ].
    assert (Hftag' : Ψsup ∩
                       (ftag_in_uskl (ptyp_to_uskl_syn τ)) [=] empty)
      by (pose proof (ftag_in_uskl_ptyp_syn τ) as Hpt; clear - Hpt; fsetdec).
    exact (IHHup Ψsup HΨsup Hftag' Θ' Ψfull Ψn Ψna Q
             Hc Hmon Hwf HΨf HΨa Hdisj Hwfq).
  - (* flex_r *)
    apply consis_split_transport_flexvar with (τ := τ); [ exact H | ].
    apply IHHup; [ exact HΨsup | exact Hftag ].
Qed.

(* ===================================================================== *)
(*  ⊑ᵤ kit additions for the subtyping level (step (3)).                  *)
(* ===================================================================== *)

Lemma ftag_in_uskl_open_rec_upper : forall R ψ k,
  ftag_in_uskl (open_uskl_wrt_uskl_rec k ψ R) [<=]
  ftag_in_uskl R `union` ftag_in_uskl ψ.
Proof.
  intros R ψ; induction R; intros k; simpl; try fsetdec.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; fsetdec.
  - pose proof (IHR1 k); pose proof (IHR2 k); fsetdec.
  - pose proof (IHR (S k)); fsetdec.
  - pose proof (IHR (S k)); fsetdec.
  - pose proof (IHR k); fsetdec.
  - pose proof (IHR k); fsetdec.
Qed.

Lemma ftag_in_uskl_open_upper : forall R ψ,
  ftag_in_uskl (open_uskl_wrt_uskl R ψ) [<=]
  ftag_in_uskl R `union` ftag_in_uskl ψ.
Proof.
  intros; unfold open_uskl_wrt_uskl; apply ftag_in_uskl_open_rec_upper.
Qed.

(** The replaced tags all come from the (decorated) RHS. *)
Lemma uskl_precise_ftag_rep : forall Θ Ψrep R' R,
  uskl_precise Θ Ψrep R' R ->
  Ψrep [<=] ftag_in_uskl R.
Proof.
  intros Θ Ψrep R' R H; induction H; simpl; try fsetdec.
  - (* all_syn cong *)
    pick fresh α for L.
    pose proof (H0 α ltac:(solve_notin_auto)) as Hα.
    pose proof (ftag_in_uskl_open_var R α); fsetdec.
  - (* all_etag cong *)
    pick fresh α for L.
    pose proof (H0 α ltac:(solve_notin_auto)) as Hα.
    pose proof (ftag_in_uskl_open_var R α); fsetdec.
  - (* all_inst *)
    pick fresh α for L.
    pose proof (H0 α ltac:(solve_notin_auto)) as Hα.
    pose proof (ftag_in_uskl_open_var R α); fsetdec.
  - (* flex_r *)
    pose proof (ftag_in_uskl_ptyp_syn τ); fsetdec.
Qed.

(** The ghostier side of ⊑ᵤ is locally closed. *)
Lemma uskl_precise_lc_l : forall Θ Ψrep R' R,
  uskl_precise Θ Ψrep R' R -> lc_uskl R'.
Proof.
  intros Θ Ψrep R' R Hup; induction Hup.
  - assumption.
  - apply lc_uskl_arrow; assumption.
  - pick fresh α for L.
    apply lc_uskl_all_syn_exists with (α1 := α). apply H0; fsetdec.
  - pick fresh α for L.
    apply lc_uskl_all_etag_exists with (α1 := α). apply H0; fsetdec.
  - pick fresh α for L.
    apply lc_uskl_all_syn_exists with (α1 := α). apply H0; fsetdec.
  - apply lc_uskl_tophole; assumption.
  - apply lc_uskl_topholeg; assumption.
  - apply lc_uskl_tophole; assumption.
  - apply lc_uskl_hole.
  - apply lc_uskl_tophole; assumption.
  - apply lc_uskl_var_f.
  - assumption.
Qed.

(** ⊑ᵤ is closed under substituting a ⊑ᵤ-related pair INTO a common
    skeleton (Sub-ForallL item 2, the subst-INTO companion of
    [uskl_precise_subst]): replace a rigid variable of [R] by the
    ghostier [ψ'] on the left and by [ψ] on the right.  Every occurrence
    replaces the SAME tags [Ψrep], and sets absorb, so the result's tag
    reading is [Ψrep] whenever the variable occurs — this occurring form
    demands [α0 ∈ ftv R]; [uskl_precise_subst_into] below packages the
    absent case (both sides collapse to [R], no tags replaced) as a
    disjunction, and [uskl_precise_open_into] restates it in the
    opening form the ForallL join rows consume. *)
Lemma uskl_precise_subst_into_in : forall R,
  lc_uskl R ->
  forall Θ Ψrep ψ' ψ α0,
  uskl_precise Θ Ψrep ψ' ψ ->
  lc_uskl ψ ->
  α0 `in` ftvar_in_uskl R ->
  uskl_precise Θ Ψrep
    (subst_uskl_in_uskl ψ' α0 R) (subst_uskl_in_uskl ψ α0 R).
Proof.
  intros R Hlc; induction Hlc; intros Θ Ψrep ψ' ψ α0 Hp Hlcψ Hin;
    simpl in Hin |- *.
  - (* unit *) exfalso; clear - Hin; fsetdec.
  - (* var *)
    destruct_if as [-> | Hne]; [ exact Hp | ].
    exfalso; clear - Hin Hne; fsetdec.
  - (* arrow : occurrence decides each component; sets absorb *)
    destruct (AtomSetProperties.In_dec α0 (ftvar_in_uskl R1))
      as [Hin1 | Hni1];
      destruct (AtomSetProperties.In_dec α0 (ftvar_in_uskl R2))
        as [Hin2 | Hni2].
    + apply upre__arrow with (Ψ1 := Ψrep) (Ψ2 := Ψrep);
        [ apply IHHlc1; assumption | apply IHHlc2; assumption
        | clear; fsetdec ].
    + apply upre__arrow with (Ψ1 := Ψrep) (Ψ2 := empty);
        [ apply IHHlc1; assumption
        | rewrite (subst_uskl_in_uskl_fresh_eq R2 ψ' α0 Hni2);
          rewrite (subst_uskl_in_uskl_fresh_eq R2 ψ α0 Hni2);
          apply upre__refl; [ assumption | reflexivity ]
        | clear; fsetdec ].
    + apply upre__arrow with (Ψ1 := empty) (Ψ2 := Ψrep);
        [ rewrite (subst_uskl_in_uskl_fresh_eq R1 ψ' α0 Hni1);
          rewrite (subst_uskl_in_uskl_fresh_eq R1 ψ α0 Hni1);
          apply upre__refl; [ assumption | reflexivity ]
        | apply IHHlc2; assumption
        | clear; fsetdec ].
    + exfalso; clear - Hin Hni1 Hni2; fsetdec.
  - (* all_syn *)
    assert (Hlcψ' : lc_uskl ψ') by (eapply uskl_precise_lc_l; exact Hp).
    apply upre__all_syn with (L := singleton α0).
    intros β Hβ.
    assert (Hne : α0 <> β) by (clear - Hβ; fsetdec).
    rewrite (subst_uskl_in_uskl_open_uskl_wrt_uskl_var R ψ' α0 β Hne Hlcψ').
    rewrite (subst_uskl_in_uskl_open_uskl_wrt_uskl_var R ψ α0 β Hne Hlcψ).
    apply H0; [ exact Hp | exact Hlcψ | ].
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f β))
      as Hlo.
    clear - Hin Hlo; fsetdec.
  - (* all_etag *)
    assert (Hlcψ' : lc_uskl ψ') by (eapply uskl_precise_lc_l; exact Hp).
    apply upre__all_etag with (L := singleton α0).
    intros β Hβ.
    assert (Hne : α0 <> β) by (clear - Hβ; fsetdec).
    rewrite (subst_uskl_in_uskl_open_uskl_wrt_uskl_var R ψ' α0 β Hne Hlcψ').
    rewrite (subst_uskl_in_uskl_open_uskl_wrt_uskl_var R ψ α0 β Hne Hlcψ).
    apply H0; [ exact Hp | exact Hlcψ | ].
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f β))
      as Hlo.
    clear - Hin Hlo; fsetdec.
  - (* hole *) exfalso; clear - Hin; fsetdec.
  - (* tophole *)
    apply upre__tophole. apply IHHlc; assumption.
  - (* holeg *) exfalso; clear - Hin; fsetdec.
  - (* topholeg *)
    apply upre__topholeg. apply IHHlc; assumption.
Qed.

(** The packaged form: [Ψrep] if the variable occurs, [∅] if not. *)
Lemma uskl_precise_subst_into : forall R Θ Ψrep ψ' ψ α0,
  lc_uskl R ->
  uskl_precise Θ Ψrep ψ' ψ ->
  lc_uskl ψ ->
  exists Ψrep',
    (Ψrep' [=] Ψrep \/ Ψrep' [=] empty) /\
    uskl_precise Θ Ψrep'
      (subst_uskl_in_uskl ψ' α0 R) (subst_uskl_in_uskl ψ α0 R).
Proof.
  intros R Θ Ψrep ψ' ψ α0 Hlc Hp Hlcψ.
  destruct (AtomSetProperties.In_dec α0 (ftvar_in_uskl R)) as [Hin | Hni].
  - exists Ψrep. split; [ left; reflexivity | ].
    eapply uskl_precise_subst_into_in; eauto.
  - exists empty. split; [ right; reflexivity | ].
    rewrite (subst_uskl_in_uskl_fresh_eq R ψ' α0 Hni).
    rewrite (subst_uskl_in_uskl_fresh_eq R ψ α0 Hni).
    apply upre__refl; [ exact Hlc | reflexivity ].
Qed.

(** The opening form the ForallL join rows consume: the row's premise
    runs at subject [R^ψ], and the precision swap replaces the opened
    instantiation wholesale. *)
Lemma uskl_precise_open_into : forall R Θ Ψrep ψ' ψ,
  (forall α, lc_uskl (open_uskl_wrt_uskl R (uskl_var_f α))) ->
  uskl_precise Θ Ψrep ψ' ψ ->
  lc_uskl ψ ->
  exists Ψrep',
    (Ψrep' [=] Ψrep \/ Ψrep' [=] empty) /\
    uskl_precise Θ Ψrep'
      (open_uskl_wrt_uskl R ψ') (open_uskl_wrt_uskl R ψ).
Proof.
  intros R Θ Ψrep ψ' ψ Hbody Hp Hlcψ.
  pick fresh α for (ftvar_in_uskl R).
  rewrite (subst_uskl_in_uskl_intro α R ψ' ltac:(clear - Fr; solve_notin_auto)).
  rewrite (subst_uskl_in_uskl_intro α R ψ ltac:(clear - Fr; solve_notin_auto)).
  eapply uskl_precise_subst_into;
    [ apply Hbody | exact Hp | exact Hlcψ ].
Qed.

(* ===================================================================== *)
(*  Sub-ForallL step (3) enabler — ERASURE-REFINEMENT over ⊑ᵤ.            *)
(*                                                                        *)
(*  [uskl_precise_erase_refine]: whatever the erasure of a subject        *)
(*  refines to, the erasure of a ⊑ᵤ-ghostier subject refines to as well.  *)
(*  ONE fused induction on the ⊳-derivation, inverting [uskl_precise] at  *)
(*  each erasure shape — [ad_refine_syn_trans]'s outer/inner skeleton     *)
(*  (prop_precise.v) with the left-hand refinement replaced by the        *)
(*  precision.                                                            *)
(*                                                                        *)
(*  The [upre__hole] crux (concluding [□ ⊳ Qr] needs [Θ ⨟ ∅ ⊢ₚₛᵃ Qr],     *)
(*  and ⊳ does NOT transport wf∅ source→target through [__tophole_fill] — *)
(*  a fill may mention the fresh context-side binder) is resolved the     *)
(*  same way [ad_refine_syn_trans] resolves its own hole case: the        *)
(*  TARGET's wf is ASSUMED (the paper's external-wf side condition;       *)
(*  declarative.tex:1427 requires it of every refinement judgment, and    *)
(*  the use site — P5's [ad_pat_sub_precise_upre] — already carries it as *)
(*  [Hwfq]) and the empty-Δ form is recovered from the Δ-discipline:      *)
(*  the policed-set transport [ad_refine_pskl_ftv_policed] below shows a  *)
(*  refinement from a Δ-free source has a Δ-free target, and              *)
(*  [a_wf_pskl_delta_shrink] then strips Δ.  No hygiene-indexed [_f]      *)
(*  mirror is needed: the conclusion derivation is rebuilt node-by-node   *)
(*  at the SAME (possibly [__tophole_fill]-extended) context as the       *)
(*  input, so well-formedness over the unextended context never arises.   *)
(* ===================================================================== *)

(** A set of atoms fresh for the context and absent from the source stays
    absent from the target: everything a refinement step introduces is a
    fill (wf at ⨟ ∅, hence Θ-scoped), a flexible definition (Θ-scoped), or
    a binder the target immediately re-binds. *)
Lemma ad_refine_pskl_ftv_policed : forall Θ Δ P Q,
  Θ ⨟ Δ ⊢ᵣₚᵃ P ⊳ Q ->
  a_wf_aenv Θ ->
  forall S,
  (forall α, α `in` S -> α `notin` dom Θ) ->
  S ∩ ftvar_in_pskl P [=] empty ->
  S ∩ ftvar_in_pskl Q [=] empty.
Proof.
  intros Θ Δ P Q Href; induction Href; intros Hwf S Hfr Hsrc;
    simpl in Hsrc |- *.
  - (* unit *) exact Hsrc.
  - (* var *) exact Hsrc.
  - (* arrow *)
    assert (Hs1 : S ∩ ftvar_in_pskl P1 [=] empty) by (clear - Hsrc; fsetdec).
    assert (Hs2 : S ∩ ftvar_in_pskl P2 [=] empty) by (clear - Hsrc; fsetdec).
    pose proof (IHHref1 Hwf S Hfr Hs1) as Ht1.
    pose proof (IHHref2 Hwf S Hfr Hs2) as Ht2.
    clear - Ht1 Ht2; fsetdec.
  - (* all *)
    pick fresh α for (L `union` S `union` dom Θ
                        `union` ftvar_in_pskl P `union` ftvar_in_pskl Q).
    assert (Hs0 : S ∩ ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f α))
                    [=] empty).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                    P (pskl_var_f α)) as Hup.
      simpl in Hup. clear - Hsrc Hup Fr. fsetdec. }
    pose proof (H0 α ltac:(clear - Fr; solve_notin_auto) Hwf S Hfr Hs0) as Ht.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_lower
                  Q (pskl_var_f α)) as Hlo.
    clear - Ht Hlo. fsetdec.
  - (* hole : the fill is wf at ⨟ ∅, hence S-free *)
    eapply a_wf_pskl_empty_delta_free; [ exact H | exact Hfr ].
  - (* tophole_remove *)
    apply IHHref; auto.
  - (* tophole_fill : the fresh binder is re-bound by the target ∀ *)
    pick fresh α for (L `union` S `union` dom Θ `union` ftvar_in_pskl Q).
    assert (Hwf' : a_wf_aenv ((α ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - Fr; fsetdec | exact Hwf ]).
    assert (Hfr' : forall β, β `in` S ->
                   β `notin` dom ((α ~ abind_tvar) ++ Θ)).
    { intros β Hβ. simpl.
      assert (Hne : β <> α) by (clear - Hβ Fr; fsetdec).
      pose proof (Hfr β Hβ) as Hβd. clear - Hne Hβd. fsetdec. }
    pose proof (H0 α ltac:(clear - Fr; solve_notin_auto) Hwf' S Hfr' Hsrc) as Ht.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_lower
                  Q (pskl_var_f α)) as Hlo.
    clear - Ht Hlo. fsetdec.
  - (* tophole_keep *)
    apply IHHref; auto.
  - (* flex_l : the definition is Θ-scoped *)
    apply IHHref; auto.
    assert (Hwfτ : Θ ⨟ empty ⊢ₚₛᵃ (ptyp_to_pskl τ))
      by (apply a_wf_ptyp_to_wf_pskl;
          eapply a_wf_aenv_binds_def_wf; [ exact Hwf | exact H ]).
    eapply a_wf_pskl_empty_delta_free; [ exact Hwfτ | exact Hfr ].
  - (* flex_r : the target variable is Θ-bound *)
    apply inter_empty_pointwise. intros β Hβ. intro Hc.
    assert (Heqβ : β = α) by (clear - Hc; fsetdec). subst β.
    apply (Hfr α Hβ). eapply binds_In; exact H.
Qed.

(** The left-hand ghost rule, in the shape the [upre__hole] rows need: a
    ghost refines to anything a wf∅ source refines to, given the target
    wf (externally, per the doctrine above) at the ambient Δ. *)
Lemma ad_refine_pskl_hole_l : forall Θ Δ Qm Qr,
  Θ ⨟ Δ ⊢ᵣₚᵃ Qm ⊳ Qr ->
  a_wf_aenv Θ ->
  (forall α, α `in` Δ -> α `notin` dom Θ) ->
  Θ ⨟ empty ⊢ₚₛᵃ Qm ->
  Θ ⨟ Δ ⊢ₚₛᵃ Qr ->
  Θ ⨟ Δ ⊢ᵣₚᵃ pskl_hole ⊳ Qr.
Proof.
  intros Θ Δ Qm Qr Href Hwf Hdisj Hwfm Hwfr.
  assert (Hsrc : Δ ∩ ftvar_in_pskl Qm [=] empty)
    by (eapply a_wf_pskl_empty_delta_free; [ exact Hwfm | exact Hdisj ]).
  assert (Htgt : Δ ∩ ftvar_in_pskl Qr [=] empty)
    by (eapply ad_refine_pskl_ftv_policed;
        [ exact Href | exact Hwf | exact Hdisj | exact Hsrc ]).
  apply ad_refine_pskl__hole.
  eapply a_wf_pskl_delta_shrink; [ exact Hwfr | ].
  intros α HαΔ HαQ. exfalso.
  assert (Hin : α `in` Δ ∩ ftvar_in_pskl Qr) by (apply inter_3; auto).
  rewrite Htgt in Hin. clear - Hin. fsetdec.
Qed.

(** ⊑ᵤ against a MONOTYPE syn painting: the ghostier side's erasure
    refines to the painted monotype.  Self-contained (a monotype painting
    is unit / var / arrow, so no binder rows fire); handles the flex-var
    unfolding rows of the main lemma, where the refinement side is
    exhausted while the precision keeps unfolding definitions. *)
Lemma uskl_precise_mono_refine : forall Θb Ψr R' R,
  uskl_precise Θb Ψr R' R ->
  forall Θ Δ τ',
  R = ptyp_to_uskl_syn τ' ->
  mono_ptyp τ' ->
  (forall x (b : abind), binds x b Θb -> binds x b Θ) ->
  a_wf_aenv Θ ->
  Θ ⨟ empty ⊢ₚₛᵃ (ptyp_to_pskl τ') ->
  Θ ⨟ Δ ⊢ᵣₚᵃ ⌊ R' ⌋ˢ ⊳ (ptyp_to_pskl τ').
Proof.
  intros Θb Ψr R' R Hp; induction Hp;
    intros Θ' Δ τ' Heq Hm Hmon Hwf Hwfτ.
  - (* refl *)
    rewrite Heq. rewrite uskl_to_pskl_ptyp.
    apply ad_refine_pskl_refl.
    eapply a_wf_pskl_delta_mono; [ exact Hwfτ | clear; fsetdec ].
  - (* arrow *)
    destruct τ' as [ | n | β | τ1 τ2 | τ0 ];
      unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in Heq;
      simpl in Heq; try discriminate Heq.
    inversion Heq; subst.
    inversion Hm; subst.
    assert (Hw1 : Θ' ⨟ empty ⊢ₚₛᵃ (ptyp_to_pskl τ1))
      by (inversion Hwfτ; subst; assumption).
    assert (Hw2 : Θ' ⨟ empty ⊢ₚₛᵃ (ptyp_to_pskl τ2))
      by (inversion Hwfτ; subst; assumption).
    simpl. apply ad_refine_pskl__arrow.
    + eapply IHHp1;
        [ unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn; reflexivity
        | assumption | exact Hmon | exact Hwf | exact Hw1 ].
    + eapply IHHp2;
        [ unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn; reflexivity
        | assumption | exact Hmon | exact Hwf | exact Hw2 ].
  - (* all_syn cong : a monotype painting is never ∀-headed *)
    destruct τ' as [ | n | β | τ1 τ2 | τ0 ];
      unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in Heq;
      simpl in Heq; try discriminate Heq.
    inversion Hm.
  - (* all_etag cong *)
    destruct τ' as [ | n | β | τ1 τ2 | τ0 ];
      unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in Heq;
      simpl in Heq; discriminate Heq.
  - (* all_inst *)
    destruct τ' as [ | n | β | τ1 τ2 | τ0 ];
      unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in Heq;
      simpl in Heq; discriminate Heq.
  - (* tophole cong *)
    destruct τ' as [ | n | β | τ1 τ2 | τ0 ];
      unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in Heq;
      simpl in Heq; discriminate Heq.
  - (* topholeg cong *)
    destruct τ' as [ | n | β | τ1 τ2 | τ0 ];
      unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in Heq;
      simpl in Heq; discriminate Heq.
  - (* tophole_keepg *)
    destruct τ' as [ | n | β | τ1 τ2 | τ0 ];
      unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in Heq;
      simpl in Heq; discriminate Heq.
  - (* hole *)
    simpl. apply ad_refine_pskl__hole. exact Hwfτ.
  - (* tophole_remove *)
    simpl. apply ad_refine_pskl__tophole_remove.
    eapply IHHp;
      [ exact Heq | exact Hm | exact Hmon | exact Hwf | exact Hwfτ ].
  - (* flex_l : unfold the ghostier side's definition *)
    simpl. eapply ad_refine_pskl__flex_l; [ apply Hmon; eassumption | ].
    pose proof (IHHp Θ' Δ τ' Heq Hm Hmon Hwf Hwfτ) as Ht.
    rewrite uskl_to_pskl_ptyp in Ht. exact Ht.
  - (* flex_r : the precise side IS a defined variable *)
    destruct τ' as [ | n | β | τ1 τ2 | τ0 ];
      unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in Heq;
      simpl in Heq; try discriminate Heq.
    inversion Heq; subst.
    simpl. eapply ad_refine_pskl__flex_r; [ apply Hmon; eassumption | ].
    match goal with
      Hb : binds _ (abind_flex_mono_def ?t) Θb |- _ =>
      eapply IHHp;
        [ reflexivity
        | eapply a_wf_aenv_binds_def_mono; [ exact Hwf | apply Hmon; exact Hb ]
        | exact Hmon | exact Hwf
        | apply a_wf_ptyp_to_wf_pskl;
          eapply a_wf_aenv_binds_def_wf; [ exact Hwf | apply Hmon; exact Hb ] ]
    end.
Qed.

(* The three ⊑ᵤ rows every inner induction of the main lemma shares.
   [refl] is inline (rewrite the erasure equation, hand back the
   reconstituted node); the others are: *)

(* [upre__hole]: the ghost helper, fed the node + the row's own source
   wf∅ (weakened Θb → Θ) + the assumed target wf. *)
Local Ltac erase_refine_hole Hrr Hwf Hdisj Hwfr Hmon Heq :=
  simpl;
  eapply ad_refine_pskl_hole_l;
    [ exact Hrr | exact Hwf | exact Hdisj
    | rewrite <- Heq; eapply a_wf_pskl_weaken; [ exact Hmon | eassumption ]
    | exact Hwfr ].

(* [upre__tophole_remove]: peel the ghostier side's ∀◇ and recurse. *)
Local Ltac erase_refine_remove IHHp Heq :=
  simpl; apply ad_refine_pskl__tophole_remove; apply IHHp; exact Heq.

(* [upre__flex_l]: unfold the ghostier side's flex definition and recurse
   (the precise side, hence the erasure equation, is unchanged). *)
Local Ltac erase_refine_flexl Hmon IHHp Heq :=
  simpl; eapply ad_refine_pskl__flex_l;
    [ apply Hmon; eassumption
    | let Ht := fresh "Ht" in
      pose proof (IHHp Heq) as Ht;
      rewrite uskl_to_pskl_ptyp in Ht; exact Ht ].

(** THE STEP-(3) ENABLER (Sub-ForallL item 1): the erasure of a
    ⊑ᵤ-ghostier subject refines to anything the original subject's
    erasure refines to.  Target wf is the assumed external side
    condition (P5's [Hwfq] at the use site); Δ holds refinement-local
    ∀-variables, fresh for Θ. *)
Lemma uskl_precise_erase_refine : forall Θ Δ Qm Qr,
  Θ ⨟ Δ ⊢ᵣₚᵃ Qm ⊳ Qr ->
  a_wf_aenv Θ ->
  (forall α, α `in` Δ -> α `notin` dom Θ) ->
  Θ ⨟ Δ ⊢ₚₛᵃ Qr ->
  forall Θb Ψr R' R,
  uskl_precise Θb Ψr R' R ->
  (forall x (b : abind), binds x b Θb -> binds x b Θ) ->
  ⌊ R ⌋ˢ = Qm ->
  Θ ⨟ Δ ⊢ᵣₚᵃ ⌊ R' ⌋ˢ ⊳ Qr.
Proof.
  intros Θ Δ Qm Qr Hr; induction Hr;
    intros Hwf Hdisj Hwfr Θb Ψr R' R Hp Hmon Heq.
  - (* unit *)
    assert (Hrr : Θ ⨟ Δ ⊢ᵣₚᵃ pskl_unit ⊳ pskl_unit)
      by (apply ad_refine_pskl__unit).
    revert Heq; induction Hp; intros Heq; simpl in Heq; try discriminate Heq.
    + rewrite Heq. exact Hrr.
    + erase_refine_hole Hrr Hwf Hdisj Hwfr Hmon Heq.
    + erase_refine_remove IHHp Heq.
    + erase_refine_flexl Hmon IHHp Heq.
  - (* var *)
    assert (Hrr : Θ ⨟ Δ ⊢ᵣₚᵃ (pskl_var_f α) ⊳ (pskl_var_f α))
      by (apply ad_refine_pskl__var; exact H).
    revert Heq; induction Hp; intros Heq; simpl in Heq; try discriminate Heq.
    + rewrite Heq. exact Hrr.
    + erase_refine_hole Hrr Hwf Hdisj Hwfr Hmon Heq.
    + erase_refine_remove IHHp Heq.
    + erase_refine_flexl Hmon IHHp Heq.
    + (* flex_r : the precise side is a DEFINED variable — the refinement
         side is exhausted (var ⊳ var); hand over to the mono kit *)
      inversion Heq; subst.
      simpl. eapply ad_refine_pskl__flex_r; [ apply Hmon; eassumption | ].
      match goal with
        Hb : binds _ (abind_flex_mono_def ?t) Θb |- _ =>
        eapply uskl_precise_mono_refine;
          [ eassumption | reflexivity
          | eapply a_wf_aenv_binds_def_mono;
              [ exact Hwf | apply Hmon; exact Hb ]
          | exact Hmon | exact Hwf
          | apply a_wf_ptyp_to_wf_pskl;
            eapply a_wf_aenv_binds_def_wf; [ exact Hwf | apply Hmon; exact Hb ] ]
      end.
  - (* arrow *)
    assert (Hrr : Θ ⨟ Δ ⊢ᵣₚᵃ (pskl_arrow P1 P2) ⊳ (pskl_arrow Q1 Q2))
      by (apply ad_refine_pskl__arrow; assumption).
    assert (Hw1 : Θ ⨟ Δ ⊢ₚₛᵃ Q1) by (inversion Hwfr; subst; assumption).
    assert (Hw2 : Θ ⨟ Δ ⊢ₚₛᵃ Q2) by (inversion Hwfr; subst; assumption).
    revert Heq; induction Hp; intros Heq; simpl in Heq; try discriminate Heq.
    + rewrite Heq. exact Hrr.
    + (* upre__arrow *)
      inversion Heq; subst.
      simpl. apply ad_refine_pskl__arrow.
      * eapply IHHr1;
          [ exact Hwf | exact Hdisj | exact Hw1
          | eassumption | exact Hmon | reflexivity ].
      * eapply IHHr2;
          [ exact Hwf | exact Hdisj | exact Hw2
          | eassumption | exact Hmon | reflexivity ].
    + erase_refine_hole Hrr Hwf Hdisj Hwfr Hmon Heq.
    + erase_refine_remove IHHp Heq.
    + erase_refine_flexl Hmon IHHp Heq.
  - (* all *)
    assert (Hrr : Θ ⨟ Δ ⊢ᵣₚᵃ (pskl_all_syn P) ⊳ (pskl_all_syn Q))
      by (apply ad_refine_pskl__all with (L := L); exact H).
    destruct (a_wf_pskl_all_inv Hwfr) as [Lw Hwbody].
    revert Heq; induction Hp; intros Heq; simpl in Heq; try discriminate Heq.
    + rewrite Heq. exact Hrr.
    + (* upre__all_syn *)
      inversion Heq; subst.
      simpl.
      match goal with
        Hfam : forall β, β `notin` ?LL -> uskl_precise _ _ _ _ |- _ =>
        apply ad_refine_pskl__all
          with (L := L `union` LL `union` Lw `union` dom Θ `union` Δ);
        intros α2 Hα2;
        rewrite <- uskl_to_pskl_open;
        eapply H0;
          [ clear - Hα2; fsetdec
          | exact Hwf
          | intros β Hβ;
            destruct (β == α2) as [-> | Hne];
              [ clear - Hα2; fsetdec
              | apply Hdisj; clear - Hβ Hne; fsetdec ]
          | apply Hwbody; clear - Hα2; fsetdec
          | apply Hfam; clear - Hα2; fsetdec
          | exact Hmon
          | apply uskl_to_pskl_open ]
      end.
    + (* upre__all_etag *)
      inversion Heq; subst.
      simpl.
      match goal with
        Hfam : forall β, β `notin` ?LL -> uskl_precise _ _ _ _ |- _ =>
        apply ad_refine_pskl__all
          with (L := L `union` LL `union` Lw `union` dom Θ `union` Δ);
        intros α2 Hα2;
        rewrite <- uskl_to_pskl_open;
        eapply H0;
          [ clear - Hα2; fsetdec
          | exact Hwf
          | intros β Hβ;
            destruct (β == α2) as [-> | Hne];
              [ clear - Hα2; fsetdec
              | apply Hdisj; clear - Hβ Hne; fsetdec ]
          | apply Hwbody; clear - Hα2; fsetdec
          | apply Hfam; clear - Hα2; fsetdec
          | exact Hmon
          | apply uskl_to_pskl_open ]
      end.
    + (* upre__all_inst *)
      inversion Heq; subst.
      simpl.
      match goal with
        Hfam : forall β, β `notin` ?LL -> uskl_precise _ _ _ _ |- _ =>
        apply ad_refine_pskl__all
          with (L := L `union` LL `union` Lw `union` dom Θ `union` Δ);
        intros α2 Hα2;
        rewrite <- uskl_to_pskl_open;
        eapply H0;
          [ clear - Hα2; fsetdec
          | exact Hwf
          | intros β Hβ;
            destruct (β == α2) as [-> | Hne];
              [ clear - Hα2; fsetdec
              | apply Hdisj; clear - Hβ Hne; fsetdec ]
          | apply Hwbody; clear - Hα2; fsetdec
          | apply Hfam; clear - Hα2; fsetdec
          | exact Hmon
          | apply uskl_to_pskl_open ]
      end.
    + erase_refine_hole Hrr Hwf Hdisj Hwfr Hmon Heq.
    + erase_refine_remove IHHp Heq.
    + erase_refine_flexl Hmon IHHp Heq.
  - (* hole *)
    assert (Hrr : Θ ⨟ Δ ⊢ᵣₚᵃ pskl_hole ⊳ Q)
      by (apply ad_refine_pskl__hole; exact H).
    revert Heq; induction Hp; intros Heq; simpl in Heq; try discriminate Heq.
    + rewrite Heq. exact Hrr.
    + simpl. exact Hrr.
    + erase_refine_remove IHHp Heq.
    + erase_refine_flexl Hmon IHHp Heq.
  - (* tophole_remove *)
    assert (Hrr : Θ ⨟ Δ ⊢ᵣₚᵃ (pskl_tophole P) ⊳ Q)
      by (apply ad_refine_pskl__tophole_remove; exact Hr).
    revert Heq; induction Hp; intros Heq; simpl in Heq; try discriminate Heq.
    + rewrite Heq. exact Hrr.
    + (* upre__tophole *)
      inversion Heq; subst.
      simpl. apply ad_refine_pskl__tophole_remove.
      eapply IHHr;
        [ exact Hwf | exact Hdisj | exact Hwfr
        | eassumption | exact Hmon | reflexivity ].
    + (* upre__topholeg *)
      inversion Heq; subst.
      simpl. apply ad_refine_pskl__tophole_remove.
      eapply IHHr;
        [ exact Hwf | exact Hdisj | exact Hwfr
        | eassumption | exact Hmon | reflexivity ].
    + (* upre__tophole_keepg *)
      inversion Heq; subst.
      simpl. apply ad_refine_pskl__tophole_remove.
      eapply IHHr;
        [ exact Hwf | exact Hdisj | exact Hwfr
        | eassumption | exact Hmon | reflexivity ].
    + erase_refine_hole Hrr Hwf Hdisj Hwfr Hmon Heq.
    + erase_refine_remove IHHp Heq.
    + erase_refine_flexl Hmon IHHp Heq.
  - (* tophole_fill *)
    assert (Hrr : Θ ⨟ Δ ⊢ᵣₚᵃ (pskl_tophole P) ⊳ (pskl_all_syn Q))
      by (apply ad_refine_pskl__tophole_fill with (L := L); exact H).
    destruct (a_wf_pskl_all_inv Hwfr) as [Lw Hwbody].
    revert Heq; induction Hp; intros Heq; simpl in Heq; try discriminate Heq.
    + rewrite Heq. exact Hrr.
    + (* upre__tophole *)
      inversion Heq; subst.
      simpl.
      apply ad_refine_pskl__tophole_fill
        with (L := L `union` Lw `union` dom Θ `union` Δ).
      intros α2 Hα2.
      match goal with
      |- _ ⨟ _ ⊢ᵣₚᵃ (pskl_tophole (uskl_to_pskl ?RR)) ⊳ _ =>
        change (pskl_tophole (uskl_to_pskl RR))
          with (uskl_to_pskl (uskl_tophole RR))
      end.
      eapply H0;
        [ clear - Hα2; fsetdec
        | apply a_wf_aenv__tvar; [ clear - Hα2; fsetdec | exact Hwf ]
        | intros β Hβ; simpl;
          assert (Hne : β <> α2) by (clear - Hβ Hα2; fsetdec);
          pose proof (Hdisj β Hβ) as Hβd; clear - Hne Hβd; fsetdec
        | eapply a_wf_pskl_delta_to_tvar with (Δ0 := add α2 Δ);
            [ apply Hwbody; clear - Hα2; fsetdec | clear; fsetdec ]
        | apply upre__tophole; eassumption
        | intros x b0 Hb0; apply binds_cons_3; apply Hmon; exact Hb0
        | reflexivity ].
    + (* upre__topholeg *)
      inversion Heq; subst.
      simpl.
      apply ad_refine_pskl__tophole_fill
        with (L := L `union` Lw `union` dom Θ `union` Δ).
      intros α2 Hα2.
      match goal with
      |- _ ⨟ _ ⊢ᵣₚᵃ (pskl_tophole (uskl_to_pskl ?RR)) ⊳ _ =>
        change (pskl_tophole (uskl_to_pskl RR))
          with (uskl_to_pskl (uskl_topholeg RR))
      end.
      eapply H0;
        [ clear - Hα2; fsetdec
        | apply a_wf_aenv__tvar; [ clear - Hα2; fsetdec | exact Hwf ]
        | intros β Hβ; simpl;
          assert (Hne : β <> α2) by (clear - Hβ Hα2; fsetdec);
          pose proof (Hdisj β Hβ) as Hβd; clear - Hne Hβd; fsetdec
        | eapply a_wf_pskl_delta_to_tvar with (Δ0 := add α2 Δ);
            [ apply Hwbody; clear - Hα2; fsetdec | clear; fsetdec ]
        | apply upre__topholeg; eassumption
        | intros x b0 Hb0; apply binds_cons_3; apply Hmon; exact Hb0
        | reflexivity ].
    + (* upre__tophole_keepg *)
      inversion Heq; subst.
      simpl.
      apply ad_refine_pskl__tophole_fill
        with (L := L `union` Lw `union` dom Θ `union` Δ).
      intros α2 Hα2.
      match goal with
      |- _ ⨟ _ ⊢ᵣₚᵃ (pskl_tophole (uskl_to_pskl ?RR)) ⊳ _ =>
        change (pskl_tophole (uskl_to_pskl RR))
          with (uskl_to_pskl (uskl_tophole RR))
      end.
      eapply H0;
        [ clear - Hα2; fsetdec
        | apply a_wf_aenv__tvar; [ clear - Hα2; fsetdec | exact Hwf ]
        | intros β Hβ; simpl;
          assert (Hne : β <> α2) by (clear - Hβ Hα2; fsetdec);
          pose proof (Hdisj β Hβ) as Hβd; clear - Hne Hβd; fsetdec
        | eapply a_wf_pskl_delta_to_tvar with (Δ0 := add α2 Δ);
            [ apply Hwbody; clear - Hα2; fsetdec | clear; fsetdec ]
        | apply upre__tophole_keepg; eassumption
        | intros x b0 Hb0; apply binds_cons_3; apply Hmon; exact Hb0
        | reflexivity ].
    + erase_refine_hole Hrr Hwf Hdisj Hwfr Hmon Heq.
    + erase_refine_remove IHHp Heq.
    + erase_refine_flexl Hmon IHHp Heq.
  - (* tophole_keep *)
    assert (Hrr : Θ ⨟ Δ ⊢ᵣₚᵃ (pskl_tophole P) ⊳ (pskl_tophole Q))
      by (apply ad_refine_pskl__tophole_keep; assumption).
    destruct (a_wf_pskl_tophole_inv Hwfr) as [HgQ HwQ0].
    assert (HwQ : Θ ⨟ Δ ⊢ₚₛᵃ Q)
      by (eapply a_wf_pskl_delta_mono; [ exact HwQ0 | clear; fsetdec ]).
    revert Heq; induction Hp; intros Heq; simpl in Heq; try discriminate Heq.
    + rewrite Heq. exact Hrr.
    + (* upre__tophole *)
      inversion Heq; subst.
      simpl. apply ad_refine_pskl__tophole_keep; [ exact H | ].
      eapply IHHr;
        [ exact Hwf | exact Hdisj | exact HwQ
        | eassumption | exact Hmon | reflexivity ].
    + (* upre__topholeg *)
      inversion Heq; subst.
      simpl. apply ad_refine_pskl__tophole_keep; [ exact H | ].
      eapply IHHr;
        [ exact Hwf | exact Hdisj | exact HwQ
        | eassumption | exact Hmon | reflexivity ].
    + (* upre__tophole_keepg *)
      inversion Heq; subst.
      simpl. apply ad_refine_pskl__tophole_keep; [ exact H | ].
      eapply IHHr;
        [ exact Hwf | exact Hdisj | exact HwQ
        | eassumption | exact Hmon | reflexivity ].
    + erase_refine_hole Hrr Hwf Hdisj Hwfr Hmon Heq.
    + erase_refine_remove IHHp Heq.
    + erase_refine_flexl Hmon IHHp Heq.
  - (* flex_l *)
    assert (Hrr : Θ ⨟ Δ ⊢ᵣₚᵃ (pskl_var_f α) ⊳ Q)
      by (eapply ad_refine_pskl__flex_l; eassumption).
    revert Heq; induction Hp; intros Heq; simpl in Heq; try discriminate Heq.
    + rewrite Heq. exact Hrr.
    + erase_refine_hole Hrr Hwf Hdisj Hwfr Hmon Heq.
    + erase_refine_remove IHHp Heq.
    + erase_refine_flexl Hmon IHHp Heq.
    + (* flex_r : the precise side unfolds the SAME definition (unique by
         wf); recurse into the definition's subderivation *)
      inversion Heq; subst.
      match goal with
        Hb : binds _ (abind_flex_mono_def ?t) Θb |- _ =>
        assert (Heqτ : t = τ) by
          (pose proof (a_wf_aenv_uniq Hwf) as Hu;
           pose proof (binds_unique _ _ _ _ _ (Hmon _ _ Hb) H Hu) as He;
           inversion He; reflexivity)
      end.
      subst.
      eapply IHHr;
        [ exact Hwf | exact Hdisj | exact Hwfr
        | eassumption | exact Hmon | apply uskl_to_pskl_ptyp ].
  - (* flex_r *)
    eapply ad_refine_pskl__flex_r; [ eassumption | ].
    eapply IHHr;
      [ exact Hwf | exact Hdisj
      | apply a_wf_ptyp_to_wf_pskl;
        eapply a_wf_aenv_binds_def_wf; [ exact Hwf | exact H ]
      | exact Hp | exact Hmon | exact Heq ].
Qed.
