(** CONSISTENCY SUBJECT-PRECISION METATHEORY (completeness track).

    The consistency-side lemma family behind the paper's
    [lemma:precision-substitution] (subtyping-proofs.tex:1664): in
    [ad_pat_sub] the tag context is consumed by the CONSISTENCY premises, so
    substituting a more-precise (ghostier) [Pa] for a decorated instantiation
    [ψa] in a subtyping subject reduces, on every consistency premise, to
    SUBJECT-precision preserving consistency (docs/
    DESIGN-completeness-subtyping.md §5.2).  This file holds that
    consistency-level metatheory:

    - general tag/wf helpers shared with sub/prop_completeness_sub_precise.v (the
      [pskl_no_forall] kit, [a_wf_pskl] Δ-stripping, [d_tags_skl] /
      [a_tags_sort] inversions and congruences);
    - crux (1a) [ad_pat_consis_strip_tags]: strip the decorated subject to
      its plain skeleton (tags → ∅);
    - crux (1b) [ad_pat_consis_subject_refine]: transport the subject DOWN a
      refinement (subject-side mirror of the Qed target-side
      [ad_pat_consis_refine_inh_gen], prop_soundness_subtag.v), with the
      wf-carrying transporters it needs;
    - crux (1) [ad_pat_consis_subject_precise] = (1a);(1b);
    - step (2) [ad_pat_consis_precise_subst]: the general subject
      SUBSTITUTION [R[ψa/α] ∼ Q  ⇒  R[Pa/α] ∼ Q], by induction on the
      consistency derivation, whose [R = α] case is crux (1).  Its tag
      bookkeeping needs the syntactic-tag reading ([ftag_in_uskl],
      fresco/def_shapes.v): the tag context is contained in the subject's tags
      ([ad_pat_consis_ftag_sub]), and the paper's [fresh Ψ'] side condition
      is rendered as disjointness from the subject's OTHER tags
      ([inter Ψ' (ftag R) = ∅]).  Consistency has no ForallL, so no new
      tags appear inside a derivation and the syntactic premise suffices —
      unlike the subtyping level (see sub/prop_completeness_sub_precise.v). *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.def_shapes.
Require Import src.fresco.coercions.
Require Import src.fresco.prop_basic.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.decl.prop_skeleton.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.def_meta.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo.prop_inc.
Require Import src.fresco.algo.prop_basic.
Require Import src.fresco.algo.prop_stability.
Require Import src.fresco.algo.prop_refine.
Require Import src.fresco.algo.consis.prop_soundness_consis.
Require Import src.fresco.algo.consis.prop_completeness_consis.
Require Import src.fresco.algo.prop_mono_bridge.
Require Import src.fresco.algo.prop_precise.
Require Import src.fresco.algo.prop_pat_sub.

Set Implicit Arguments.

(* ===================================================================== *)
(*  General tag / wf helpers (shared with sub/prop_completeness_sub_precise.v).  *)
(* ===================================================================== *)

(** A pskl with no synthesised quantifier: [inh] and [syn] paintings then
    coincide (they differ only at [pskl_all_syn]). *)
Fixpoint pskl_no_forall (P : pskl) : Prop :=
  match P with
  | pskl_all_syn _ => False
  | pskl_arrow P1 P2 => pskl_no_forall P1 /\ pskl_no_forall P2
  | pskl_univ_ghost P0 => pskl_no_forall P0
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

(** Empty tags ⇒ the erasure is quantifier-free ([all_tag] always carries a
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

Lemma d_tags_skl_all_tag_inv : forall Ψ ε ψ,
  d_tags_skl Ψ (uskl_all_tag ε ψ) ->
  exists L Ψ0,
    (forall α, α `notin` L ->
       d_tags_skl Ψ0 (open_uskl_wrt_uskl ψ (uskl_var_f α)))
    /\ ε `notin` Ψ0 /\ Ψ [=] add ε Ψ0.
Proof. intros Ψ ε ψ H. inversion H; subst. eauto 8. Qed.

Lemma d_tags_skl_dot_univ_ghost_inv : forall Ψ ψ,
  d_tags_skl Ψ (uskl_dot_univ_ghost ψ) -> d_tags_skl Ψ ψ.
Proof. intros Ψ ψ H. inversion H; subst; auto. Qed.
(** Recover the tag reading / re-tag under set-equality. *)
Lemma a_tags_sort_d_tags : forall NM Ψ ψ,
  a_tags_sort NM Ψ ψ -> d_tags_skl Ψ ψ.
Proof. intros NM Ψ ψ H. inversion H; auto. Qed.

Lemma a_tags_sort_psi_cong : forall NM Ψ Ψ' ψ,
  a_tags_sort NM Ψ ψ -> Ψ [=] Ψ' -> a_tags_sort NM Ψ' ψ.
Proof.
  intros NM Ψ Ψ' ψ H Heq. inversion H; subst;
    [ apply a_tags_sort__sk | apply a_tags_sort__ty ]; auto;
    eapply d_tags_skl_psi_cong; eauto.
Qed.

(** Structural inversions of [a_tags_sort] (both modes at once), carrying the
    tag decomposition needed to pin the sub-derivations' tag sets. *)
Lemma a_tags_sort_arrow_inv : forall NM Ψ ψ1 ψ2,
  a_tags_sort NM Ψ (uskl_arrow ψ1 ψ2) ->
  exists Ψ1 Ψ2, a_tags_sort NM Ψ1 ψ1 /\ a_tags_sort NM Ψ2 ψ2
             /\ Ψ1 ∩ Ψ2 [=] empty /\ Ψ [=] Ψ1 `union` Ψ2.
Proof.
  intros NM Ψ ψ1 ψ2 H. inversion H; subst;
    match goal with Ht : is_dskl _ |- _ => inversion Ht; subst end;
    match goal with Hd : d_tags_skl _ (uskl_arrow _ _) |- _ =>
      apply d_tags_skl_arrow_inv in Hd as [Ψa [Ψb [Hd1 [Hd2 [Hdisj Hun]]]]] end.
  - exists Ψa, Ψb. repeat apply conj; try assumption; apply a_tags_sort__sk; auto.
  - match goal with Hg : uskl_ghost_free (uskl_arrow _ _) |- _ =>
      inversion Hg; subst end.
    exists Ψa, Ψb. repeat apply conj; try assumption; apply a_tags_sort__ty; auto.
Qed.

Lemma a_tags_sort_all_tag_inv : forall NM Ψ ε ψ,
  a_tags_sort NM Ψ (uskl_all_tag ε ψ) ->
  exists L Ψ0,
    (forall α, α `notin` L ->
       a_tags_sort NM Ψ0 (open_uskl_wrt_uskl ψ (uskl_var_f α)))
    /\ ε `notin` Ψ0 /\ Ψ [=] add ε Ψ0.
Proof.
  intros NM Ψ ε ψ H. inversion H; subst.
  - (* sk *)
    match goal with Hit : is_dskl (uskl_all_tag _ _) |- _ =>
      inversion Hit; subst end.
    match goal with Hd : d_tags_skl _ (uskl_all_tag _ _) |- _ =>
      apply d_tags_skl_all_tag_inv in Hd as [Ld [Ψ0 [Hd0 [Hεt Hun]]]] end.
    match goal with Hit0 : forall α, α `notin` ?Li -> is_dskl _ |- _ =>
      exists (Li `union` Ld), Ψ0; repeat apply conj; try assumption;
      intros α Hα; apply a_tags_sort__sk; [ apply Hit0 | apply Hd0 ]; fsetdec end.
  - (* ty *)
    match goal with Hit : is_dskl (uskl_all_tag _ _) |- _ =>
      inversion Hit; subst end.
    match goal with Hd : d_tags_skl _ (uskl_all_tag _ _) |- _ =>
      apply d_tags_skl_all_tag_inv in Hd as [Ld [Ψ0 [Hd0 [Hεt Hun]]]] end.
    match goal with Hgf : uskl_ghost_free (uskl_all_tag _ _) |- _ =>
      inversion Hgf; subst end.
    match goal with
    | Hit0 : forall α, α `notin` ?Li -> is_dskl _,
      Hgf0 : forall α, α `notin` ?Lg -> uskl_ghost_free _ |- _ =>
      exists (Li `union` Lg `union` Ld), Ψ0; repeat apply conj; try assumption;
      intros α Hα;
      apply a_tags_sort__ty; [ apply Hit0 | apply Hd0 | apply Hgf0 ]; fsetdec
    end.
Qed.

(* ===================================================================== *)
(*  P5b-ii — precision-substitution, foundational crux.                    *)
(*  The paper's no-type-mismatch step is, on the consistency premises,       *)
(*  subject-precision preserving consistency.  Built in two steps           *)
(*  consistency.  Built in two steps (DESIGN §5.2): (1a) strip the          *)
(*  decorated subject to plain (tags drop to ∅); (1b) transport the erased  *)
(*  subject along the refinement — the SUBJECT-side mirror of the Qed       *)
(*  target-side [ad_pat_consis_refine_inh_gen] (prop_soundness_subtag.v).          *)
(* ===================================================================== *)

(** (1a) Stripping the decorated subject to its plain skeleton preserves
    consistency; the subject is then tag-free so the tag context is [∅]. *)
Lemma ad_pat_consis_strip_tags : forall Ψt Θ ψa Q,
  {{ Ψt ⨟ Θ ⊢ˢ ψa ∼ Q }}ad ->
  {{ empty ⨟ Θ ⊢ˢ (pskl_to_uskl (uskl_to_pskl ψa)) ∼ Q }}ad.
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
  - change bskl_ghost with (pskl_to_bskl_inh pskl_ghost).
    apply ad_pat_consis__ghost; [ reflexivity | apply a_wf_pskl__ghost ].
  - (* dot_univ_ghost: stripping the dotted ghost yields a plain [univ_ghost] *)
    apply ad_pat_consis__univ_ghost. exact IHad_pat_consis.
  - apply ad_pat_consis__ghost; [ reflexivity | exact H0 ].
  - apply ad_pat_consis__univ_ghost. exact IHad_pat_consis.
  - eapply ad_pat_consis__univ_ghost_inh with (L := L).
    intros α Hα. specialize (H0 α Hα). simpl in H0. exact H0.
  - apply ad_pat_consis__univ_ghost_drop. exact IHad_pat_consis.
  - eapply ad_pat_consis__flex_l; [ exact H | ].
    rewrite uskl_to_pskl_ptyp_to_uskl_syn, pskl_to_uskl_ptyp in IHad_pat_consis.
    exact IHad_pat_consis.
  - eapply ad_pat_consis__flex_r; [ exact H | exact IHad_pat_consis ].
Qed.

(** WF bridge for a ∀-target: the erased opened body is wf with the ∀-var
    as a TVAR in [Θ] (which the consistency transport needs), from the opened
    body as [a_wf_pskl_all_inv] gives it (the ∀-var in BOTH [Θ] and [Δ]):
    dropping it from [Δ] only relaxes the check. *)
Lemma wf_open_of_all : forall Θ Δ Q0 α,
  {{ ((α ~ abind_tvar) ++ Θ) ⨟ (add α Δ)
    ⊢ₚₛ open_pskl_wrt_pskl (bskl_to_pskl Q0) (pskl_var_f α) }}a ->
  {{ ((α ~ abind_tvar) ++ Θ) ⨟ Δ
    ⊢ₚₛ bskl_to_pskl (open_bskl_wrt_bskl Q0 (bskl_var_f α)) }}a.
Proof.
  intros Θ Δ Q0 α Hb.
  rewrite bskl_to_pskl_open.
  eapply a_wf_pskl_delta_mono; [ exact Hb | ].
  intros β2 _ HW. clear - HW. fsetdec.
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

(** (1b) ghost-case leaf (EQUATION ONLY): a CONCRETE, ∀-free subject
    [pskl_to_uskl P] consistent with [Q] forces [Q] to be an inh-painting of
    its own erasure — [inh (bskl_to_pskl Q) = Q] — with empty tags.  That is
    ALL the main lemma's ghost case needs: combined with a THREADED
    [Θ ⊢ bskl_to_pskl Q] (well-formedness is an INPUT, not a conclusion — cf.
    [ad_pat_consis_refine_inh_gen]'s [Bsrc] premise), [uskl_ghost ∼ Q] follows
    by [__ghost] with [B := bskl_to_pskl Q].  Proving only the EQUATION avoids
    reconstructing the wf of a ∀-witness under the [Θ↔Δ] tension (which is not
    a general fact — a [∀◇] body cannot reference a Δ-var). *)
Lemma consis_concrete_target_inh : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  {{ ⊢ Θ }}a ->
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
  - (* forall_inh_tagged: subject all_tag — impossible *)
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
  - (* dot_univ_ghost *)
    destruct P0 as [ | n | αv | Pl Pr | Pq | | Pt ]; simpl in HR; discriminate HR.
  - (* ghost *)
    split; [ exact H
           | simpl; rewrite bskl_to_pskl_pskl_to_bskl_inh; reflexivity ].
  - (* univ_ghost: bskl_univ_ghost Q0 *)
    destruct P0 as [ | n | αv | Pl Pr | Pq | | Pt ];
      simpl in HR; try discriminate HR. inversion HR; subst.
    simpl in Hnf.
    destruct (IHHc Hwfa _ eq_refl Hnf) as [HΨ0 Heq0].
    split; [ exact HΨ0 | simpl; rewrite Heq0; reflexivity ].
  - (* univ_ghost_inh: bskl_all_inh Q0 — close the opened equation via open-inj *)
    destruct P0 as [ | n | αv | Pl Pr | Pq | | Pt ];
      simpl in HR; try discriminate HR. inversion HR; subst.
    simpl in Hnf.
    pick fresh α for (L `union` dom Θ `union` ftvar_in_bskl Q).
    assert (HwfX : {{ ⊢ ((α ~ abind_tvar) ++ Θ) }}a)
      by (apply a_wf_aenv__tvar; [ fsetdec | exact Hwfa ]).
    destruct (H0 α ltac:(solve_notin_auto) HwfX (pskl_univ_ghost Pt) eq_refl Hnf)
      as [HΨα HeqX].
    split; [ exact HΨα | ].
    simpl. f_equal.
    eapply open_bskl_wrt_bskl_inj with (α1 := α).
    + rewrite ftvar_in_bskl_inh, ftvar_bskl_to_pskl. fsetdec.
    + fsetdec.
    + rewrite <- pskl_to_bskl_inh_open, <- bskl_to_pskl_open. exact HeqX.
  - (* univ_ghost_drop: Q arbitrary *)
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

(* ===================================================================== *)
(*  Step (2) infrastructure — syntactic tags [ftag_in_uskl] (fresco/def_shapes.v). *)
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

(* ⚙ RESTART NOTE (2026-08-11): [ftag_in_pskl_to_uskl] ("a [pskl] painting is
   tag-free", [induction P; simpl; fsetdec]) lived here and had NO consumer;
   deleted along with [ftag_in_bskl_to_uskl], which duplicated
   fresco/prop_coercions.v §5's [ftag_bskl_to_uskl]. *)

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
    tags — every solved tag is consumed at an [all_tag] node of the
    subject.  (Syntactic counterpart of [ad_partial_precise_tags_sub],
    above; the precision-substitution crux uses it to pin
    the residual tag context of a wholly-[ψa] subject to ∅.) *)
Lemma ad_pat_consis_ftag_sub : forall Ψ Θ R' Q,
  {{ Ψ ⨟ Θ ⊢ˢ R' ∼ Q }}ad ->
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
  - (* univ_ghost_inh: subject fixed under the target binder *)
    pick fresh α for L;
    pose proof (H0 α ltac:(solve_notin_auto)) as Hα; simpl in Hα; fsetdec.
  - (* flex_l: the unfolded def is a painted monotype — tag-free *)
    match goal with H0 : _ [<=] ftag_in_uskl (ptyp_to_uskl_syn ?t) |- _ =>
      pose proof (ftag_ptyp_to_uskl_syn t) end; fsetdec.
Qed.

(* ===================================================================== *)
(*  Step (2) — the [R = α] crux case, packaged: a wholly-[ψa] subject      *)
(*  transports to [Pa] with residual tag context ∅ (= Ψ).                  *)
(* ===================================================================== *)

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
(*  a tag shared between an [all_tag] of [R] and one of [ψa] makes the    *)
(*  conclusion underivable (the [R]-node is forced to re-consume a tag     *)
(*  that substitution removed).  Consistency derivations introduce no new  *)
(*  tags (no ForallL), so the syntactic premise is stable under the        *)
(*  induction.                                                             *)
(* ===================================================================== *)

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
(*  substitution leaves on both sides.  [univ_ghost_fill] has NO mirror: the  *)
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
| upre__all_tag : forall L Ψrep ε R' R,
    (forall α, α `notin` L ->
       uskl_precise Θ Ψrep
         (open_uskl_wrt_uskl R' (uskl_var_f α))
         (open_uskl_wrt_uskl R (uskl_var_f α))) ->
    uskl_precise Θ Ψrep (uskl_all_tag ε R') (uskl_all_tag ε R)
| upre__all_inst : forall L Ψrep Ψ0 ε R' R,
    (forall α, α `notin` L ->
       uskl_precise Θ Ψ0
         (open_uskl_wrt_uskl R' (uskl_var_f α))
         (open_uskl_wrt_uskl R (uskl_var_f α))) ->
    Ψrep [=] add ε Ψ0 ->
    uskl_precise Θ Ψrep (uskl_all_syn R') (uskl_all_tag ε R)
| upre__univ_ghost : forall Ψrep R' R,
    uskl_precise Θ Ψrep R' R ->
    uskl_precise Θ Ψrep (uskl_univ_ghost R') (uskl_univ_ghost R)
| upre__dot_univ_ghost : forall Ψrep R' R,
    uskl_precise Θ Ψrep R' R ->
    uskl_precise Θ Ψrep (uskl_dot_univ_ghost R') (uskl_dot_univ_ghost R)
| upre__univ_ghost_keepg : forall Ψrep R' R,
    uskl_precise Θ Ψrep R' R ->
    uskl_precise Θ Ψrep (uskl_univ_ghost R') (uskl_dot_univ_ghost R)
| upre__ghost : forall Ψrep R,
    Ψrep [=] empty ->
    pskl_no_forall (uskl_to_pskl R) ->
    {{ Θ ⨟ empty ⊢ₚₛ (uskl_to_pskl R) }}a ->
    uskl_precise Θ Ψrep uskl_ghost R
| upre__univ_ghost_remove : forall Ψrep R' R,
    uskl_precise Θ Ψrep R' R ->
    uskl_precise Θ Ψrep (uskl_univ_ghost R') R
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
  - eapply upre__all_tag with (L := L); intros α Hα; eauto.
  - eapply upre__all_inst with (L := L) (Ψ0 := Ψ0);
      [ intros α Hα; eauto | fsetdec ].
  - apply upre__univ_ghost; eauto.
  - apply upre__dot_univ_ghost; eauto.
  - apply upre__univ_ghost_keepg; eauto.
  - apply upre__ghost; [ fsetdec | assumption | assumption ].
  - apply upre__univ_ghost_remove; eauto.
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
  - (* all_tag cong *)
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
    pose proof (ftag_ptyp_to_uskl_syn τ). fsetdec.
Qed.

(** ∀-free erasure ⇒ no tags (all_tag erases to a quantifier). *)
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
    skeleton on BOTH sides — the ForallL-crux enabler.  The ghost rule
    survives because its target is wf in the EMPTY Δ, hence [α]-free. *)
Lemma uskl_precise_subst : forall Θ Ψrep R' R,
  uskl_precise Θ Ψrep R' R ->
  forall α' ψs,
  lc_uskl ψs ->
  {{ ⊢ Θ }}a ->
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
  - (* all_tag cong *)
    apply upre__all_tag with (L := L `union` singleton α0).
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
  - (* univ_ghost cong *)
    apply upre__univ_ghost; apply IHHup; assumption.
  - (* dot_univ_ghost cong *)
    apply upre__dot_univ_ghost; apply IHHup; assumption.
  - (* univ_ghost_keepg *)
    apply upre__univ_ghost_keepg; apply IHHup; assumption.
  - (* ghost *)
    assert (Hfr : α0 `notin` ftvar_in_uskl R).
    { pose proof (a_wf_pskl_ftv_dom H1) as Hsc.
      rewrite ftvar_in_pskl_uskl_to_pskl in Hsc.
      clear - Hsc Hα. fsetdec. }
    rewrite (subst_uskl_in_uskl_fresh_eq R ψs α0 Hfr).
    apply upre__ghost; assumption.
  - (* univ_ghost_remove *)
    apply upre__univ_ghost_remove; apply IHHup; assumption.
  - (* flex_l *)
    assert (Hdom : α `in` dom Θ) by (eapply binds_In; exact H).
    destruct_if as [-> | Hne]; [ exfalso; clear - Hdom Hα; fsetdec | ].
    eapply upre__flex_l; [ exact H | ].
    assert (Hfrτ : α0 `notin` ftvar_in_uskl (ptyp_to_uskl_syn τ)).
    { rewrite ftvar_ptyp_to_uskl_syn.
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
    { rewrite ftvar_ptyp_to_uskl_syn.
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
    erasure structure against decorated structure ([all_syn]↔[all_tag],
    [univ_ghost]↔[dot_univ_ghost]); [univ_ghost_fill] cannot occur (the ⊑-target is an
    inh-painting, never [all_syn]-headed).

    The refinement's ghost rule no longer checks its fill, so [upre__ghost]'s
    [Θ ⨟ ∅ ⊢ fill] comes from the paper's presupposition that the TARGET is
    well-formed ([Hwft]).  The ∀ rule pushes its variable into BOTH the
    context and [Δ], so the ⊑ᵤ context [Θb] is held FIXED and related to the
    growing [Θ] by the two maps: every non-[Δ] variable of [Θ] is a [Θb]
    variable (a fill is [Δ]-free), and [Θ]'s flexible definitions are
    [Θb]'s. *)
Lemma uskl_precise_of_precise_gen : forall Θ Δ Qsrc Qtgt,
  ad_refine_syn Θ Δ Qsrc Qtgt ->
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δ ⊢ₚₛ bskl_to_pskl Qtgt }}a ->
  forall Θb,
  (forall α, a_binds_tvar α Θ -> α `notin` Δ -> a_binds_tvar α Θb) ->
  (forall α τ, binds α (abind_flex_mono_def τ) Θ ->
     binds α (abind_flex_mono_def τ) Θb) ->
  forall Pa ψt Ψt,
  Qsrc = pskl_to_bskl_inh Pa ->
  Qtgt = pskl_to_bskl_inh (uskl_to_pskl ψt) ->
  is_dskl ψt ->
  d_tags_skl Ψt ψt ->
  uskl_precise Θb Ψt (pskl_to_uskl Pa) ψt.
Proof.
  intros Θ Δ Qsrc Qtgt Hr; induction Hr;
    intros Hwf Hwft Θb Hmtv Hmfl Pa ψt Ψt HSrc HTgt Htsk Hdt.
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
    simpl in Hwft.
    inversion Hwft as [ | | Θz Δz Pw1 Pw2 Hwft1 Hwft2 | | | ]; subst.
    simpl.
    eapply upre__arrow;
      [ eapply IHHr1; try reflexivity; try eassumption
      | eapply IHHr2; try reflexivity; try eassumption
      | exact Hun ].
  - (* all: Pa = all_syn Pa0, ψt = all_tag ε ψ0 *)
    destruct Pa as [ | n | α0 | Pa1 Pa2 | Pa0 | | Pa0 ];
      simpl in HSrc; try discriminate HSrc.
    destruct ψt as [ | n | α0 | ψ1 ψ2 | ψ0 | ε ψ0 | | ψ0 | | ψ0 ];
      simpl in HTgt; try discriminate HTgt;
      [ inversion Htsk | ].
    inversion HSrc; inversion HTgt; subst.
    inversion Htsk as [ | | | Lt ε' ψ0' Ht0 | | ]; subst.
    apply d_tags_skl_all_tag_inv in Hdt
      as [Ld [Ψ0d [Hd0 [Hε Hun]]]].
    simpl in Hwft. destruct (a_wf_pskl_all_inv Hwft) as [Lw Hwbody].
    simpl.
    apply upre__all_inst
      with (L := L `union` Lt `union` Ld `union` Lw `union` dom Θ)
           (Ψ0 := Ψ0d);
      [ | exact Hun ].
    intros α Hα.
    rewrite <- pskl_to_uskl_open_var.
    eapply H1 with (α := α) (ψt := open_uskl_wrt_uskl ψ0 (uskl_var_f α));
      [ clear - Hα; solve_notin_auto
      | apply a_wf_aenv__tvar; [ clear - Hα; solve_notin_auto | exact Hwf ]
      | rewrite bskl_to_pskl_open; apply Hwbody; clear - Hα; solve_notin_auto
      | intros β Hβ HβΔ;
        apply a_binds_tvar_cons_tvar_inv in Hβ as [-> | Hβ];
        [ exfalso; clear - HβΔ; fsetdec
        | apply Hmtv; [ exact Hβ | clear - HβΔ; fsetdec ] ]
      | intros β τ Hb; apply Hmfl; eapply binds_flex_def_cons_tvar_inv; exact Hb
      | symmetry; apply pskl_to_bskl_inh_open
      | rewrite uskl_to_pskl_open; symmetry; apply pskl_to_bskl_inh_open
      | apply Ht0; clear - Hα; solve_notin_auto
      | apply Hd0; clear - Hα; solve_notin_auto ].
  - (* ghost *)
    destruct Pa; simpl in HSrc; try discriminate HSrc.
    assert (Hnf : pskl_no_forall (uskl_to_pskl ψt))
      by (eapply inh_eq_syn_no_forall; symmetry; exact HTgt).
    assert (HeqP : P = uskl_to_pskl ψt).
    { apply pskl_to_bskl_syn_inj.
      rewrite HTgt.
      apply pskl_no_forall_inh_eq_syn. exact Hnf. }
    simpl. apply upre__ghost.
    + pose proof (d_tags_skl_ftag Hdt) as Htg.
      pose proof (no_forall_uskl_ftag _ Hnf) as Hfe.
      clear - Htg Hfe; fsetdec.
    + exact Hnf.
    + (* the fill is wf (target presupposition) and Δ-free (rule premise) *)
      rewrite <- HeqP.
      rewrite bskl_to_pskl_pskl_to_bskl_syn in Hwft.
      assert (Hwf0 : {{ Θ ⨟ empty ⊢ₚₛ P }}a)
        by (eapply a_wf_pskl_delta_mono;
            [ exact Hwft | intros β _ Hβ; clear - Hβ; fsetdec ]).
      eapply a_wf_pskl_tvar_mono_ftv; [ exact Hwf0 | ].
      intros β HβP Hβ. apply Hmtv; [ exact Hβ | ].
      intro HβΔ.
      assert (Hin : β `in` Δ ∩ ftvar_in_pskl P) by (apply inter_3; auto).
      rewrite H in Hin. clear - Hin. fsetdec.
  - (* univ_ghost_remove *)
    destruct Pa as [ | n | α0 | Pa1 Pa2 | Pa0 | | Pa0 ];
      simpl in HSrc; try discriminate HSrc.
    inversion HSrc; subst.
    simpl. apply upre__univ_ghost_remove.
    eapply IHHr; try reflexivity; try eassumption.
  - (* univ_ghost_fill: an inh-painting is never all_syn-headed *)
    destruct ψt; simpl in HTgt; discriminate HTgt.
  - (* univ_ghost_keep: ψt = dot_univ_ghost ψ0 *)
    destruct Pa as [ | n | α0 | Pa1 Pa2 | Pa0 | | Pa0 ];
      simpl in HSrc; try discriminate HSrc.
    destruct ψt as [ | n | α0 | ψ1 ψ2 | ψ0 | ε ψ0 | | ψ0 | | ψ0 ];
      simpl in HTgt; try discriminate HTgt;
      [ inversion Htsk | ].
    inversion HSrc; inversion HTgt; subst.
    inversion Htsk; subst.
    apply d_tags_skl_dot_univ_ghost_inv in Hdt.
    simpl in Hwft. apply a_wf_pskl_univ_ghost_body in Hwft.
    simpl. apply upre__univ_ghost_keepg.
    eapply IHHr; try reflexivity; try eassumption.
  - (* flex_l *)
    destruct Pa as [ | n | α0 | Pa1 Pa2 | Pa0 | | Pa0 ];
      simpl in HSrc; try discriminate HSrc.
    inversion HSrc; subst.
    assert (Hm : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf | exact H ]).
    simpl. eapply upre__flex_l; [ apply Hmfl; exact H | ].
    rewrite <- pskl_to_uskl_ptyp.
    eapply IHHr;
      [ exact Hwf | exact Hwft | exact Hmtv | exact Hmfl
      | symmetry; apply (ptyp_to_bskl_inh_syn_eq Hm)
      | reflexivity | exact Htsk | exact Hdt ].
  - (* flex_r: ψt = var α *)
    destruct ψt as [ | n | α0 | ψ1 ψ2 | ψ0 | ε ψ0 | | ψ0 | | ψ0 ];
      simpl in HTgt; try discriminate HTgt.
    inversion HTgt; subst.
    assert (Hm : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf | exact H ]).
    eapply uskl_precise_psi_cong with (Ψrep := empty);
      [ | pose proof (d_tags_skl_var_inv Hdt); fsetdec ].
    eapply upre__flex_r; [ apply Hmfl; exact H | ].
    eapply IHHr;
      [ exact Hwf
      | unfold ptyp_to_bskl_syn; rewrite bskl_to_pskl_pskl_to_bskl_syn;
        apply a_wf_ptyp_to_wf_pskl;
        eapply a_wf_aenv_binds_def_wf; [ exact Hwf | exact H ]
      | exact Hmtv | exact Hmfl
      | reflexivity
      | rewrite uskl_to_pskl_ptyp_to_uskl_syn;
        symmetry; apply (ptyp_to_bskl_inh_syn_eq Hm)
      | apply mono_ptyp_to_uskl_syn_is_dskl; exact Hm
      | apply (mono_ptyp_to_uskl_syn_tags Hm); reflexivity ].
Qed.

(** The embedding at a single context; [Hwft] is the paper's
    well-formedness presupposition on the refinement's target. *)
Lemma uskl_precise_of_precise : forall Θ Δ Qsrc Qtgt,
  ad_refine_syn Θ Δ Qsrc Qtgt ->
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δ ⊢ₚₛ bskl_to_pskl Qtgt }}a ->
  forall Pa ψt Ψt,
  Qsrc = pskl_to_bskl_inh Pa ->
  Qtgt = pskl_to_bskl_inh (uskl_to_pskl ψt) ->
  is_dskl ψt ->
  d_tags_skl Ψt ψt ->
  uskl_precise Θ Ψt (pskl_to_uskl Pa) ψt.
Proof.
  intros Θ Δ Qsrc Qtgt Hr Hwf Hwft.
  eapply uskl_precise_of_precise_gen;
    [ exact Hr | exact Hwf | exact Hwft
    | intros α Hα _; exact Hα | intros α τ Hb; exact Hb ].
Qed.

(* ===================================================================== *)
(*  (2') — consistency transport over ⊑ᵤ.                                 *)
(*                                                                         *)
(*  [consis_split_transport Θb Ψsup A B] packages: any consistency of the  *)
(*  subject A transports to B, with the tag context dropping by its        *)
(*  Ψsup-portion.  The per-shape transporters below run the inner          *)
(*  induction on the consistency derivation (handling the subject-         *)
(*  preserving rules [flex_r]/[univ_ghost_inh]); the main lemma               *)
(*  [ad_pat_consis_precise_upre] inducts on ⊑ᵤ and packages its IHs into   *)
(*  the functional.  [Ψsup] over-approximates the replaced tags UNIFORMLY  *)
(*  (it is fixed across congruences), which is what makes the arrow case   *)
(*  compositional.                                                         *)
(* ===================================================================== *)

Definition consis_split_transport (Θb : aenv) (Ψsup : atoms) (A B : uskl) :=
  forall Θ' Ψfull Ψn Ψna Q,
    {{ Ψfull ⨟ Θ' ⊢ˢ A ∼ Q }}ad ->
    (forall x b, binds x b Θb -> binds x b Θ') ->
    {{ ⊢ Θ' }}a ->
    Ψfull [=] Ψn `union` Ψna ->
    Ψna [<=] Ψsup ->
    Ψsup ∩ Ψn [=] empty ->
    {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a ->
    {{ Ψn ⨟ Θ' ⊢ˢ B ∼ Q }}ad.

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

Lemma consis_split_transport_all_tag_cong : forall Θb Ψsup ε R0 R0' L0,
  ε `notin` Ψsup ->
  (forall α, α `notin` L0 ->
     consis_split_transport Θb Ψsup
       (open_uskl_wrt_uskl R0 (uskl_var_f α))
       (open_uskl_wrt_uskl R0' (uskl_var_f α))) ->
  consis_split_transport Θb Ψsup (uskl_all_tag ε R0) (uskl_all_tag ε R0').
Proof.
  intros Θb Ψsup ε R0 R0' L0 Hεout Ht.
  intros Θ' Ψfull Ψn Ψna Q Hc Hmon Hwf HΨf HΨa Hdisj Hwfq.
  remember (uskl_all_tag ε R0) as Ssub eqn:HeqS.
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
  consis_split_transport Θb Ψsup (uskl_all_tag ε R0) (uskl_all_syn R0').
Proof.
  intros Θb Ψsup ε R0 R0' L0 Hεin Ht.
  intros Θ' Ψfull Ψn Ψna Q Hc Hmon Hwf HΨf HΨa Hdisj Hwfq.
  remember (uskl_all_tag ε R0) as Ssub eqn:HeqS.
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

Lemma consis_split_transport_univ_ghost : forall Θb Ψsup R0 R0',
  consis_split_transport Θb Ψsup R0 R0' ->
  consis_split_transport Θb Ψsup (uskl_univ_ghost R0) (uskl_univ_ghost R0').
Proof.
  intros Θb Ψsup R0 R0' Ht.
  intros Θ' Ψfull Ψn Ψna Q Hc Hmon Hwf HΨf HΨa Hdisj Hwfq.
  remember (uskl_univ_ghost R0) as Ssub eqn:HeqS.
  revert Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  induction Hc; try discriminate HeqS;
    intros Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  - (* univ_ghost: target ∀◇ *)
    inversion HeqS; subst.
    simpl in Hwfq. destruct (a_wf_pskl_univ_ghost_inv Hwfq) as [Hg Hwb].
    apply ad_pat_consis__univ_ghost.
    eapply Ht with (Ψna := Ψna);
      [ exact Hc | exact Hmon | exact Hwf
      | exact HΨf | exact HΨa | exact Hdisj | exact Hwb ].
  - (* univ_ghost_inh: subject fixed, target opens under an extended context *)
    inversion HeqS; subst.
    simpl in Hwfq. destruct (a_wf_pskl_all_inv Hwfq) as [Lw Hwbody].
    eapply ad_pat_consis__univ_ghost_inh with
      (L := L `union` Lw `union` dom Θ).
    intros α Hα.
    eapply (H0 α ltac:(clear - Hα; solve_notin_auto) eq_refl Ψn Ψna HΨf HΨa Hdisj);
      [ intros x b Hb; unfold binds; simpl; right; apply Hmon; exact Hb
      | apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ]
      | apply wf_open_of_all; apply Hwbody; clear - Hα; fsetdec ].
  - (* univ_ghost_drop *)
    inversion HeqS; subst.
    apply ad_pat_consis__univ_ghost_drop.
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

(** Both dotted (dot_univ_ghost-vs-dot_univ_ghost) and mixed (univ_ghost-vs-dot_univ_ghost)
    ∀◇-transporters; the DERIVATION's subject is the dotted one. *)
Lemma consis_split_transport_dot_univ_ghost : forall Θb Ψsup R0 R0',
  consis_split_transport Θb Ψsup R0 R0' ->
  consis_split_transport Θb Ψsup (uskl_dot_univ_ghost R0) (uskl_dot_univ_ghost R0').
Proof.
  intros Θb Ψsup R0 R0' Ht.
  intros Θ' Ψfull Ψn Ψna Q Hc Hmon Hwf HΨf HΨa Hdisj Hwfq.
  remember (uskl_dot_univ_ghost R0) as Ssub eqn:HeqS.
  revert Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  induction Hc; try discriminate HeqS;
    intros Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  - (* dot_univ_ghost *)
    inversion HeqS; subst.
    simpl in Hwfq. destruct (a_wf_pskl_univ_ghost_inv Hwfq) as [Hg Hwb].
    apply ad_pat_consis__dot_univ_ghost.
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
  consis_split_transport Θb Ψsup (uskl_dot_univ_ghost R0) (uskl_univ_ghost R0').
Proof.
  intros Θb Ψsup R0 R0' Ht.
  intros Θ' Ψfull Ψn Ψna Q Hc Hmon Hwf HΨf HΨa Hdisj Hwfq.
  remember (uskl_dot_univ_ghost R0) as Ssub eqn:HeqS.
  revert Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  induction Hc; try discriminate HeqS;
    intros Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  - (* dot_univ_ghost → univ_ghost (plain keep) *)
    inversion HeqS; subst.
    simpl in Hwfq. destruct (a_wf_pskl_univ_ghost_inv Hwfq) as [Hg Hwb].
    apply ad_pat_consis__univ_ghost.
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
  - (* all_tag cong *)
    assert (Hεout : ε `notin` Ψsup) by (clear - Hftag; fsetdec).
    apply consis_split_transport_all_tag_cong with (L0 := L);
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
  - (* univ_ghost cong *)
    apply consis_split_transport_univ_ghost.
    apply IHHup; [ exact HΨsup | clear - Hftag; fsetdec ].
  - (* dot_univ_ghost cong *)
    apply consis_split_transport_dot_univ_ghost.
    apply IHHup; [ exact HΨsup | clear - Hftag; fsetdec ].
  - (* univ_ghost_keepg *)
    apply consis_split_transport_keepg.
    apply IHHup; [ exact HΨsup | clear - Hftag; fsetdec ].
  - (* ghost *)
    intros Θ' Ψfull Ψn Ψna Q Hc Hmon Hwf HΨf HΨa Hdisj Hwfq.
    assert (HΨe : Ψn [=] empty).
    { pose proof (ad_pat_consis_ftag_sub Hc) as Hfs.
      pose proof (no_forall_uskl_ftag _ H0) as Hfe.
      clear - Hfs Hfe HΨf; fsetdec. }
    pose proof (ad_pat_consis_strip_tags Hc) as Hstr.
    destruct (consis_concrete_target_inh Hstr Hwf (uskl_to_pskl R) eq_refl H0)
      as [_ Heqinh].
    rewrite <- Heqinh.
    apply ad_pat_consis__ghost; [ exact HΨe | exact Hwfq ].
  - (* univ_ghost_remove *)
    intros Θ' Ψfull Ψn Ψna Q Hc Hmon Hwf HΨf HΨa Hdisj Hwfq.
    apply ad_pat_consis__univ_ghost_drop.
    assert (Hftag' : Ψsup ∩ ftag_in_uskl R' [=] empty)
      by (clear - Hftag; fsetdec).
    exact (IHHup Ψsup HΨsup Hftag' Θ' Ψfull Ψn Ψna Q
             Hc Hmon Hwf HΨf HΨa Hdisj Hwfq).
  - (* flex_l *)
    intros Θ' Ψfull Ψn Ψna Q Hc Hmon Hwf HΨf HΨa Hdisj Hwfq.
    eapply ad_pat_consis__flex_l; [ apply Hmon; exact H | ].
    assert (Hftag' : Ψsup ∩
                       (ftag_in_uskl (ptyp_to_uskl_syn τ)) [=] empty)
      by (pose proof (ftag_ptyp_to_uskl_syn τ) as Hpt; clear - Hpt; fsetdec).
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
  - (* all_tag cong *)
    pick fresh α for L.
    pose proof (H0 α ltac:(solve_notin_auto)) as Hα.
    pose proof (ftag_in_uskl_open_var R α); fsetdec.
  - (* all_inst *)
    pick fresh α for L.
    pose proof (H0 α ltac:(solve_notin_auto)) as Hα.
    pose proof (ftag_in_uskl_open_var R α); fsetdec.
  - (* flex_r *)
    pose proof (ftag_ptyp_to_uskl_syn τ); fsetdec.
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
    apply lc_uskl_all_tag_exists with (α1 := α). apply H0; fsetdec.
  - pick fresh α for L.
    apply lc_uskl_all_syn_exists with (α1 := α). apply H0; fsetdec.
  - apply lc_uskl_univ_ghost; assumption.
  - apply lc_uskl_dot_univ_ghost; assumption.
  - apply lc_uskl_univ_ghost; assumption.
  - apply lc_uskl_ghost.
  - apply lc_uskl_univ_ghost; assumption.
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
  - (* all_tag *)
    assert (Hlcψ' : lc_uskl ψ') by (eapply uskl_precise_lc_l; exact Hp).
    apply upre__all_tag with (L := singleton α0).
    intros β Hβ.
    assert (Hne : α0 <> β) by (clear - Hβ; fsetdec).
    rewrite (subst_uskl_in_uskl_open_uskl_wrt_uskl_var R ψ' α0 β Hne Hlcψ').
    rewrite (subst_uskl_in_uskl_open_uskl_wrt_uskl_var R ψ α0 β Hne Hlcψ).
    apply H0; [ exact Hp | exact Hlcψ | ].
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f β))
      as Hlo.
    clear - Hin Hlo; fsetdec.
  - (* ghost *) exfalso; clear - Hin; fsetdec.
  - (* univ_ghost *)
    apply upre__univ_ghost. apply IHHlc; assumption.
  - (* dot_ghost *) exfalso; clear - Hin; fsetdec.
  - (* dot_univ_ghost *)
    apply upre__dot_univ_ghost. apply IHHlc; assumption.
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
(*  The [upre__ghost] crux (concluding [□ ⊳ Qr] needs [Δ ∩ ftv Qr = ∅]) is  *)
(*  the Δ-discipline of prop_precise.v: the precise side's erasure is wf  *)
(*  at [Θb ⨟ ∅] (the [upre__ghost] premise), hence Δ-free because Δ is     *)
(*  fresh for the FIXED [Θb]; and Δ-freeness propagates across a          *)
(*  refinement ([ad_refine_pskl_ftv_policed]) as long as no flexible      *)
(*  variable is a Δ-variable and no flexible definition mentions one.     *)
(*  Those two hypotheses survive the [all] rule (which puts its variable  *)
(*  into Θ AND Δ), whereas Δ's freshness for Θ does not — hence the       *)
(*  [_gen] form, of which the Δ-fresh statement is a corollary.           *)
(* ===================================================================== *)

(** A subset of Δ that no flexible variable or definition mentions, and that
    is absent from the source, stays absent from the target: everything a
    refinement step introduces is a fill (Δ-free by the ghost rule), a
    flexible definition, a flexible variable, or a binder the target
    immediately re-binds. *)
Lemma ad_refine_pskl_ftv_policed : forall Θ Δ P Q,
  {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ Q }}ad ->
  forall S,
  S [<=] Δ ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     S ∩ ftvar_in_ptyp τ [=] empty) ->
  (forall β τ, β `in` S -> ~ binds β (abind_flex_mono_def τ) Θ) ->
  S ∩ ftvar_in_pskl P [=] empty ->
  S ∩ ftvar_in_pskl Q [=] empty.
Proof.
  intros Θ Δ P Q Href; induction Href; intros S HSΔ Hdefs Hflex Hsrc;
    simpl in Hsrc |- *.
  - (* unit *) exact Hsrc.
  - (* var *) exact Hsrc.
  - (* arrow *)
    assert (Hs1 : S ∩ ftvar_in_pskl P1 [=] empty) by (clear - Hsrc; fsetdec).
    assert (Hs2 : S ∩ ftvar_in_pskl P2 [=] empty) by (clear - Hsrc; fsetdec).
    pose proof (IHHref1 S HSΔ Hdefs Hflex Hs1) as Ht1.
    pose proof (IHHref2 S HSΔ Hdefs Hflex Hs2) as Ht2.
    clear - Ht1 Ht2; fsetdec.
  - (* all *)
    pick fresh α for (L `union` S `union` ftvar_in_pskl P `union` ftvar_in_pskl P').
    destruct (@delta_flex_defs_cons_tvar α Θ S Hdefs Hflex) as [Hdefs' Hflex'].
    assert (Hs0 : S ∩ ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f α))
                    [=] empty).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                    P (pskl_var_f α)) as Hup.
      simpl in Hup. clear - Hsrc Hup Fr. fsetdec. }
    pose proof (H0 α ltac:(clear - Fr; solve_notin_auto) S
                  ltac:(clear - HSΔ; fsetdec) Hdefs' Hflex' Hs0) as Ht.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_lower
                  P' (pskl_var_f α)) as Hlo.
    clear - Ht Hlo. fsetdec.
  - (* ghost : the fill is Δ-free by the rule's own premise *)
    clear - H HSΔ. fsetdec.
  - (* univ_ghost_remove *)
    apply IHHref; auto.
  - (* univ_ghost_fill : the fresh binder is re-bound by the target ∀ *)
    pick fresh α for (L `union` S `union` ftvar_in_pskl P').
    destruct (@delta_flex_defs_cons_tvar α Θ S Hdefs Hflex) as [Hdefs' Hflex'].
    pose proof (H0 α ltac:(clear - Fr; solve_notin_auto) S HSΔ
                  Hdefs' Hflex' Hsrc) as Ht.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_lower
                  P' (pskl_var_f α)) as Hlo.
    clear - Ht Hlo. fsetdec.
  - (* univ_ghost_keep *)
    apply IHHref; auto.
  - (* flex_l : the definition is Δ-free *)
    apply IHHref; auto.
    rewrite ftvar_ptyp_to_pskl. eapply Hdefs; exact H.
  - (* flex_r : the target variable is flexible, never in S *)
    apply inter_empty_pointwise. intros β Hβ. intro Hc.
    assert (Heqβ : β = α) by (clear - Hc; fsetdec). subst β.
    exact (Hflex α τ Hβ H).
Qed.

(** The left-hand ghost rule, in the shape the [upre__ghost] rows need: a
    ghost refines to anything a Δ-free source refines to. *)
Lemma ad_refine_pskl_ghost_l : forall Θ Δ Qm Qr,
  {{ Θ ⨟ Δ ⊢ᵣₚ Qm ⊳ Qr }}ad ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     Δ ∩ ftvar_in_ptyp τ [=] empty) ->
  (forall β τ, β `in` Δ -> ~ binds β (abind_flex_mono_def τ) Θ) ->
  Δ ∩ ftvar_in_pskl Qm [=] empty ->
  {{ Θ ⨟ Δ ⊢ᵣₚ pskl_ghost ⊳ Qr }}ad.
Proof.
  intros Θ Δ Qm Qr Href Hdefs Hflex Hsrc.
  apply ad_refine_pskl__ghost.
  eapply ad_refine_pskl_ftv_policed;
    [ exact Href | clear; fsetdec | exact Hdefs | exact Hflex | exact Hsrc ].
Qed.

(** ⊑ᵤ against a MONOTYPE syn painting: the ghostier side's erasure
    refines to the painted monotype.  Self-contained (a monotype painting
    is unit / var / arrow, so no binder rows fire); handles the flex-var
    unfolding rows of the main lemma, where the refinement side is
    exhausted while the precision keeps unfolding definitions.  The ghost
    rule needs the monotype — and every flexible definition it unfolds
    to — to be Δ-free. *)
Lemma uskl_precise_mono_refine : forall Θb Ψr R' R,
  uskl_precise Θb Ψr R' R ->
  forall Θ Δ τ',
  R = ptyp_to_uskl_syn τ' ->
  mono_ptyp τ' ->
  (forall x (b : abind), binds x b Θb -> binds x b Θ) ->
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ empty ⊢ₚₛ (ptyp_to_pskl τ') }}a ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     Δ ∩ ftvar_in_ptyp τ [=] empty) ->
  Δ ∩ ftvar_in_ptyp τ' [=] empty ->
  {{ Θ ⨟ Δ ⊢ᵣₚ ⌊ R' ⌋ˢ ⊳ (ptyp_to_pskl τ') }}ad.
Proof.
  intros Θb Ψr R' R Hp; induction Hp;
    intros Θ' Δ τ' Heq Hm Hmon Hwf Hwfτ Hdefs Hfree.
  - (* refl *)
    rewrite Heq. rewrite uskl_to_pskl_ptyp.
    eapply ad_refine_pskl_refl_gen. exact Hwfτ.
  - (* arrow *)
    destruct τ' as [ | n | β | τ1 τ2 | τ0 ];
      unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in Heq;
      simpl in Heq; try discriminate Heq.
    inversion Heq; subst.
    inversion Hm; subst.
    simpl in Hfree.
    assert (Hw1 : {{ Θ' ⨟ empty ⊢ₚₛ (ptyp_to_pskl τ1) }}a)
      by (inversion Hwfτ; subst; assumption).
    assert (Hw2 : {{ Θ' ⨟ empty ⊢ₚₛ (ptyp_to_pskl τ2) }}a)
      by (inversion Hwfτ; subst; assumption).
    simpl. apply ad_refine_pskl__arrow.
    + eapply IHHp1;
        [ unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn; reflexivity
        | assumption | exact Hmon | exact Hwf | exact Hw1 | exact Hdefs
        | clear - Hfree; fsetdec ].
    + eapply IHHp2;
        [ unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn; reflexivity
        | assumption | exact Hmon | exact Hwf | exact Hw2 | exact Hdefs
        | clear - Hfree; fsetdec ].
  - (* all_syn cong : a monotype painting is never ∀-headed *)
    destruct τ' as [ | n | β | τ1 τ2 | τ0 ];
      unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in Heq;
      simpl in Heq; try discriminate Heq.
    inversion Hm.
  - (* all_tag cong *)
    destruct τ' as [ | n | β | τ1 τ2 | τ0 ];
      unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in Heq;
      simpl in Heq; discriminate Heq.
  - (* all_inst *)
    destruct τ' as [ | n | β | τ1 τ2 | τ0 ];
      unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in Heq;
      simpl in Heq; discriminate Heq.
  - (* univ_ghost cong *)
    destruct τ' as [ | n | β | τ1 τ2 | τ0 ];
      unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in Heq;
      simpl in Heq; discriminate Heq.
  - (* dot_univ_ghost cong *)
    destruct τ' as [ | n | β | τ1 τ2 | τ0 ];
      unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in Heq;
      simpl in Heq; discriminate Heq.
  - (* univ_ghost_keepg *)
    destruct τ' as [ | n | β | τ1 τ2 | τ0 ];
      unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in Heq;
      simpl in Heq; discriminate Heq.
  - (* ghost *)
    simpl. apply ad_refine_pskl__ghost.
    rewrite ftvar_ptyp_to_pskl. exact Hfree.
  - (* univ_ghost_remove *)
    simpl. apply ad_refine_pskl__univ_ghost_remove.
    eapply IHHp;
      [ exact Heq | exact Hm | exact Hmon | exact Hwf | exact Hwfτ
      | exact Hdefs | exact Hfree ].
  - (* flex_l : unfold the ghostier side's definition *)
    simpl. eapply ad_refine_pskl__flex_l; [ apply Hmon; eassumption | ].
    pose proof (IHHp Θ' Δ τ' Heq Hm Hmon Hwf Hwfτ Hdefs Hfree) as Ht.
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
          eapply a_wf_aenv_binds_def_wf; [ exact Hwf | apply Hmon; exact Hb ]
        | exact Hdefs
        | eapply Hdefs; apply Hmon; exact Hb ]
    end.
Qed.

(* The three ⊑ᵤ rows every inner induction of the main lemma shares.
   [refl] is inline (rewrite the erasure equation, hand back the
   reconstituted node); the others are: *)

(* [upre__ghost]: the ghost helper, fed the node + the Δ-freeness of the
   row's own source (wf at [Θb ⨟ ∅], and Δ is fresh for [Θb]). *)
Local Ltac erase_refine_ghost Hrr Hdefs Hflex HΔb Θb Heq :=
  simpl;
  eapply ad_refine_pskl_ghost_l;
    [ exact Hrr | exact Hdefs | exact Hflex
    | rewrite <- Heq;
      eapply a_wf_pskl_empty_delta_free with (Θ := Θb);
        [ eassumption | exact HΔb ] ].

(* [upre__univ_ghost_remove]: peel the ghostier side's ∀◇ and recurse. *)
Local Ltac erase_refine_remove IHHp Heq :=
  simpl; apply ad_refine_pskl__univ_ghost_remove; apply IHHp; exact Heq.

(* [upre__flex_l]: unfold the ghostier side's flex definition and recurse
   (the precise side, hence the erasure equation, is unchanged). *)
Local Ltac erase_refine_flexl Hmon IHHp Heq :=
  simpl; eapply ad_refine_pskl__flex_l;
    [ apply Hmon; eassumption
    | let Ht := fresh "Ht" in
      pose proof (IHHp Heq) as Ht;
      rewrite uskl_to_pskl_ptyp in Ht; exact Ht ].

(* [all]-row recursion: the binder enters Θ AND Δ. *)
Local Ltac erase_refine_all H0 Hfam LL L Θ Θb Δ Hwf Hdefs Hflex Hmon HΔb :=
  apply ad_refine_pskl__all
    with (L := L `union` LL `union` dom Θ `union` dom Θb `union` Δ);
  let α2 := fresh "α2" in
  let Hα2 := fresh "Hα2" in
  let HαΘ := fresh "HαΘ" in
  let Hdefs' := fresh "Hdefs'" in
  let Hflex' := fresh "Hflex'" in
  intros α2 Hα2;
  rewrite <- uskl_to_pskl_open;
  assert (HαΘ : α2 `notin` dom Θ) by (clear - Hα2; fsetdec);
  destruct (delta_flex_defs_cons_tvar_add Hwf HαΘ Hdefs Hflex)
    as [Hdefs' Hflex'];
  eapply H0;
    [ clear - Hα2; fsetdec
    | apply a_wf_aenv__tvar; [ exact HαΘ | exact Hwf ]
    | exact Hdefs' | exact Hflex'
    | apply Hfam; clear - Hα2; fsetdec
    | intros x b0 Hb0; apply binds_cons_3; apply Hmon; exact Hb0
    | let β := fresh "β" in
      let Hβ := fresh "Hβ" in
      let Hne := fresh "Hne" in
      intros β Hβ;
      destruct (β == α2) as [-> | Hne];
        [ clear - Hα2; fsetdec
        | apply HΔb; clear - Hβ Hne; fsetdec ]
    | apply uskl_to_pskl_open ].

(* [univ_ghost_fill]-row recursion: the binder enters Θ only. *)
Local Ltac erase_refine_fill H0 L Θ Θb Δ Hwf Hdefs Hflex Hmon HΔb ctor :=
  apply ad_refine_pskl__univ_ghost_fill
    with (L := L `union` dom Θ `union` dom Θb `union` Δ);
  let α2 := fresh "α2" in
  let Hα2 := fresh "Hα2" in
  let Hdefs' := fresh "Hdefs'" in
  let Hflex' := fresh "Hflex'" in
  intros α2 Hα2;
  match goal with
  |- {{ _ ⨟ _ ⊢ᵣₚ (pskl_univ_ghost (uskl_to_pskl ?RR)) ⊳ _ }}ad =>
    change (pskl_univ_ghost (uskl_to_pskl RR))
      with (uskl_to_pskl (ctor RR))
  end;
  destruct (@delta_flex_defs_cons_tvar α2 Θ Δ Hdefs Hflex)
    as [Hdefs' Hflex'];
  eapply H0;
    [ clear - Hα2; fsetdec
    | apply a_wf_aenv__tvar; [ clear - Hα2; fsetdec | exact Hwf ]
    | exact Hdefs' | exact Hflex'
    | first [ apply upre__univ_ghost; eassumption
            | apply upre__dot_univ_ghost; eassumption
            | apply upre__univ_ghost_keepg; eassumption ]
    | intros x b0 Hb0; apply binds_cons_3; apply Hmon; exact Hb0
    | exact HΔb
    | reflexivity ].

(** THE STEP-(3) ENABLER, general form: Δ need not be fresh for [Θ] (the
    [all] rule puts its variable into both); it suffices that no flexible
    variable or definition of [Θ] meets Δ ([Hdefs]/[Hflex]) and that Δ is
    fresh for the FIXED ⊑ᵤ context [Θb]. *)
Lemma uskl_precise_erase_refine_gen : forall Θ Δ Qm Qr,
  {{ Θ ⨟ Δ ⊢ᵣₚ Qm ⊳ Qr }}ad ->
  {{ ⊢ Θ }}a ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     Δ ∩ ftvar_in_ptyp τ [=] empty) ->
  (forall β τ, β `in` Δ -> ~ binds β (abind_flex_mono_def τ) Θ) ->
  forall Θb Ψr R' R,
  uskl_precise Θb Ψr R' R ->
  (forall x (b : abind), binds x b Θb -> binds x b Θ) ->
  (forall α, α `in` Δ -> α `notin` dom Θb) ->
  ⌊ R ⌋ˢ = Qm ->
  {{ Θ ⨟ Δ ⊢ᵣₚ ⌊ R' ⌋ˢ ⊳ Qr }}ad.
Proof.
  intros Θ Δ Qm Qr Hr; induction Hr;
    intros Hwf Hdefs Hflex Θb Ψr R' R Hp Hmon HΔb Heq.
  - (* unit *)
    assert (Hrr : {{ Θ ⨟ Δ ⊢ᵣₚ pskl_unit ⊳ pskl_unit }}ad)
      by (apply ad_refine_pskl__unit).
    revert Heq; induction Hp; intros Heq; simpl in Heq; try discriminate Heq.
    + rewrite Heq. exact Hrr.
    + erase_refine_ghost Hrr Hdefs Hflex HΔb Θb Heq.
    + erase_refine_remove IHHp Heq.
    + erase_refine_flexl Hmon IHHp Heq.
  - (* var *)
    assert (Hrr : {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_var_f α) ⊳ (pskl_var_f α) }}ad)
      by (apply ad_refine_pskl__var).
    revert Heq; induction Hp; intros Heq; simpl in Heq; try discriminate Heq.
    + rewrite Heq. exact Hrr.
    + erase_refine_ghost Hrr Hdefs Hflex HΔb Θb Heq.
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
            eapply a_wf_aenv_binds_def_wf; [ exact Hwf | apply Hmon; exact Hb ]
          | exact Hdefs
          | eapply Hdefs; apply Hmon; exact Hb ]
      end.
  - (* arrow *)
    assert (Hrr : {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_arrow P1 P2) ⊳ (pskl_arrow P3 P4) }}ad)
      by (apply ad_refine_pskl__arrow; assumption).
    revert Heq; induction Hp; intros Heq; simpl in Heq; try discriminate Heq.
    + rewrite Heq. exact Hrr.
    + (* upre__arrow *)
      inversion Heq; subst.
      simpl. apply ad_refine_pskl__arrow.
      * eapply IHHr1;
          [ exact Hwf | exact Hdefs | exact Hflex
          | eassumption | exact Hmon | exact HΔb | reflexivity ].
      * eapply IHHr2;
          [ exact Hwf | exact Hdefs | exact Hflex
          | eassumption | exact Hmon | exact HΔb | reflexivity ].
    + erase_refine_ghost Hrr Hdefs Hflex HΔb Θb Heq.
    + erase_refine_remove IHHp Heq.
    + erase_refine_flexl Hmon IHHp Heq.
  - (* all *)
    assert (Hrr : {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_all_syn P) ⊳ (pskl_all_syn P') }}ad)
      by (apply ad_refine_pskl__all with (L := L); exact H).
    revert Heq; induction Hp; intros Heq; simpl in Heq; try discriminate Heq.
    + rewrite Heq. exact Hrr.
    + (* upre__all_syn *)
      inversion Heq; subst.
      simpl.
      match goal with
        Hfam : forall β, β `notin` ?LL -> uskl_precise _ _ _ _ |- _ =>
        erase_refine_all H0 Hfam LL L Θ Θb Δ Hwf Hdefs Hflex Hmon HΔb
      end.
    + (* upre__all_tag *)
      inversion Heq; subst.
      simpl.
      match goal with
        Hfam : forall β, β `notin` ?LL -> uskl_precise _ _ _ _ |- _ =>
        erase_refine_all H0 Hfam LL L Θ Θb Δ Hwf Hdefs Hflex Hmon HΔb
      end.
    + (* upre__all_inst *)
      inversion Heq; subst.
      simpl.
      match goal with
        Hfam : forall β, β `notin` ?LL -> uskl_precise _ _ _ _ |- _ =>
        erase_refine_all H0 Hfam LL L Θ Θb Δ Hwf Hdefs Hflex Hmon HΔb
      end.
    + erase_refine_ghost Hrr Hdefs Hflex HΔb Θb Heq.
    + erase_refine_remove IHHp Heq.
    + erase_refine_flexl Hmon IHHp Heq.
  - (* ghost *)
    assert (Hrr : {{ Θ ⨟ Δ ⊢ᵣₚ pskl_ghost ⊳ P' }}ad)
      by (apply ad_refine_pskl__ghost; exact H).
    revert Heq; induction Hp; intros Heq; simpl in Heq; try discriminate Heq.
    + rewrite Heq. exact Hrr.
    + simpl. exact Hrr.
    + erase_refine_remove IHHp Heq.
    + erase_refine_flexl Hmon IHHp Heq.
  - (* univ_ghost_remove *)
    assert (Hrr : {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_univ_ghost P) ⊳ P' }}ad)
      by (apply ad_refine_pskl__univ_ghost_remove; exact Hr).
    revert Heq; induction Hp; intros Heq; simpl in Heq; try discriminate Heq.
    + rewrite Heq. exact Hrr.
    + (* upre__univ_ghost *)
      inversion Heq; subst.
      simpl. apply ad_refine_pskl__univ_ghost_remove.
      eapply IHHr;
        [ exact Hwf | exact Hdefs | exact Hflex
        | eassumption | exact Hmon | exact HΔb | reflexivity ].
    + (* upre__dot_univ_ghost *)
      inversion Heq; subst.
      simpl. apply ad_refine_pskl__univ_ghost_remove.
      eapply IHHr;
        [ exact Hwf | exact Hdefs | exact Hflex
        | eassumption | exact Hmon | exact HΔb | reflexivity ].
    + (* upre__univ_ghost_keepg *)
      inversion Heq; subst.
      simpl. apply ad_refine_pskl__univ_ghost_remove.
      eapply IHHr;
        [ exact Hwf | exact Hdefs | exact Hflex
        | eassumption | exact Hmon | exact HΔb | reflexivity ].
    + erase_refine_ghost Hrr Hdefs Hflex HΔb Θb Heq.
    + erase_refine_remove IHHp Heq.
    + erase_refine_flexl Hmon IHHp Heq.
  - (* univ_ghost_fill *)
    assert (Hrr : {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_univ_ghost P) ⊳ (pskl_all_syn P') }}ad)
      by (apply ad_refine_pskl__univ_ghost_fill with (L := L); exact H).
    revert Heq; induction Hp; intros Heq; simpl in Heq; try discriminate Heq.
    + rewrite Heq. exact Hrr.
    + (* upre__univ_ghost *)
      inversion Heq; subst.
      simpl.
      erase_refine_fill H0 L Θ Θb Δ Hwf Hdefs Hflex Hmon HΔb uskl_univ_ghost.
    + (* upre__dot_univ_ghost *)
      inversion Heq; subst.
      simpl.
      erase_refine_fill H0 L Θ Θb Δ Hwf Hdefs Hflex Hmon HΔb uskl_dot_univ_ghost.
    + (* upre__univ_ghost_keepg *)
      inversion Heq; subst.
      simpl.
      erase_refine_fill H0 L Θ Θb Δ Hwf Hdefs Hflex Hmon HΔb uskl_univ_ghost.
    + erase_refine_ghost Hrr Hdefs Hflex HΔb Θb Heq.
    + erase_refine_remove IHHp Heq.
    + erase_refine_flexl Hmon IHHp Heq.
  - (* univ_ghost_keep *)
    assert (Hrr : {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_univ_ghost P) ⊳ (pskl_univ_ghost P') }}ad)
      by (apply ad_refine_pskl__univ_ghost_keep; assumption).
    revert Heq; induction Hp; intros Heq; simpl in Heq; try discriminate Heq.
    + rewrite Heq. exact Hrr.
    + (* upre__univ_ghost *)
      inversion Heq; subst.
      simpl. apply ad_refine_pskl__univ_ghost_keep.
      eapply IHHr;
        [ exact Hwf | exact Hdefs | exact Hflex
        | eassumption | exact Hmon | exact HΔb | reflexivity ].
    + (* upre__dot_univ_ghost *)
      inversion Heq; subst.
      simpl. apply ad_refine_pskl__univ_ghost_keep.
      eapply IHHr;
        [ exact Hwf | exact Hdefs | exact Hflex
        | eassumption | exact Hmon | exact HΔb | reflexivity ].
    + (* upre__univ_ghost_keepg *)
      inversion Heq; subst.
      simpl. apply ad_refine_pskl__univ_ghost_keep.
      eapply IHHr;
        [ exact Hwf | exact Hdefs | exact Hflex
        | eassumption | exact Hmon | exact HΔb | reflexivity ].
    + erase_refine_ghost Hrr Hdefs Hflex HΔb Θb Heq.
    + erase_refine_remove IHHp Heq.
    + erase_refine_flexl Hmon IHHp Heq.
  - (* flex_l *)
    assert (Hrr : {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_var_f α) ⊳ P' }}ad)
      by (eapply ad_refine_pskl__flex_l; eassumption).
    revert Heq; induction Hp; intros Heq; simpl in Heq; try discriminate Heq.
    + rewrite Heq. exact Hrr.
    + erase_refine_ghost Hrr Hdefs Hflex HΔb Θb Heq.
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
        [ exact Hwf | exact Hdefs | exact Hflex
        | eassumption | exact Hmon | exact HΔb | apply uskl_to_pskl_ptyp ].
  - (* flex_r *)
    eapply ad_refine_pskl__flex_r; [ eassumption | ].
    eapply IHHr;
      [ exact Hwf | exact Hdefs | exact Hflex
      | exact Hp | exact Hmon | exact HΔb | exact Heq ].
Qed.

(** THE STEP-(3) ENABLER (Sub-ForallL item 1): the erasure of a
    ⊑ᵤ-ghostier subject refines to anything the original subject's
    erasure refines to.  Δ holds refinement-local ∀-variables, fresh for
    Θ.  No well-formedness of the target is needed: the ghost rule asks
    only Δ-freeness. *)
Lemma uskl_precise_erase_refine : forall Θ Δ Qm Qr,
  {{ Θ ⨟ Δ ⊢ᵣₚ Qm ⊳ Qr }}ad ->
  {{ ⊢ Θ }}a ->
  (forall α, α `in` Δ -> α `notin` dom Θ) ->
  forall Θb Ψr R' R,
  uskl_precise Θb Ψr R' R ->
  (forall x (b : abind), binds x b Θb -> binds x b Θ) ->
  ⌊ R ⌋ˢ = Qm ->
  {{ Θ ⨟ Δ ⊢ᵣₚ ⌊ R' ⌋ˢ ⊳ Qr }}ad.
Proof.
  intros Θ Δ Qm Qr Hr Hwf Hdisj Θb Ψr R' R Hp Hmon Heq.
  destruct (delta_fresh_flex_defs Hwf Hdisj) as [Hdefs Hflex].
  eapply uskl_precise_erase_refine_gen;
    [ exact Hr | exact Hwf | exact Hdefs | exact Hflex
    | exact Hp | exact Hmon | | exact Heq ].
  intros α Hα Hin. apply (Hdisj α Hα).
  apply binds_In_inv in Hin as [b Hb].
  eapply binds_In. apply Hmon. exact Hb.
Qed.
