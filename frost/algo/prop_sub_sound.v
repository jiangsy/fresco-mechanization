(** SOUNDNESS OF DECORATED SUBTYPING (lemma:sound-decorated-subtyping,
    subtyping-proofs.tex:43-58, mutual with
    lemma:sound-decorated-flex-subtyping :1094) — the L-B half of
    thm:sound-subtyping (docs/DESIGN-subtyping.md §2.1).

    A decorated run is an identity information increase whose output (read
    back as a [bskl] Qt) is a declarative subtype of the subject over the
    OUTPUT context, and a valid fill of the input [P0].  Every consistency
    premise is discharged by [a_consistag_sound_aux] (Qed); the flexible
    walk recurses on the decorated walk [a_subtag_flex].

    COMPLETE — every case Qed; the bundle is axiom-free (see the
    Print Assumptions check at the end of the file). *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_ln.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decl_algo_sub.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_decorate.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_compose.
Require Import src.frost.algo.prop_metasubst.
Require Import src.frost.algo.prop_mono_bridge.
Require Import src.frost.algo.prop_consis_sound.
Require Import src.frost.algo.prop_consis_complete.
Require Import src.frost.algo.prop_precise.
Require Import src.frost.algo.prop_pat_sub.
Require Import src.frost.algo.prop_looksub.

Set Implicit Arguments.

Scheme a_subtag_mutind := Induction for a_subtag Sort Prop
  with a_subtag_flex_mutind := Induction for a_subtag_flex Sort Prop.

Combined Scheme a_subtag_subtag_flex_mutind
  from a_subtag_mutind, a_subtag_flex_mutind.

(* ===================================================================== *)
(*  §1  Small erasure/painting transports                                 *)
(* ===================================================================== *)

(** The syn painting of an lc skeleton is synthesised. *)
Lemma is_sskl_pskl_to_bskl_syn : forall P,
  lc_pskl P ->
  is_sskl (pskl_to_bskl_syn P).
Proof.
  intros P Hlc; induction Hlc; simpl; try (constructor; auto; fail).
  apply is_sskl__all with (L := {}).
  intros α _. rewrite <- pskl_to_bskl_syn_open. auto.
Qed.

(** Erasure preserves local closure. *)
Lemma lc_uskl_to_pskl : forall R,
  lc_uskl R ->
  lc_pskl ⌊ R ⌋ˢ.
Proof.
  intros R H; induction H; simpl;
    try (constructor; auto; fail);
    constructor; intros α; rewrite <- uskl_to_pskl_open; auto.
Qed.

(** Erasure preserves guardedness (guarded shapes have no decorations). *)
Lemma guarded_uskl_to_pskl : forall R,
  guarded_uskl R ->
  guarded_pskl ⌊ R ⌋ˢ.
Proof.
  intros R H; inversion H; simpl; constructor;
    auto using lc_uskl_to_pskl.
Qed.

(** The syn painting preserves guardedness. *)
Lemma guarded_pskl_to_bskl_syn : forall P,
  guarded_pskl P ->
  guarded_bskl (pskl_to_bskl_syn P).
Proof.
  intros P H; inversion H; simpl; constructor;
    auto using lc_pskl_to_bskl_syn.
Qed.

(** A declaration-only prefix preserves context well-formedness (decls
    carry no payload; freshness comes from the uniq hypothesis). *)
Lemma a_wf_aenv_prepend_decls : forall Ξ Θ,
  a_decls Ξ ->
  uniq Ξ ->
  (forall α1, α1 `in` dom Ξ -> α1 `notin` dom Θ) ->
  a_wf_aenv Θ ->
  a_wf_aenv (Ξ ++ Θ).
Proof.
  induction Ξ as [ | [α1 b] Ξ' IH ]; intros Θ Hdecl Huq Hfr Hwf;
    [ exact Hwf | ].
  inversion Hdecl; subst.
  simpl_env. apply a_wf_aenv__flex.
  - simpl_env. 
    assert (Hα1Θ : α1 `notin` dom Θ)
      by (apply Hfr; simpl; fsetdec).
    clear - Huq Hα1Θ. simpl_env in *. solve_uniq.
  - apply IH; auto.
    + clear - Huq. solve_uniq.
    + intros α10 Hγ0. apply Hfr. simpl. fsetdec.
Qed.

(** Decorated skeletons are locally closed ([is_tskl] is cofinite at its
    binder). *)
Lemma is_tskl_lc : forall ψ,
  is_tskl ψ ->
  lc_uskl ψ.
Proof.
  intros ψ H; induction H; try (constructor; auto; fail).
  destruct (atom_fresh L) as [α Hα].
  eapply lc_uskl_all_etag_exists; eauto.
Qed.

(** Substituting a well-formed skeleton for a Δ-variable preserves
    (disciplined) well-formedness.  The ∀◇ case is where the freshness
    hypothesis earns its keep: a ∀◇-body is well-formed at the EMPTY Δ,
    so it cannot mention α and the substitution is the identity there. *)
Lemma a_wf_pskl_subst_tvar : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  forall α P' Δ0,
  Δ0 [=] remove α Δ ->
  α `notin` dom Θ ->
  Θ ⨟ Δ0 ⊢ₚₛᵃ P' ->
  Θ ⨟ Δ0 ⊢ₚₛᵃ subst_pskl_in_pskl P' α P.
Proof.
  intros Θ Δ P H; induction H;
    intros α0 Q0 Δ0 Heq Hfr HwfQ; simpl.
  - apply a_wf_pskl__unit.
  - destruct_if as [-> | Hne].
    + exact HwfQ.
    + apply a_wf_pskl__var.
      destruct H as [HΔ | Ht];
        [ left; clear - HΔ Hne Heq; fsetdec | right; exact Ht ].
  - apply a_wf_pskl__arrow; eauto.
  - apply a_wf_pskl__all
      with (L := L `union` {{α0}} `union` dom Θ `union` Δ0).
    intros β Hβ.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | let He := fresh in intro He; subst; clear - Hβ; fsetdec
        | eapply a_wf_pskl_lc; eauto ].
    match goal with
    | IH : forall α, α `notin` L -> _ |- _ => eapply IH
    end;
      [ clear - Hβ; fsetdec
      | clear - Hβ Heq; fsetdec
      | exact Hfr
      | eapply a_wf_pskl_delta_mono; [ exact HwfQ | clear; fsetdec ] ].
  - apply a_wf_pskl__hole.
  - assert (Hα : α0 `notin` ftvar_in_pskl P).
    { intro HXin.
      destruct (a_wf_pskl_ftv_tvarish H0 HXin) as [HΔ | Ht];
        [ clear - HΔ; fsetdec | ].
      apply Hfr.
      destruct Ht as [Hb | [Hb | [τ Hb]]]; eapply binds_In; eauto. }
    rewrite subst_pskl_in_pskl_fresh_eq; [ | exact Hα ].
    apply a_wf_pskl__tophole; auto.
Qed.

(** Opening a ∀-body with a well-formed skeleton: the binder's Δ-slot is
    traded for the substituend's own well-formedness. *)
Lemma a_wf_pskl_open : forall L Θ Δ P P',
  (forall α, α `notin` L ->
     Θ ⨟ (add α Δ) ⊢ₚₛᵃ open_pskl_wrt_pskl P (pskl_var_f α)) ->
  Θ ⨟ Δ ⊢ₚₛᵃ P' ->
  Θ ⨟ Δ ⊢ₚₛᵃ open_pskl_wrt_pskl P P'.
Proof.
  intros L Θ Δ P P' Hbody HwfQ.
  destruct (atom_fresh (L `union` dom Θ `union` Δ
                          `union` ftvar_in_pskl P)) as [α Hα].
  rewrite (subst_pskl_in_pskl_intro α); [ | clear - Hα; fsetdec ].
  eapply a_wf_pskl_subst_tvar with (Δ := add α Δ);
    [ apply Hbody; clear - Hα; fsetdec
    | clear - Hα; fsetdec
    | clear - Hα; fsetdec
    | exact HwfQ ].
Qed.

(** audit-F2 bridge helpers.  A consistency judgement whose output is an
    inh-painting-shaped skeleton transports its subject down to the exact
    inh-painting, peeling the subject's leading [∀◇]/flex nodes.  These handle
    the ARROW and ∀ structural cases of [ad_pat_consis_refine_inh_gen]. *)

Lemma consis_transport_arrow : forall Ψ Θ' R Q1 Q2 P1 P2,
  Ψ ⨟ Θ' ⊢ₛᵃ R ∼ (bskl_arrow Q1 Q2) ->
  Θ' ⨟ empty ⊢ₚₛᵃ (pskl_arrow P1 P2) ->
  (forall Ψ' R', Ψ' ⨟ Θ' ⊢ₛᵃ R' ∼ Q1 ->
     Ψ' ⨟ Θ' ⊢ₛᵃ R' ∼ (pskl_to_bskl_inh P1)) ->
  (forall Ψ' R', Ψ' ⨟ Θ' ⊢ₛᵃ R' ∼ Q2 ->
     Ψ' ⨟ Θ' ⊢ₛᵃ R' ∼ (pskl_to_bskl_inh P2)) ->
  Ψ ⨟ Θ' ⊢ₛᵃ R ∼ (pskl_to_bskl_inh (pskl_arrow P1 P2)).
Proof.
  intros Ψ Θ' R Q1 Q2 P1 P2 Hc HwfB HR1 HR2.
  remember (bskl_arrow Q1 Q2) as Qout eqn:HQ.
  induction Hc; try discriminate HQ.
  - (* arrow *) inversion HQ; subst. simpl.
    apply ad_pat_consis__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
      [ apply HR1; assumption | apply HR2; assumption | assumption ].
  - (* hole : uskl_hole ∼ any inh painting via the wf target *)
    apply ad_pat_consis__hole; [ assumption | exact HwfB ].
  - (* tophole_drop *) apply ad_pat_consis__tophole_drop. apply IHHc; assumption.
  - (* flex_l *) eapply ad_pat_consis__flex_l; [ eassumption | ].
    apply IHHc; assumption.
Qed.

Lemma consis_transport_all : forall Ψ Θ' R Q0 P0 L,
  Ψ ⨟ Θ' ⊢ₛᵃ R ∼ (bskl_all_inh Q0) ->
  Θ' ⨟ empty ⊢ₚₛᵃ (pskl_all_syn P0) ->
  (forall α, α `notin` L ->
     forall Ψ' R',
       Ψ' ⨟ ((α ~ abind_tvar) ++ Θ') ⊢ₛᵃ
         R' ∼ (open_bskl_wrt_bskl Q0 (bskl_var_f α)) ->
       Ψ' ⨟ ((α ~ abind_tvar) ++ Θ') ⊢ₛᵃ
         R' ∼ (pskl_to_bskl_inh (open_pskl_wrt_pskl P0 (pskl_var_f α)))) ->
  Ψ ⨟ Θ' ⊢ₛᵃ R ∼ (pskl_to_bskl_inh (pskl_all_syn P0)).
Proof.
  intros Ψ Θ' R Q0 P0 L Hc HwfB Htr.
  remember (bskl_all_inh Q0) as Qout eqn:HQ.
  induction Hc; try discriminate HQ.
  - (* forall_inh_tagged : R = uskl_all_etag ε R *)
    inversion HQ; subst.
    eapply ad_pat_consis__forall_inh_tagged with (Ψ0 := Ψ0)
      (L := L `union` L0); [ | assumption ].
    intros α Hα.
    rewrite <- pskl_to_bskl_inh_open.
    apply Htr; [ clear - Hα; fsetdec | ].
    match goal with
    | Hbody : forall α, α `notin` ?L1 -> _ |- _ =>
        apply (Hbody α ltac:(clear - Hα; fsetdec))
    end.
  - (* forall_inh_untagged : R = uskl_all_syn R *)
    inversion HQ; subst.
    apply ad_pat_consis__forall_inh_untagged with (L := L `union` L0).
    intros α Hα.
    rewrite <- pskl_to_bskl_inh_open.
    apply Htr; [ clear - Hα; fsetdec | ].
    match goal with
    | Hbody : forall α, α `notin` ?L1 -> _ |- _ =>
        apply (Hbody α ltac:(clear - Hα; fsetdec))
    end.
  - (* hole *) apply ad_pat_consis__hole; [ assumption | exact HwfB ].
  - (* tophole_inh : R = uskl_tophole R *)
    inversion HQ; subst.
    apply ad_pat_consis__tophole_inh with (L := L `union` L0).
    intros α Hα.
    rewrite <- pskl_to_bskl_inh_open.
    apply Htr; [ clear - Hα; fsetdec | ].
    match goal with
    | Hbody : forall α, α `notin` ?L1 -> _ |- _ =>
        apply (Hbody α ltac:(clear - Hα; fsetdec))
    end.
  - (* tophole_drop *) apply ad_pat_consis__tophole_drop. apply IHHc; assumption.
  - (* flex_l *) eapply ad_pat_consis__flex_l; [ eassumption | ].
    apply IHHc; assumption.
Qed.

(** audit-F2 bridge: the declarative consistency output transports from any
    fill [Qt] of a well-formed ghost-free painting [inh B] back to [inh B]
    itself.  Machine-checked form of the paper's "when either input is a type
    annotation A, the output Q is a type EQUIVALENT to A"
    (full-algo-spec.tex:1444): a flexible subject yields output [α̂ ≔ B ≡ B] and
    the fill conjunct lets us fold it back to [B].  Induction on the
    consistency derivation, threading the fill; ghost-free + wf on [B] exclude
    the fill's ghost/flex-def source rules. *)
Lemma ad_pat_consis_refine_inh_gen : forall Θ Δ Qsrc Qt,
  ad_refine_syn_f empty Θ Δ Qsrc Qt ->
  forall Psrc, Qsrc = pskl_to_bskl_inh Psrc ->
  pskl_ghost_free Psrc ->
  forall Θ',
  (forall x b, binds x b Θ -> binds x b Θ') ->
  (forall α, α `in` Δ -> a_binds_tvar α Θ') ->
  a_wf_aenv Θ' ->
  Θ' ⨟ empty ⊢ₚₛᵃ Psrc ->
  forall Ψ R, Ψ ⨟ Θ' ⊢ₛᵃ R ∼ Qt -> Ψ ⨟ Θ' ⊢ₛᵃ R ∼ (pskl_to_bskl_inh Psrc).
Proof.
  intros Θ Δ Qsrc Qt Hfill.
  induction Hfill; intros Bsrc HeqSrc Hgf Θ' Hmon Hrig Hwf' HwfB Ψ T Hc.
  - (* unit *)
    destruct Bsrc; simpl in HeqSrc; try discriminate HeqSrc. exact Hc.
  - (* var *)
    destruct Bsrc; simpl in HeqSrc; try discriminate HeqSrc.
    inversion HeqSrc; subst. exact Hc.
  - (* arrow *)
    destruct Bsrc; simpl in HeqSrc, Hgf; try discriminate HeqSrc.
    inversion HeqSrc; subst. destruct Hgf as [Hgf1 Hgf2].
    pose proof HwfB as HwfBc. simpl in HwfBc.
    inversion HwfBc as [ | | Θz Δz P1z P2z HwfB1 HwfB2 | | | ]; subst.
    eapply consis_transport_arrow with (P1 := Bsrc1) (P2 := Bsrc2);
      [ exact Hc | exact HwfB
      | intros Ψ' T' HT'; eapply IHHfill1;
          [ reflexivity | exact Hgf1 | exact Hmon | exact Hrig
          | exact Hwf' | exact HwfB1 | exact HT' ]
      | intros Ψ' T' HT'; eapply IHHfill2;
          [ reflexivity | exact Hgf2 | exact Hmon | exact Hrig
          | exact Hwf' | exact HwfB2 | exact HT' ] ].
  - (* all *)
    destruct Bsrc; simpl in HeqSrc, Hgf; try discriminate HeqSrc.
    inversion HeqSrc; subst.
    pose proof HwfB as HwfBc. simpl in HwfBc.
    inversion HwfBc as [ | | | Lwf Θz Δz Bz Hbody Heqz | | ]; subst.
    eapply consis_transport_all with (P0 := Bsrc)
      (L := L `union` Lwf `union` dom Θ' `union` ftvar_in_pskl Bsrc);
      [ exact Hc | exact HwfB | ].
    intros α Hα Ψ0 T0 HT0.
    match goal with
    | IH : forall α0, α0 `notin` ?L0 ->
             forall Bsrc0, _ = pskl_to_bskl_inh Bsrc0 -> _ |- _ =>
        eapply (IH α ltac:(clear - Hα; fsetdec)
                  (open_pskl_wrt_pskl Bsrc (pskl_var_f α)))
    end;
      [ symmetry; apply pskl_to_bskl_inh_open
      | unfold open_pskl_wrt_pskl; apply pskl_ghost_free_open_rec; exact Hgf
      | intros x b Hb; unfold binds; simpl; right; apply Hmon; exact Hb
      | intros β Hβ; destruct (β == α) as [-> | Hne];
          [ left; unfold binds; simpl; left; reflexivity
          | apply a_binds_tvar_weaken_cons; apply Hrig;
            clear - Hβ Hne; fsetdec ]
      | apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf' ]
      | eapply a_wf_pskl_delta_to_tvar;
          [ apply Hbody; clear - Hα; fsetdec | clear; fsetdec ]
      | exact HT0 ].
  - (* hole : source ghost, excluded *)
    destruct Bsrc; simpl in HeqSrc, Hgf; try discriminate HeqSrc; contradiction.
  - (* tophole_remove *)
    destruct Bsrc; simpl in HeqSrc, Hgf; try discriminate HeqSrc; contradiction.
  - (* tophole_fill *)
    destruct Bsrc; simpl in HeqSrc, Hgf; try discriminate HeqSrc; contradiction.
  - (* tophole_keep *)
    destruct Bsrc; simpl in HeqSrc, Hgf; try discriminate HeqSrc; contradiction.
  - (* flex_l : source is a defined flex var *)
    assert (Hbα' : binds α (abind_flex_mono_def τ) Θ') by (apply Hmon; exact H).
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    assert (Hwfτ : a_wf_ptyp Θ' τ) by (eapply a_wf_aenv_binds_def_wf; eauto).
    rewrite <- HeqSrc.
    eapply ad_pat_consis__flex_r; [ exact Hbα' | ].
    rewrite <- (mono_inh_eq_syn Hmτ).
    eapply (IHHfill (ptyp_to_pskl τ));
      [ symmetry; apply (mono_inh_eq_syn Hmτ)
      | apply ptyp_to_pskl_ghost_free
      | exact Hmon | exact Hrig | exact Hwf'
      | apply a_wf_pskl_mono_ptyp; [ exact Hmτ | exact Hwfτ ]
      | exact Hc ].
  - (* flex_r : output is a defined flex var; unfold the consistency *)
    assert (Hbα' : binds α (abind_flex_mono_def τ) Θ') by (apply Hmon; exact H).
    assert (Hunf : Ψ ⨟ Θ' ⊢ₛᵃ T ∼ (ptyp_to_bskl_syn τ))
      by (eapply consis_unfold_def_join;
            [ exact Hc | exact Hwf' | reflexivity | exact Hbα' ]).
    eapply IHHfill with (Psrc := Bsrc) (Θ' := Θ');
      [ exact HeqSrc | exact Hgf | exact Hmon | exact Hrig
      | exact Hwf' | exact HwfB | exact Hunf ].
Qed.

Lemma ad_pat_consis_refine_inh_target : forall Ψ Θ R Qt,
  Ψ ⨟ Θ ⊢ₛᵃ R ∼ Qt ->
  a_wf_aenv Θ ->
  forall P,
  Θ ⨟ empty ⊢ₚₛᵃ P ->
  pskl_ghost_free P ->
  ad_refine_syn_f empty Θ empty (pskl_to_bskl_inh P) Qt ->
  Ψ ⨟ Θ ⊢ₛᵃ R ∼ (pskl_to_bskl_inh P).
Proof.
  intros Ψ Θ R Qt Hc Hwf P HwfB Hgf Href.
  eapply ad_pat_consis_refine_inh_gen with (Θ := Θ) (Δ := empty) (Psrc := P);
    [ exact Href | reflexivity | exact Hgf
    | auto | intros α Hα; clear - Hα; fsetdec | exact Hwf | exact HwfB | exact Hc ].
Qed.

(* ===================================================================== *)
(*  §2  The mutual soundness statement                                    *)
(* ===================================================================== *)

(** L-B threads the paper's [a_ty_mode_compat M P0] (:ty) instead of
    [ghost_free P0]: a TC input IS a type (⟹ ghost_free where the refinement
    needs it), an FN input is an arrow whose codomain recurses (the domain
    goes to consistency via WF, not ghost-freeness), a TI input is ◇. *)
Lemma a_ty_mode_compat_tc_ghost_free : forall P,
  a_ty_mode_compat mode_tc P -> pskl_ghost_free P.
Proof. intros P H; inversion H; subst; apply ptyp_to_pskl_ghost_free. Qed.

Lemma subst_ptyp_to_pskl_comm : forall A τ β,
  subst_pskl_in_pskl (ptyp_to_pskl τ) β (ptyp_to_pskl A)
    = ptyp_to_pskl (subst_ptyp_in_ptyp τ β A).
Proof.
  induction A; intros τ β; simpl; try solve [ f_equal; auto ];
    destruct_if;
    reflexivity.
Qed.

Lemma a_ty_mode_compat_subst_mono : forall M P τ β,
  a_ty_mode_compat M P -> mono_ptyp τ ->
  a_ty_mode_compat M (subst_pskl_in_pskl (ptyp_to_pskl τ) β P).
Proof.
  intros M P τ β H Hm; induction H; simpl.
  - apply a_ty_mode_compat__ti.
  - rewrite subst_ptyp_to_pskl_comm; apply a_ty_mode_compat__tc.
  - apply a_ty_mode_compat__fn; assumption.
Qed.

(** A ghost-free skeleton IS a type skeleton, hence TC-compatible — the reverse
    of [a_ty_mode_compat_tc_ghost_free], for re-entering TC recursions (ForallR). *)
Lemma pskl_ghost_free_ptyp : forall P,
  pskl_ghost_free P -> exists A, P = ptyp_to_pskl A.
Proof.
  induction P; simpl; intros H.
  - exists ptyp_unit; reflexivity.
  - match goal with |- exists A, pskl_var_b ?n = _ => exists (ptyp_var_b n) end; reflexivity.
  - match goal with |- exists A, pskl_var_f ?v = _ => exists (ptyp_var_f v) end; reflexivity.
  - destruct H as [H1 H2]; destruct (IHP1 H1) as [A1 ->];
      destruct (IHP2 H2) as [A2 ->]; exists (ptyp_arrow A1 A2); reflexivity.
  - destruct (IHP H) as [A ->]; exists (ptyp_all A); reflexivity.
  - contradiction.
  - contradiction.
Qed.

Lemma pskl_ghost_free_ty_mode_compat_tc : forall P,
  pskl_ghost_free P -> a_ty_mode_compat mode_tc P.
Proof.
  intros P H; destruct (pskl_ghost_free_ptyp _ H) as [A ->]; apply a_ty_mode_compat__tc.
Qed.

(** The subtyping conclusion (paper: ⊴, the fill of [P0], and the
    declarative subtyping of the subject, at the OUTPUT context). *)
Definition subtag_sound_concl
    (NM : a_sub_mode) (M : mode) (P0 : pskl) (Ψ : atoms)
    (Θ0 : aenv) (R : uskl) (Q : pskl) (Θ1 : aenv) : Prop :=
  a_wf_aenv Θ0 ->
  lc_uskl R ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ ⌊ R ⌋ˢ ->
  (NM = a_sub_mode_sk -> mod_comp_sk (pskl_to_bskl_inh P0) M) ->
  (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->
  Θ0 ⊴ Θ1 /\ a_wf_aenv Θ1 /\
  (exists Qt, bskl_to_pskl Qt = Q /\
     Ψ ⨟ Θ1 ⊢ₛᵃ[ NM | M ] R ⩽ Qt /\
     ad_refine_syn_f empty Θ1 empty (pskl_to_bskl_inh P0) Qt).

(** The flexible-walk conclusion (paper lemma:sound-decorated-flex-subtyping:
    the walked context [Θ0 ∣ Ξ] re-merges on the left). *)
Definition subtag_flex_sound_concl
    (NM : a_sub_mode) (M : mode) (P0 : pskl)
    (Θ0 Ξ : aenv) (α : atom) (A : pskl) (Θ1 : aenv) : Prop :=
  a_wf_aenv (Ξ ++ Θ0) ->
  a_decls Ξ ->
  (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P0 ->
  a_binds_tvar α (Ξ ++ Θ0) ->
  (NM = a_sub_mode_sk -> mod_comp_sk (pskl_to_bskl_inh P0) (mode_fn M)) ->
  (NM = a_sub_mode_ty -> a_ty_mode_compat (mode_fn M) P0) ->
  (Ξ ++ Θ0) ⊴ Θ1 /\ a_wf_aenv Θ1 /\
  (exists Qt, bskl_to_pskl Qt = A /\
     empty ⨟ Θ1 ⊢ₛᵃ[ NM | mode_fn M ] (uskl_var_f α) ⩽ Qt /\
     ad_refine_syn_f empty Θ1 empty (pskl_to_bskl_inh P0) Qt).

Theorem a_subtag_sound_bundle :
  (forall NM M P0 Ψ Θ0 R P' Θ1,
     Θ0 ⊢ᵗ[ NM | M | P0 | Ψ ] R ⩽˙ P' ⊣ Θ1 ->
     subtag_sound_concl NM M P0 Ψ Θ0 R P' Θ1) /\
  (forall NM M P0 Θ0 Ξ α P Θ1,
     a_subtag_flex NM M P0 Θ0 Ξ α P Θ1 ->
     subtag_flex_sound_concl NM M P0 Θ0 Ξ α P Θ1).
Proof.
  apply (a_subtag_subtag_flex_mutind
           (fun NM M P0 Ψ Θ0 R P' Θ1 _ =>
              subtag_sound_concl NM M P0 Ψ Θ0 R P' Θ1)
           (fun NM M P0 Θ0 Ξ α P Θ1 _ =>
              subtag_flex_sound_concl NM M P0 Θ0 Ξ α P Θ1));
    unfold subtag_sound_concl, subtag_flex_sound_concl.

  - (* Infer : output ⌊R⌋, context unchanged *)
    intros NM Ψ Θ0 R HΨ Hwf HlcS HwfP0 HwfS Hmod Hgf.
    split; [ apply a_isub_refl; exact Hwf | ].
    split; [ exact Hwf | ].
    exists (pskl_to_bskl_syn ⌊ R ⌋ˢ).
    split; [ apply bskl_to_pskl_pskl_to_bskl_syn | ].
    assert (Hvis : forall α0, α0 `in` ftvar_in_uskl R -> a_binds_tvar α0 Θ0).
    { intros α0 Hα0.
      rewrite <- ftvar_in_pskl_uskl_to_pskl in Hα0.
      destruct (a_wf_pskl_ftv_tvarish HwfS Hα0) as [HΔ | Ht];
        [ exfalso; clear - HΔ; fsetdec | exact Ht ]. }
    split.
    + apply ad_pat_sub__infer;
        [ exact HΨ
        | apply ad_pat_consis_refl_erase; assumption
        | apply is_sskl_pskl_to_bskl_syn; eauto using a_wf_pskl_lc ].
    + (* P0 = ◇ : the fill is the hole rule *)
      simpl. apply ad_refine_syn_f__hole;
        [ clear; fsetdec | exact HwfS ].

  - (* Check (TY) : audit-F2 — the consistency output [P'] is NOT literally [B]
       (for a flexible subject [α̂] it is the flex variable, ≡ B; paper
       full-algo-spec.tex:1441/1655, impl [U-FlexL]).  But [B] is a
       well-formed ghost-free type, so the fill conjunct
       [ad_refine_syn_f _ (inh B) Qt] forces the declarative consistency to
       transport from output [Qt] to [inh B] ([ad_pat_consis_refine_inh_target]),
       recovering the paper's "output ≡ B" reading. *)
    intros Ψ Θ0 Θ1 T B P' Hgfb HgT HgB Hc Hwf HlcT HwfB HwfT Hmod Hgf.
    specialize (Hgf eq_refl).
    destruct (a_consistag_sound_aux Hc Hwf HlcT HwfB HwfT
                ltac:(intros α0 Hα0; clear - Hα0; fsetdec)
                ltac:(intros β τ Hb; apply inter_empty_pointwise;
                      intros α0 Hα0; clear - Hα0; fsetdec)
                ltac:(intros Θa β b Θb Heq Hne;
                      apply inter_empty_pointwise;
                      intros α0 Hα0; clear - Hα0; fsetdec))
      as [Hle [Hwf1 [_ [_ [[Qt [HeQt [Hcons Hfill]]] _]]]]].
    assert (HwfB1 : Θ1 ⨟ empty ⊢ₚₛᵃ B)
      by (eapply a_wf_pskl_isub; [ exact HwfB | exact Hle ]).
    assert (Hcons' : Ψ ⨟ Θ1 ⊢ₛᵃ T ∼ (pskl_to_bskl_inh B))
      by (eapply ad_pat_consis_refine_inh_target;
            [ exact Hcons | exact Hwf1 | exact HwfB1
            | apply a_ty_mode_compat_tc_ghost_free; exact Hgf | exact Hfill ]).
    split; [ exact Hle | ].
    split; [ exact Hwf1 | ].
    exists (pskl_to_bskl_inh B).
    split; [ apply bskl_to_pskl_pskl_to_bskl_inh | ].
    split.
    + apply ad_pat_sub__check; [ exact HgT | exact HgB | exact Hcons' ].
    + apply ad_refine_syn_f_refl_inh; exact HwfB1.

  - (* ForallR (TY) : open the binder, run the body, strip the trailing
       suffix, and re-attach the rigid head (crib: a_consistag_sound_aux's
       ForallInh; the fill re-attaches via the ghost-free strip+rename). *)
    intros α Ψ Θ0 Θ1 Ξ R B Hgfb Hsuf Huq Hfr Hprem IH Hwf HlcS HwfP0 HwfS Hmod Hgf.
    assert (HgfB : pskl_ghost_free B)
      by (specialize (Hgf eq_refl);
          apply a_ty_mode_compat_tc_ghost_free in Hgf; simpl in Hgf; exact Hgf).
    simpl in HwfP0.
    rewrite dom_app in Hfr.
    (* the rule's own Barendregt-fresh binder replaces the old atom_fresh *)
    destruct (IH (ltac:(apply a_wf_aenv__tvar;
                          [ clear - Hfr; fsetdec | exact Hwf ]))
                HlcS
                (ltac:(eapply a_wf_pskl_all_syn_open_tvar;
                         [ exact HwfP0 | clear - Hfr; fsetdec ]))
                (ltac:(eapply a_wf_pskl_weaken;
                         [ intros x b Hb; unfold binds in *;
                           simpl; right; exact Hb
                         | exact HwfS ]))
                ltac:(intro HSK; discriminate HSK)
                (ltac:(intro He; apply pskl_ghost_free_ty_mode_compat_tc;
                       unfold open_pskl_wrt_pskl;
                       apply pskl_ghost_free_open_rec; exact HgfB)))
      as [Hle [Hwf1 [Qt [HeQt [Hsub Hfill]]]]].
    assert (HuqT : uniq (Ξ ++ (α ~ abind_tvar) ++ Θ1))
      by (apply a_wf_aenv_uniq_local; exact Hwf1).
    assert (HαΘ1 : α `notin` dom Θ1)
      by (clear - HuqT; simpl_env in HuqT; destruct_uniq;
          unfold disjoint in *; simpl_env in *; fsetdec).
    assert (HαΞ : α `notin` dom Ξ)
      by (clear - HuqT; simpl_env in HuqT; destruct_uniq;
          unfold disjoint in *; simpl_env in *; fsetdec).
    assert (Hwf1' : a_wf_aenv Θ1)
      by (eapply a_wf_aenv_strip_prefix_suffix_local; exact Hwf1).
    (* scoping chains for the suffix-strip freshness *)
    assert (HS : ftvar_in_uskl R [<=] dom Θ0).
    { intros α2 Hα2. rewrite <- ftvar_in_pskl_uskl_to_pskl in Hα2.
      destruct (a_wf_pskl_ftv_tvarish HwfS Hα2) as [HΔ | Ht];
        [ exfalso; clear - HΔ; fsetdec | ].
      destruct Ht as [Hb | [Hb | [τ Hb]]]; eapply binds_In; eauto. }
    assert (HB : ftvar_in_pskl B [<=] dom Θ0).
    { intros α2 Hα2.
      destruct (a_wf_pskl_ftv_tvarish HwfP0 ltac:(simpl; exact Hα2))
        as [HΔ | Ht]; [ exfalso; clear - HΔ; fsetdec | ].
      destruct Ht as [Hb | [Hb | [τ Hb]]]; eapply binds_In; eauto. }
    assert (HQt : ftvar_in_bskl Qt [<=]
                    (ftvar_in_pskl B `union` singleton α)).
    { intros α2 Hα2.
      rewrite <- (ftvar_in_pskl_bskl_to_pskl Qt) in Hα2.
      rewrite HeQt in Hα2.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                    B (pskl_var_f α)) as Hup.
      simpl in Hup. clear - Hα2 Hup. fsetdec. }
    assert (Hfresh : forall γ, γ `in` dom Ξ ->
              γ `notin` (ftvar_in_uskl R `union` ftvar_in_bskl Qt)).
    { intros γ Hγ.
      assert (HγΘ0 : γ `notin` dom Θ0)
        by (clear - Huq Hγ; destruct_uniq; unfold disjoint in *; fsetdec).
      assert (Hγα : γ <> α) by (intros ->; clear - HαΞ Hγ; fsetdec).
      clear - HγΘ0 Hγα HS HQt HB. fsetdec. }
    (* the suffix-stripped subtyping, α0-independent *)
    assert (Hsub1 : Ψ ⨟ ((α ~ abind_tvar) ++ Θ1)
                      ⊢ₛᵃ[ a_sub_mode_ty | mode_tc ] R ⩽ Qt).
    { eapply ad_pat_sub_strip_suffix with (Ξ := Ξ);
        [ exact Hsuf
        | simpl_env; simpl_env in Hwf1; exact Hwf1
        | exact Hfresh
        | simpl_env; simpl_env in Hsub; exact Hsub ]. }
    (* defs of Θ1 do not mention α *)
    assert (Hdefs1 : forall β τ, binds β (abind_flex_mono_def τ) Θ1 ->
              α `notin` ftvar_in_ptyp τ).
    { intros β τ Hb.
      assert (Hsc : ftvar_in_ptyp τ [<=] dom Θ1)
        by (eapply a_wf_aenv_def_ftv_dom; eauto).
      clear - Hsc HαΘ1. fsetdec. }
    split.
    { eapply a_isub_strip_tvar_mid with (Ξ := Ξ);
        [ exact HuqT | exact Huq | clear - Hfr; fsetdec | exact Hle ]. }
    split; [ exact Hwf1' | ].
    exists (bskl_all_inh (close_bskl_wrt_bskl α Qt)).
    split.
    { simpl. rewrite bskl_to_pskl_close. rewrite HeQt.
      rewrite close_pskl_wrt_pskl_open_pskl_wrt_pskl;
        [ reflexivity | clear - Hfr; fsetdec ]. }
    split.
    + apply ad_pat_sub__forall_r
        with (L := dom Θ1 `union` singleton α `union` ftvar_in_pskl B
                     `union` ftvar_in_uskl R `union` ftvar_in_bskl Qt).
      intros α0 Hα0.
      rewrite (subst_bskl_in_bskl_intro α (close_bskl_wrt_bskl α Qt)
                 (bskl_var_f α0));
        [ | rewrite ftvar_in_bskl_close_bskl_wrt_bskl; clear; fsetdec ].
      rewrite open_bskl_wrt_bskl_close_bskl_wrt_bskl.
      rewrite <- (subst_bskl_in_uskl_fresh_eq R (uskl_var_f α0) α)
        at 1;
        [ | clear - Hfr; fsetdec ].
      change ((α0 ~ abind_tvar) ++ Θ1)
        with (nil ++ (α0 ~ abind_tvar) ++ Θ1).
      apply ad_pat_sub_rename_tvar;
        [ simpl_env; exact Hsub1
        | simpl; exact HαΘ1
        | simpl; exact Hdefs1 ].
    + change (pskl_to_bskl_inh (pskl_all_syn B))
        with (bskl_all_inh (pskl_to_bskl_inh B)).
      apply ad_refine_syn_f__all
        with (L := dom Θ1 `union` dom Ξ `union` singleton α
                     `union` ftvar_in_pskl B `union` ftvar_in_bskl Qt).
      intros α0 Hα0.
      rewrite <- pskl_to_bskl_inh_open.
      rewrite (subst_bskl_in_bskl_intro α (close_bskl_wrt_bskl α Qt)
                 (bskl_var_f α0));
        [ | rewrite ftvar_in_bskl_close_bskl_wrt_bskl; clear; fsetdec ].
      rewrite open_bskl_wrt_bskl_close_bskl_wrt_bskl.
      assert (Hfr0 : α `notin` ftvar_in_pskl B) by (clear - Hfr; fsetdec).
      rewrite (subst_pskl_in_pskl_intro α B (pskl_var_f α0) Hfr0).
      rewrite <- subst_var_bskl_inh.
      eapply ad_refine_syn_f_delta_mono;
        [ eapply ad_refine_syn_f_ghost_free_strip_rename;
            [ simpl_env; simpl_env in Hfill; exact Hfill
            | reflexivity
            | apply pskl_to_bskl_inh_ghost_free;
              unfold open_pskl_wrt_pskl;
              apply pskl_ghost_free_open_rec; exact HgfB
            | simpl_env; simpl_env in Hwf1; exact Hwf1
            | simpl_env; exact HuqT
            | intros α2 Hα2;
              assert (HZin : α2 `in` (ftvar_in_pskl (open_pskl_wrt_pskl
                                       B (pskl_var_f α))
                                     `union` ftvar_in_bskl Qt))
                by (rewrite <- (ftvar_in_pskl_bskl_to_pskl
                                  (pskl_to_bskl_inh
                                     (open_pskl_wrt_pskl B (pskl_var_f α))))
                      in Hα2;
                    rewrite bskl_to_pskl_pskl_to_bskl_inh in Hα2;
                    clear - Hα2; fsetdec);
              pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                            B (pskl_var_f α)) as Hup;
              simpl in Hup;
              assert (HZB : α2 `in` (ftvar_in_pskl B `union` singleton α
                                    `union` ftvar_in_bskl Qt))
                by (clear - HZin Hup; fsetdec);
              assert (HγΘ0 : forall γ, γ `in` dom Ξ -> γ `notin` dom Θ0)
                by (clear - Huq; intros γ Hγ; destruct_uniq;
                    unfold disjoint in *; fsetdec);
              intro Hα2Ξ;
              assert (Hα2α : α2 <> α) by (intros ->; clear - HαΞ Hα2Ξ; fsetdec);
              assert (HZQt : α2 `in` ftvar_in_bskl Qt ->
                        α2 `in` (ftvar_in_pskl B `union` singleton α))
                by (intros HZq; apply HQt; exact HZq);
              assert (HZBd : α2 `in` ftvar_in_pskl B)
                by (clear - HZB Hα2α HZQt; fsetdec);
              specialize (HγΘ0 α2 Hα2Ξ); apply HγΘ0; apply HB; exact HZBd ]
        | clear - Hα0; fsetdec ].

  - (* UnivGhostR (SK) : axis — output ∀◇⌊R⌋, context unchanged *)
    intros Ψ Θ0 R HgS HΨ Hwf HlcS HwfP0 HwfS Hmod Hgf.
    split; [ apply a_isub_refl; exact Hwf | ].
    split; [ exact Hwf | ].
    exists (bskl_tophole (pskl_to_bskl_syn ⌊ R ⌋ˢ)).
    split; [ simpl; f_equal; apply bskl_to_pskl_pskl_to_bskl_syn | ].
    assert (Hvis : forall α0, α0 `in` ftvar_in_uskl R -> a_binds_tvar α0 Θ0).
    { intros α0 Hα0.
      rewrite <- ftvar_in_pskl_uskl_to_pskl in Hα0.
      destruct (a_wf_pskl_ftv_tvarish HwfS Hα0) as [HΔ | Ht];
        [ exfalso; clear - HΔ; fsetdec | exact Ht ]. }
    assert (Hg : guarded_pskl ⌊ R ⌋ˢ) by (apply guarded_uskl_to_pskl; auto).
    split.
    + apply ad_pat_sub__univ_ghost_r;
        [ exact HΨ | exact HgS
        | apply guarded_pskl_to_bskl_syn; exact Hg
        | apply is_sskl_pskl_to_bskl_syn; eauto using a_wf_pskl_lc
        | apply ad_pat_consis_refl_erase; assumption ].
    + (* P0 = ◇ : hole rule against the syn painting of ∀◇⌊R⌋ *)
      simpl.
      change (bskl_tophole (pskl_to_bskl_syn ⌊ R ⌋ˢ))
        with (pskl_to_bskl_syn (pskl_tophole ⌊ R ⌋ˢ)).
      apply ad_refine_syn_f__hole; [ clear; fsetdec | ].
      apply a_wf_pskl__tophole; [ exact Hg | exact HwfS ].

  - (* Arrow : a_consistag_sound_aux on the consistency premise (Δs = ∅),
       ⊴-transport its conclusions to Θ2, IH on the sub-premise. *)
    intros NM M Ψ Ψ1 Ψ2 Θ0 Θ1 Θ2 P0a P0b S1 S2 Q1 Q2
      Hc Hsub IH HΨ Hwf Hlc HwfP0 HwfS Hmod Hgf.
    inversion Hlc; subst.
    match goal with H : lc_uskl S1 |- _ => rename H into HlcS1 end.
    match goal with H : lc_uskl S2 |- _ => rename H into HlcS2 end.
    inversion HwfP0; subst.
    match goal with H : Θ0 ⨟ empty ⊢ₚₛᵃ P0a |- _ => rename H into HwfP0a end.
    match goal with H : Θ0 ⨟ empty ⊢ₚₛᵃ P0b |- _ => rename H into HwfP0b end.
    simpl in HwfS. inversion HwfS; subst.
    match goal with H : Θ0 ⨟ empty ⊢ₚₛᵃ ⌊ S1 ⌋ˢ |- _ => rename H into HwfS1 end.
    match goal with H : Θ0 ⨟ empty ⊢ₚₛᵃ ⌊ S2 ⌋ˢ |- _ => rename H into HwfS2 end.

    destruct (a_consistag_sound_aux Hc Hwf HlcS1 HwfP0a HwfS1
                ltac:(intros α0 Hα0; clear - Hα0; fsetdec)
                ltac:(intros β τ Hb; apply inter_empty_pointwise;
                      intros α0 Hα0; clear - Hα0; fsetdec)
                ltac:(intros Θa β b Θb Heq Hne;
                      apply inter_empty_pointwise;
                      intros α0 Hα0; clear - Hα0; fsetdec))
      as [Hle1 [Hwf1 [_ [_ [[Qt1 [HeQt1 [Hcons1 Hfill1]]] _]]]]].
    assert (HwfP0b1 : Θ1 ⨟ empty ⊢ₚₛᵃ P0b)
      by (eapply a_wf_pskl_isub; eauto).
    assert (HwfS21 : Θ1 ⨟ empty ⊢ₚₛᵃ ⌊ S2 ⌋ˢ)
      by (eapply a_wf_pskl_isub; eauto).
    destruct (IH Hwf1 HlcS2 HwfP0b1 HwfS21
                ltac:(intro HSK; specialize (Hmod HSK); simpl in Hmod;
                      inversion Hmod; subst; assumption)
                ltac:(intro HNMe; specialize (Hgf HNMe);
                      inversion Hgf; subst; assumption))
      as [Hle2 [Hwf2 [Qt2 [HeQt2 [Hsub2 Hfill2]]]]].
    split; [ eapply a_isub_trans; eauto | ].
    split; [ exact Hwf2 | ].
    exists (bskl_arrow Qt1 Qt2).
    split; [ simpl; f_equal; assumption | ].
    split.
    + eapply ad_pat_sub__arrow;
        [ eapply ad_pat_consis_isub; eauto | exact Hsub2 | exact HΨ ].
    + simpl. apply ad_refine_syn_f__arrow;
        [ eapply ad_refine_syn_f_isub; eauto | exact Hfill2 ].

  - (* ForallL (tagged) : instantiate with the decorated candidate ψg.
       IH at (Ξ ++ Θ0); strip the ⊴ over the decls prefix; conclude with
       ad_pat_sub__forall_l_tagged (its disciplined scope premise now
       comes straight off the rule, ⊴-transported). *)
    intros L NM M P0 Ψ Θ0 Θ1 ε R P' Ξ P1
      Hneq Hgor Hex Huq HwfP1 Hfam IHfam
      Hwf Hlc HwfP0 HwfS Hmod Hgf.
    destruct (atom_fresh L) as [α Hα].
    assert (Hdecls : a_decls Ξ) by (eapply a_extract_decls; eauto).
    (* pick a fresh decoration of P1 to instantiate the cofinite family *)
    assert (HlcP1 : lc_pskl P1) by (eapply a_wf_pskl_lc; eauto).
    destruct (a_tags_sort_decorate_exists (Hex α Hα) HlcP1 (L `union` Ψ))
      as [Ψg [ψg [Hint0 [Hsort Herase]]]].
    assert (Hint : Ψg ∩ Ψ [=] empty)
      by (clear - Hint0; fsetdec).
    assert (Hprem := Hfam Ψg ψg ltac:(clear - Hint0; fsetdec) Hsort Herase).
    assert (IH := IHfam Ψg ψg ltac:(clear - Hint0; fsetdec) Hsort Herase).
    assert (HwfΞΘ : a_wf_aenv (Ξ ++ Θ0)).
    { apply a_wf_aenv_prepend_decls; auto.
      - clear - Huq. solve_uniq.
      - intros γ Hγ. clear - Huq Hγ. destruct_uniq.
        unfold disjoint in *. fsetdec. }
    assert (Hlcψ : lc_uskl ψg)
      by (apply is_tskl_lc; inversion Hsort; auto).
    assert (HlcSψ : lc_uskl (open_uskl_wrt_uskl R ψg)).
    { apply lc_body_uskl_wrt_uskl; [ | exact Hlcψ ].
      eapply lc_body_uskl_all_etag_2. exact Hlc. }
    assert (Hmono : forall x (b : abind),
               binds x b Θ0 -> binds x b (Ξ ++ Θ0))
      by (intros x b Hb; unfold binds in *; apply in_or_app; auto).
    assert (HwfP0' : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P0)
      by (eapply a_wf_pskl_weaken; [ exact Hmono | exact HwfP0 ]).
    assert (HwfSψ : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ ⌊ open_uskl_wrt_uskl R ψg ⌋ˢ).
    { unfold open_uskl_wrt_uskl. rewrite uskl_to_pskl_open_rec.
      rewrite Herase.
      change (open_pskl_wrt_pskl_rec 0 P1 ⌊ R ⌋ˢ)
        with (open_pskl_wrt_pskl ⌊ R ⌋ˢ P1).
      simpl in HwfS.
      (* name the ∀-body premise explicitly rather than fishing for it with a
         `match goal` pattern over its binder — the binder name is Coq's to
         choose, so the pattern was brittle. *)
      inversion HwfS as [ | | | Lb Θb Δb Pb Hbody | | ]; subst.
      apply a_wf_pskl_open with (L := Lb);
        [ intros α0 Hα0;
          eapply a_wf_pskl_weaken; [ exact Hmono | apply Hbody; auto ]
        | exact HwfP1 ]. }
    destruct (IH HwfΞΘ HlcSψ HwfP0' HwfSψ Hmod Hgf)
      as [Hle [Hwf1 [Qt [HeQt [Hsub Hfill]]]]].
    split; [ eapply a_isub_strengthen_decls_src; eauto | ].
    split; [ exact Hwf1 | ].
    exists Qt. split; [ exact HeQt | ].
    split; [ | exact Hfill ].
    apply ad_pat_sub__forall_l_tagged with (Ψ' := Ψg) (ψ := ψg);
      [ exact Hneq | exact Hint | exact Hsort | | exact Hsub ].
    rewrite Herase. eapply a_wf_pskl_isub; eauto.

  - (* ForallL (untagged) : same as tagged. *)
    intros L NM M P0 Ψ Θ0 Θ1 R P' Ξ P1
      Hneq Hgor Hex Huq HwfP1 Hfam IHfam
      Hwf Hlc HwfP0 HwfS Hmod Hgf.
    destruct (atom_fresh L) as [α Hα].
    assert (Hdecls : a_decls Ξ) by (eapply a_extract_decls; eauto).
    (* pick a fresh decoration of P1 to instantiate the cofinite family *)
    assert (HlcP1 : lc_pskl P1) by (eapply a_wf_pskl_lc; eauto).
    destruct (a_tags_sort_decorate_exists (Hex α Hα) HlcP1 (L `union` Ψ))
      as [Ψg [ψg [Hint0 [Hsort Herase]]]].
    assert (Hint : Ψg ∩ Ψ [=] empty)
      by (clear - Hint0; fsetdec).
    assert (Hprem := Hfam Ψg ψg ltac:(clear - Hint0; fsetdec) Hsort Herase).
    assert (IH := IHfam Ψg ψg ltac:(clear - Hint0; fsetdec) Hsort Herase).
    assert (HwfΞΘ : a_wf_aenv (Ξ ++ Θ0)).
    { apply a_wf_aenv_prepend_decls; auto.
      - clear - Huq. solve_uniq.
      - intros γ Hγ. clear - Huq Hγ. destruct_uniq.
        unfold disjoint in *. fsetdec. }
    assert (Hlcψ : lc_uskl ψg)
      by (apply is_tskl_lc; inversion Hsort; auto).
    assert (HlcSψ : lc_uskl (open_uskl_wrt_uskl R ψg)).
    { apply lc_body_uskl_wrt_uskl; [ | exact Hlcψ ].
      eapply lc_body_uskl_all_syn_1. exact Hlc. }
    assert (Hmono : forall x (b : abind),
               binds x b Θ0 -> binds x b (Ξ ++ Θ0))
      by (intros x b Hb; unfold binds in *; apply in_or_app; auto).
    assert (HwfP0' : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P0)
      by (eapply a_wf_pskl_weaken; [ exact Hmono | exact HwfP0 ]).
    assert (HwfSψ : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ ⌊ open_uskl_wrt_uskl R ψg ⌋ˢ).
    { unfold open_uskl_wrt_uskl. rewrite uskl_to_pskl_open_rec.
      rewrite Herase.
      change (open_pskl_wrt_pskl_rec 0 P1 ⌊ R ⌋ˢ)
        with (open_pskl_wrt_pskl ⌊ R ⌋ˢ P1).
      simpl in HwfS.
      (* name the ∀-body premise explicitly rather than fishing for it with a
         `match goal` pattern over its binder. *)
      inversion HwfS as [ | | | Lb Θb Δb Pb Hbody | | ]; subst.
      apply a_wf_pskl_open with (L := Lb);
        [ intros α0 Hα0;
          eapply a_wf_pskl_weaken; [ exact Hmono | apply Hbody; auto ]
        | exact HwfP1 ]. }
    destruct (IH HwfΞΘ HlcSψ HwfP0' HwfSψ Hmod Hgf)
      as [Hle [Hwf1 [Qt [HeQt [Hsub Hfill]]]]].
    split; [ eapply a_isub_strengthen_decls_src; eauto | ].
    split; [ exact Hwf1 | ].
    exists Qt. split; [ exact HeQt | ].
    split; [ | exact Hfill ].
    apply ad_pat_sub__forall_l_untagged with (Ψ' := Ψg) (ψ := ψg);
      [ exact Hneq | exact Hint | exact Hsort | | exact Hsub ].
    rewrite Herase. eapply a_wf_pskl_isub; eauto.

  - (* Ghost (SK) : ◇ below the input P0 *)
    intros M Ψ Θ0 P0 HΨ Hwf HlcS HwfP0 HwfS Hmod Hgf.
    split; [ apply a_isub_refl; exact Hwf | ].
    split; [ exact Hwf | ].
    exists (pskl_to_bskl_inh P0).
    split; [ apply bskl_to_pskl_pskl_to_bskl_inh | ].
    split.
    + apply ad_pat_sub__ghost; [ exact HΨ | exact HwfP0 | exact (Hmod eq_refl) ].
    + apply ad_refine_syn_f_refl_inh; exact HwfP0.

  - (* GhostG (SK) : dotted ghost below ◇ *)
    intros M Ψ Θ0 HΨ Hwf HlcS HwfP0 HwfS Hmod Hgf.
    split; [ apply a_isub_refl; exact Hwf | ].
    split; [ exact Hwf | ].
    exists bskl_hole.
    split; [ reflexivity | ].
    split.
    + apply ad_pat_sub__ghostg; [ exact HΨ | ].
      specialize (Hmod eq_refl). simpl in Hmod. exact Hmod.
    + simpl. change bskl_hole with (pskl_to_bskl_syn pskl_hole).
      apply ad_refine_syn_f__hole;
        [ clear; fsetdec | apply a_wf_pskl__hole ].

  - (* UnivGhostL (SK) : drop the subject's ∀◇ *)
    intros M Ψ Θ0 Θ1 P0 R P' Hne Hprem IH Hwf HlcS HwfP0 HwfS Hmod Hgf.
    inversion HlcS; subst.
    simpl in HwfS.
    inversion HwfS; subst.
    destruct (IH Hwf ltac:(assumption) HwfP0 ltac:(assumption) Hmod Hgf)
      as [Hle [Hwf1 [Qt [HeqQt [Hsub Hfill]]]]].
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    exists Qt. split; [ exact HeqQt | ].
    split; [ apply ad_pat_sub__univ_ghost_l; assumption | exact Hfill ].

  - (* UnivGhostLG (SK) : drop the subject's dotted ∀◇ *)
    intros M Ψ Θ0 Θ1 P0 R P' Hne Hprem IH Hwf HlcS HwfP0 HwfS Hmod Hgf.
    inversion HlcS; subst.
    simpl in HwfS.
    inversion HwfS; subst.
    destruct (IH Hwf ltac:(assumption) HwfP0 ltac:(assumption) Hmod Hgf)
      as [Hle [Hwf1 [Qt [HeqQt [Hsub Hfill]]]]].
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    exists Qt. split; [ exact HeqQt | ].
    split; [ apply ad_pat_sub__univ_ghost_lg; assumption | exact Hfill ].

  - (* FlexMono : hand off to the decorated walk (Ξ = nil) *)
    intros NM M P0 Ψ Θ0 Θ1 α P Hflex IH HΨ Hwf HlcS HwfP0 HwfS Hmod Hgf.
    destruct (IH Hwf a_decls__nil HwfP0
                ltac:(simpl;
                      destruct (a_wf_pskl_ftv_tvarish HwfS (α := α)
                                  ltac:(simpl; clear; fsetdec))
                        as [HΔx | Htx];
                      [ exfalso; clear - HΔx; fsetdec | exact Htx ])
                Hmod Hgf)
      as [Hle [Hwf1 [Qt [HeqQt [Hsub Hfill]]]]].
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    exists Qt. split; [ exact HeqQt | ].
    split; [ | exact Hfill ].
    eapply ad_pat_sub_psi_cong; [ exact Hsub | clear - HΨ; fsetdec ].

  - (* Flex-Solve : deposit α̂0 := α̂→β̂ and recurse on the arrow.  The
       source lifts into the deposited context by a ⊴ (suffix-weaken the
       core, then re-prepend α̂0 and Ξ as declarations), so every
       hypothesis transports by ⊴-stability and the conclusion is
       FlexMono off the IH's arrow subtyping. *)
    intros NM M P0 Θ0 Θ1 Ξ α0 α β P Hne Hαf Hβf Hprem IH Hwf Hdecl HwfP0 Hαb Hmod Hgf.
    set (τab := ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)).
    set (Θmid := (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0).
    set (Θ' := Ξ ++ (α0 ~ abind_flex_mono_def τab) ++ Θmid).
    assert (Huq : uniq (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Hwf0 : a_wf_aenv Θ0).
    { eapply a_wf_aenv_app_r with (Θp := Ξ ++ (α0 ~ abind_flex_mono)).
      simpl_env. exact Hwf. }
    assert (Hbα : binds α abind_flex_mono Θmid)
      by (unfold Θmid; unfold binds; simpl; right; left; reflexivity).
    assert (Hbβ : binds β abind_flex_mono Θmid)
      by (unfold Θmid; unfold binds; simpl; left; reflexivity).
    assert (Hwfmid : a_wf_aenv Θmid).
    { unfold Θmid. apply a_wf_aenv__flex.
      { simpl. clear - Hβf Hne. simpl_env in *. fsetdec. }
      apply a_wf_aenv__flex;
        [ clear - Hαf; simpl_env in *; fsetdec | exact Hwf0 ]. }
    assert (Hwfdef : a_wf_aenv ((α0 ~ abind_flex_mono_def τab) ++ Θmid)).
    { apply a_wf_aenv__flex_def.
      - unfold Θmid. simpl. clear - Hαf Hβf Huq. simpl_env in *. solve_uniq.
      - apply a_wf_ptyp__arrow; apply a_wf_ptyp__var;
          [ right; left; exact Hbα | right; left; exact Hbβ ].
      - repeat constructor.
      - exact Hwfmid. }
    assert (HwfΘ' : a_wf_aenv Θ').
    { unfold Θ'. apply a_wf_aenv_prepend_decls; auto.
      - clear - Huq. solve_uniq.
      - intros γ Hγ. unfold Θmid. simpl_env.
        clear - Huq Hαf Hβf Hγ. destruct_uniq.
        unfold disjoint in *. simpl_env in *. fsetdec. }
    (* the source lifts into Θ' *)
    assert (Hbase : Θ0 ⊴ Θ').
    { unfold Θ', Θmid.
      replace (Ξ ++ (α0 ~ abind_flex_mono_def τab)
                 ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0)
        with ((Ξ ++ (α0 ~ abind_flex_mono_def τab)
                 ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono)) ++ Θ0)
        by (simpl_env; reflexivity).
      apply a_isub_weaken_suffix;
        [ apply a_wf_aenv_lc_aenv; exact Hwf0 | ].
      apply a_suffix_app; [ auto using a_decls_suffix | ].
      apply (a_suffix__cons α0);
        [ apply (a_suffix__cons β);
            [ apply (a_suffix__cons α);
                [ apply a_suffix__nil | constructor ]
            | constructor ]
        | constructor ]. }
    assert (Hbα0' : binds α0 (abind_flex_mono_def τab) Θ').
    { unfold Θ'. unfold binds. apply in_or_app. right. left. reflexivity. }
    assert (Hlift : (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0) ⊴ Θ').
    { apply a_isub_prepend_decls_src; auto.
      { intros γ Hb. right; left.
        unfold Θ'. unfold binds. apply in_or_app. left. exact Hb. }
      apply a_isub_prepend_decls_src;
        [ apply (a_decls__cons α0); apply a_decls__nil | | exact Hbase ].
      intros γ Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> _] | Hb'];
        [ right; right; exists τab; exact Hbα0' | inversion Hb' ]. }
    (* transported hypotheses for the IH *)
    assert (HwfP0' : Θ' ⨟ empty ⊢ₚₛᵃ P0)
      by (eapply a_wf_pskl_isub; eauto).
    assert (Hwfarr : Θ' ⨟ empty ⊢ₚₛᵃ ⌊ uskl_arrow (uskl_var_f α)
                                        (uskl_var_f β) ⌋ˢ).
    { simpl. apply a_wf_pskl__arrow; apply a_wf_pskl__var;
        right; right; left;
        (unfold Θ'; unfold binds; apply in_or_app; right; simpl;
         right; auto). }
    destruct (IH HwfΘ' ltac:(repeat constructor) HwfP0' Hwfarr Hmod Hgf)
      as [Hle' [Hwf1 [Qt [HeQt [Hsub Hfill]]]]].
    split. { eapply a_isub_trans; [ exact Hlift | exact Hle' ]. }
    split; [ exact Hwf1 | ].
    exists Qt. split; [ exact HeQt | ].
    split; [ | exact Hfill ].
    eapply ad_pat_sub__flex_mono with (τ := τab).
    + destruct Hle' as [_ Hdefs]. apply Hdefs. exact Hbα0'.
    + exact Hsub.

  - (* Flex-Assign : merge and re-enter the main judgment with the
       substituted subject; fold the definition back on the way out
       (the fill via [ad_refine_syn_f_fold_def_source], the subtyping
       via [flex_mono] when the subject IS the assigned variable). *)
    intros NM M P0 Θ0 Θ1 Ξ α β τ P Hβ1 Hprem IH Hwf Hdecl HwfP0 Hαb Hmod Hgf.
    assert (Hwfcons : a_wf_aenv ((β ~ abind_flex_mono_def τ) ++ Θ0))
      by (eapply a_wf_aenv_strip_prefix; eauto).
    inversion Hwfcons as [ | | βz τz Θz HβΘ0 Hwfτ Hm Hwf0 | | | ]; subst.
    assert (HβΞΘ0 : β `notin` dom (Ξ ++ Θ0)).
    { pose proof (a_wf_aenv_uniq_local Hwf) as Huq.
      clear - Huq. simpl_env in Huq. destruct_uniq.
      unfold disjoint in *. simpl_env in *. fsetdec. }
    assert (HwfΞΘ0 : a_wf_aenv (Ξ ++ Θ0))
      by (eapply a_wf_aenv_strip_mid; eauto).
    assert (Hwfpaint : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ ptyp_to_pskl τ).
    { apply a_scope_pskl_of_ptyp_vis;
        [ apply mono_ptyp_lc; exact Hm | ].
      intros α0 Hα0. right.
      pose proof (a_wf_ptyp_ftv_tvarish Hwfτ Hα0) as Ht.
      destruct Ht as [Hb | [Hb | [τ1 Hb]]];
        [ left | right; left | right; right; exists τ1 ];
        unfold binds in *; apply in_or_app; auto. }
    assert (HwfP0' : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ
              subst_pskl_in_pskl (ptyp_to_pskl τ) β P0).
    { eapply a_wf_pskl_subst_ctx with (b := abind_flex_mono_def τ);
        [ exact HwfP0 | reflexivity | exact HβΞΘ0 | clear; fsetdec
        | apply mono_ptyp_to_pskl_guarded; exact Hm | exact Hwfpaint ]. }
    assert (Hwfvarsub : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ
              subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)).
    { eapply a_wf_pskl_subst_ctx with (b := abind_flex_mono_def τ);
        [ apply a_wf_pskl__var; right; exact Hαb
        | reflexivity | exact HβΞΘ0 | clear; fsetdec
        | apply mono_ptyp_to_pskl_guarded; exact Hm | exact Hwfpaint ]. }
    destruct (IH HwfΞΘ0
                ltac:(apply pskl_to_uskl_lc; eapply a_wf_pskl_lc;
                      exact Hwfvarsub)
                HwfP0'
                ltac:(rewrite uskl_to_pskl_pskl_to_uskl; exact Hwfvarsub)
                ltac:(intro HSK; specialize (Hmod HSK);
                      rewrite <- pskl_to_bskl_inh_subst_mono;
                        [ apply mod_comp_sk_subst_mono;
                            [ exact Hmod | exact Hm ]
                        | exact Hm ])
                ltac:(intro HTY; specialize (Hgf HTY);
                      apply a_ty_mode_compat_subst_mono;
                        [ exact Hgf | exact Hm ]))
      as [Hle [Hwf1 [Qt [HeQt [Hsub Hfill]]]]].
    assert (Hle0 : Θ0 ⊴ Θ1)
      by (eapply a_isub_strengthen_decls_src; eauto).
    split.
    { apply a_isub_prepend_decls_src; [ exact Hdecl | | ].
      { intros γ Hb.
        apply a_binds_tvar_weaken_cons.
        eapply a_isub_binds_flex; [ exact Hle | ].
        unfold binds; apply in_or_app; left; exact Hb. }
      apply a_isub_cons_flex_def;
        [ exact Hle0 | apply mono_ptyp_lc; exact Hm ]. }
    split.
    { apply a_wf_aenv__flex_def;
        [ exact Hβ1
        | eapply a_wf_ptyp_isub; eauto
        | exact Hm | exact Hwf1 ]. }
    exists Qt.
    split; [ exact HeQt | ].
    split.
    + (* subtyping : the walked variable against Qt at the def-context *)
      assert (Hsub' : empty ⨟ ((β ~ abind_flex_mono_def τ) ++ Θ1)
                        ⊢ₛᵃ[ NM | mode_fn M ]
                        (pskl_to_uskl
                           (subst_pskl_in_pskl (ptyp_to_pskl τ) β
                              (pskl_var_f α))) ⩽ Qt).
      { eapply ad_pat_sub_weaken; [ exact Hsub | ].
        intros x b Hb. unfold binds in *. simpl. right. exact Hb. }
      simpl in Hsub'.
      match type of Hsub' with
      | context [ if ?e then _ else _ ] => destruct e as [-> | HneAB]
      end.
      * (* α = β : the subject reduced to the assigned monotype *)
        eapply ad_pat_sub__flex_mono.
        { unfold binds. left. reflexivity. }
        rewrite <- ptyp_to_uskl_syn_eq. exact Hsub'.
      * (* α ≠ β : the subject is untouched *)
        exact Hsub'.
    + (* fill : fold the definition back into the source *)
      eapply ad_refine_syn_f_fold_def_source with
        (β := β) (τ := τ)
        (Qs := subst_bskl_in_bskl (ptyp_to_bskl_syn τ) β
                 (pskl_to_bskl_inh P0));
        [ | unfold binds; left; reflexivity | exact Hm | reflexivity ].
      rewrite pskl_to_bskl_inh_subst_mono; [ | exact Hm ].
      eapply ad_refine_syn_f_weaken_ctx; [ exact Hfill | ].
      intros x b Hb. unfold binds in *. simpl. right. exact Hb.

  - (* Flex-Depend : β̂ joins the suffix at the Θ0-adjacent end, so the
       premise context is the conclusion's up to associativity. *)
    intros NM M P0 Θ0 Θ1 Ξ α β P Hne Hin Hprem IH Hwf Hdecl HwfP0 Hαb Hmod Hgf.
    assert (Hdecl' : a_decls (Ξ ++ (β ~ abind_flex_mono)))
      by (apply a_decls_app;
          [ exact Hdecl | apply (a_decls__cons β); apply a_decls__nil ]).
    destruct (IH ltac:(simpl_env; simpl_env in Hwf; exact Hwf) Hdecl'
                ltac:(simpl_env; simpl_env in HwfP0; exact HwfP0)
                ltac:(simpl_env; simpl_env in Hαb; exact Hαb) Hmod Hgf)
      as [Hle [Hwf1 [Qt [HeQt [Hsub Hfill]]]]].
    split; [ simpl_env in Hle; simpl_env; exact Hle | ].
    split; [ exact Hwf1 | ].
    exists Qt. auto.

  - (* Flex-Skip : strip the mid entry, IH, re-cons + lift the outputs. *)
    intros NM M P0 Θ0 Θ1 Ξ α β P Hne Hni Hβ1 Hprem IH Hwf Hdecl HwfP0 Hαb Hmod Hgf.
    assert (Hwf' : a_wf_aenv (Ξ ++ Θ0))
      by (eapply a_wf_aenv_strip_mid; eauto).
    assert (HwfP0' : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P0)
      by (eapply a_wf_pskl_strip_mid; eauto).
    destruct (IH Hwf' Hdecl HwfP0'
                ltac:(eapply a_binds_tvar_strip_mid;
                        [ exact Hαb
                        | intro He; inversion He; subst;
                          exact (Hne eq_refl)
                        | intro He; inversion He; subst;
                          exact (Hne eq_refl)
                        | intros τ1 He; inversion He; subst;
                          exact (Hne eq_refl) ])
                Hmod Hgf)
      as [Hle [Hwf1 [Qt [HeQt [Hsub Hfill]]]]].
    assert (Hlift : Θ1 ⊴ ((β ~ abind_flex_mono) ++ Θ1)).
    { apply a_isub_weaken_suffix;
        [ apply a_wf_aenv_lc_aenv; exact Hwf1 | ].
      apply (a_suffix__cons β); [ constructor | constructor ]. }
    split.
    { apply a_isub_prepend_decls_src; auto.
      { intros γ Hb.
        apply a_binds_tvar_weaken_cons.
        eapply a_isub_binds_flex; [ exact Hle | ].
        unfold binds; apply in_or_app; left; exact Hb. }
      apply a_isub_cons_flex.
      eapply a_isub_strengthen_decls_src; eauto. }
    split; [ apply a_wf_aenv__flex; auto | ].
    exists Qt. split; [ exact HeQt | ].
    split; [ eapply ad_pat_sub_isub; eauto
           | eapply ad_refine_syn_f_isub; eauto ].

  - (* Flex-SkipRigid : as Flex-Skip with a rigid head. *)
    intros NM M P0 Θ0 Θ1 Ξ α β P Hne Hni Hβ1 Hprem IH Hwf Hdecl HwfP0 Hαb Hmod Hgf.
    assert (Hwf' : a_wf_aenv (Ξ ++ Θ0))
      by (eapply a_wf_aenv_strip_mid; eauto).
    assert (HwfP0' : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P0)
      by (eapply a_wf_pskl_strip_mid; eauto).
    destruct (IH Hwf' Hdecl HwfP0'
                ltac:(eapply a_binds_tvar_strip_mid;
                        [ exact Hαb
                        | intro He; inversion He; subst;
                          exact (Hne eq_refl)
                        | intro He; inversion He; subst;
                          exact (Hne eq_refl)
                        | intros τ1 He; inversion He; subst;
                          exact (Hne eq_refl) ])
                Hmod Hgf)
      as [Hle [Hwf1 [Qt [HeQt [Hsub Hfill]]]]].
    split.
    { apply a_isub_prepend_decls_src; auto.
      { intros γ Hb.
        apply a_binds_tvar_weaken_cons.
        eapply a_isub_binds_flex; [ exact Hle | ].
        unfold binds; apply in_or_app; left; exact Hb. }
      apply a_isub_cons_tvar.
      eapply a_isub_strengthen_decls_src; eauto. }
    split; [ apply a_wf_aenv__tvar; auto | ].
    exists Qt. split; [ exact HeQt | ].
    split.
    + eapply ad_pat_sub_weaken; [ exact Hsub | ].
      intros x b0 Hb; unfold binds; right; exact Hb.
    + eapply ad_refine_syn_f_weaken_ctx; [ exact Hfill | ].
      intros x b0 Hb; unfold binds; right; exact Hb.
  - (* Flex-SkipTmVar : as Flex-SkipRigid with a TERM entry.  A term entry is
       never [a_binds_tvar], so [P0] cannot mention it (that is what supplies
       [a_wf_pskl_strip_mid]'s freshness, which the rule does not carry — the
       twin walk's [Assign-SkipTmVar] does not carry it either), and the two
       outputs weaken by [a_isub_cons_var_typ] / [a_wf_ptyp_isub]. *)
    intros NM M P0 Θ0 Θ1 Ξ α x Q P Hxout Hprem IH Hwf Hdecl HwfP0 Hαb Hmod Hgf.
    assert (Huq : uniq (Ξ ++ (x ~ abind_var_typ Q) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Hbx : binds x (abind_var_typ Q)
                    (Ξ ++ (x ~ abind_var_typ Q) ++ Θ0))
      by (apply binds_app_3; apply binds_app_2;
          unfold binds; simpl; left; reflexivity).
    assert (Hxfr : x `notin` ftvar_in_pskl P0).
    { intro Hin.
      destruct (a_wf_pskl_ftv_tvarish HwfP0 Hin) as [Hemp | Hbt];
        [ clear - Hemp; fsetdec | ].
      destruct Hbt as [Hb | [Hb | [τ0 Hb]]];
        pose proof (binds_unique _ _ _ _ _ Hbx Hb Huq) as Hc; discriminate Hc. }
    assert (Hwf' : a_wf_aenv (Ξ ++ Θ0))
      by (eapply a_wf_aenv_strip_mid; eauto).
    assert (HwfT : a_wf_aenv ((x ~ abind_var_typ Q) ++ Θ0))
      by (eapply a_wf_aenv_app_r; exact Hwf).
    apply a_wf_aenv_var_typ_inv in HwfT.
    destruct HwfT as [_ [HwfQ0 _]].
    assert (HwfQ' : a_wf_ptyp (Ξ ++ Θ0) Q)
      by (eapply a_wf_ptyp_weaken;
          [ intros y b0 Hb; apply binds_app_3; exact Hb | exact HwfQ0 ]).
    destruct (IH Hwf' Hdecl
                ltac:(eapply a_wf_pskl_strip_mid; [ exact HwfP0 | exact Hxfr ])
                ltac:(eapply a_binds_tvar_strip_mid;
                        [ exact Hαb
                        | intro He; discriminate He
                        | intro He; discriminate He
                        | intros τ1 He; discriminate He ])
                Hmod Hgf)
      as [Hle [Hwf1 [Qt [HeQt [Hsub Hfill]]]]].
    split.
    { apply a_isub_prepend_decls_src; auto.
      { intros γ Hb.
        apply a_binds_tvar_weaken_cons.
        eapply a_isub_binds_flex; [ exact Hle | ].
        unfold binds; apply in_or_app; left; exact Hb. }
      apply a_isub_cons_var_typ;
        [ eapply a_isub_strengthen_decls_src; eauto
        | eapply a_wf_ptyp_lc; exact HwfQ0 ]. }
    split.
    { apply a_wf_aenv__var_typ; [ exact Hxout | | exact Hwf1 ].
      eapply a_wf_ptyp_isub; [ exact HwfQ' | exact Hle ]. }
    exists Qt. split; [ exact HeQt | ].
    split.
    + eapply ad_pat_sub_weaken; [ exact Hsub | ].
      intros y b0 Hb; unfold binds; right; exact Hb.
    + eapply ad_refine_syn_f_weaken_ctx; [ exact Hfill | ].
      intros y b0 Hb; unfold binds; right; exact Hb.

  - (* Flex-SkipTmVar (skeleton entry) — the same, at [a_scope_pskl]. *)
    intros NM M P0 Θ0 Θ1 Ξ α x Q P Hxout Hprem IH Hwf Hdecl HwfP0 Hαb Hmod Hgf.
    assert (Huq : uniq (Ξ ++ (x ~ abind_var_skl Q) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Hbx : binds x (abind_var_skl Q)
                    (Ξ ++ (x ~ abind_var_skl Q) ++ Θ0))
      by (apply binds_app_3; apply binds_app_2;
          unfold binds; simpl; left; reflexivity).
    assert (Hxfr : x `notin` ftvar_in_pskl P0).
    { intro Hin.
      destruct (a_wf_pskl_ftv_tvarish HwfP0 Hin) as [Hemp | Hbt];
        [ clear - Hemp; fsetdec | ].
      destruct Hbt as [Hb | [Hb | [τ0 Hb]]];
        pose proof (binds_unique _ _ _ _ _ Hbx Hb Huq) as Hc; discriminate Hc. }
    assert (Hwf' : a_wf_aenv (Ξ ++ Θ0))
      by (eapply a_wf_aenv_strip_mid; eauto).
    assert (HwfT : a_wf_aenv ((x ~ abind_var_skl Q) ++ Θ0))
      by (eapply a_wf_aenv_app_r; exact Hwf).
    apply a_wf_aenv_var_skl_inv in HwfT.
    destruct HwfT as [_ [HscQ0 _]].
    assert (HscQ' : a_scope_pskl (Ξ ++ Θ0) Q)
      by (eapply a_scope_pskl_weaken;
          [ intros y b0 Hb; apply binds_app_3; exact Hb | exact HscQ0 ]).
    destruct (IH Hwf' Hdecl
                ltac:(eapply a_wf_pskl_strip_mid; [ exact HwfP0 | exact Hxfr ])
                ltac:(eapply a_binds_tvar_strip_mid;
                        [ exact Hαb
                        | intro He; discriminate He
                        | intro He; discriminate He
                        | intros τ1 He; discriminate He ])
                Hmod Hgf)
      as [Hle [Hwf1 [Qt [HeQt [Hsub Hfill]]]]].
    split.
    { apply a_isub_prepend_decls_src; auto.
      { intros γ Hb.
        apply a_binds_tvar_weaken_cons.
        eapply a_isub_binds_flex; [ exact Hle | ].
        unfold binds; apply in_or_app; left; exact Hb. }
      apply a_isub_cons_var_skl;
        [ eapply a_isub_strengthen_decls_src; eauto
        | eapply a_scope_pskl_lc; exact HscQ0 ]. }
    split.
    { apply a_wf_aenv__var; [ exact Hxout | | exact Hwf1 ].
      eapply a_scope_pskl_isub; [ exact HscQ' | exact Hle ]. }
    exists Qt. split; [ exact HeQt | ].
    split.
    + eapply ad_pat_sub_weaken; [ exact Hsub | ].
      intros y b0 Hb; unfold binds; right; exact Hb.
    + eapply ad_refine_syn_f_weaken_ctx; [ exact Hfill | ].
      intros y b0 Hb; unfold binds; right; exact Hb.

Qed.

(* The flagship check: no admits, no axioms. *)
Print Assumptions a_subtag_sound_bundle.
