(** Frost — declarative subtyping metatheory: consistency-subtyping
    transitivity (paper Lemma B.3) — [d_consis_sub_trans] (+ the
    nil-Δ corollary) and the new helper [d_consis_RHS_syn_color_eq]
    used to pin LHS syn-shape under wf. *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Sorting.Permutation.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.subtyping.prop_basics.
Require Import src.frost.decl.subtyping.prop_consis_trans.

Set Implicit Arguments.

(** [d_consis_RHS_syn_color_eq]: a [d_consis] with a [syn_color]-shaped
    RHS pins the LHS to [syn_color X] (and forces Δ = nil) under wf.
    Mirror of [d_consis_gen_RHS_syn_color_eq] (prop_typing/gen.v) for the
    non-gen [d_consis]. The [__forall_inh*] / [__forall_inh] cases are
    vacuous on a [syn_color]-shaped RHS (colour mismatch: [syn_color]
    paints [colour_syn], not [colour_inh]); [__forall_syn_tagged] is
    LHS-unwf (etag is not [d_wf_typ]). Used by [d_consis_sub_trans]
    __infer / __check sub-cases for LHS rigidity. *)
Lemma d_consis_RHS_syn_color_eq : forall Δ Γ A X,
    Δ ⨟ Γ ⊨ A ≈ (syn_color X) ->
    d_wf_typ Γ A ->
    A = syn_color X /\ Δ = nil.
Proof.
  intros Δ Γ A X Hc.
  remember (syn_color X) as A_RHS eqn:HeqA.
  generalize dependent X.
  induction Hc; intros X' HeqA HwfA; subst.
  - (* __unit *)
    destruct X'; simpl in HeqA; try discriminate.
    split; reflexivity.
  - (* __var *)
    destruct X'; simpl in HeqA; try discriminate.
    injection HeqA; intro; subst.
    split; reflexivity.
  - (* __forall_inh_tagged: RHS = typ_all_col colour_inh, syn_color paints colour_syn. *)
    destruct X'; simpl in HeqA; try discriminate.
  - (* __forall_syn_tagged: LHS = typ_all_etag — not d_wf_typ. *)
    inversion HwfA.
  - (* __forall_syn: LHS = typ_all_col colour_syn T, RHS = typ_all_col colour_syn A. *)
    destruct X'; simpl in HeqA; try discriminate.
    inversion HeqA; subst.
    inversion HwfA; subst.
    pick fresh X0 for
      (L `union` L0 `union` ftvar_in_typ T `union` ftvar_in_ctyp X' `union` dom Γ).
    assert (HX_L : X0 `notin` L) by fsetdec.
    assert (HX_L0 : X0 `notin` L0) by fsetdec.
    assert (HnotinT : X0 `notin` ftvar_in_typ T) by fsetdec.
    assert (HnotinSC : X0 `notin` ftvar_in_typ (syn_color X')).
    { rewrite syn_color_ftvar. fsetdec. }
    pose proof (H0 X0 HX_L
                   (open_ctyp_wrt_ctyp X' (ctyp_var_f X0))) as Heq.
    rewrite syn_color_open_var in Heq.
    specialize (Heq eq_refl (H3 X0 HX_L0)).
    destruct Heq as [Heq_body HΔ_eq]; subst.
    split; [| reflexivity].
    f_equal.
    apply (open_typ_wrt_typ_inj T (syn_color X') X0); auto.
  - (* __forall_inh: RHS = typ_all_col colour_inh, syn_color paints colour_syn. *)
    destruct X'; simpl in HeqA; discriminate.
  - (* __arrow *)
    destruct X'; simpl in HeqA; try discriminate.
    inversion HeqA; subst.
    inversion HwfA as [| | ? ? ? HwfT1 HwfT2 |]; subst.
    destruct (IHHc1 X'1 eq_refl HwfT1) as [HT1eq HΔ1eq]; subst.
    destruct (IHHc2 X'2 eq_refl HwfT2) as [HT2eq HΔ2eq]; subst.
    split; reflexivity.
Qed.

(** Paper Lemma B.3 (Consistency-Subtyping Transitivity) —
    [paper-ref: thm:consist-subtyping-transitivity, syntax-directed.tex:161].

    Stated modulo [Permutation] since the conclusion's Δ depends on
    arrow-structural shuffling (same issue as [d_consis_compose]).

    Side conditions:
    - [list_disjoint Δ Δ']: linearity at the cross.
    - [M = mode_ti -> Δ = nil]: encoding-only — d_sub__infer rigidly
      fixes [Δ = nil] on its conclusion. With the new [d_wf_typ Γ T]
      premise + [d_consis_RHS_syn_color_eq] the __infer case derives
      [Δ = nil] independently; the side condition is kept for
      uniformity with the __forall_l_tagged path.
    - [d_wf_typ Γ T]: added post-refactor — the new [d_consis__forall_syn]
      rule allows non-mono [syn_color] LHS, so [d_consis_LHS_syn_color_mono]
      is no longer sound; [d_consis_RHS_syn_color_eq] requires wf on
      the LHS to rule out the [typ_all_etag] case of [__forall_syn_tagged].

    All 6 d_sub cases close:
    - [__infer] / [__check]: pin [T0 = syn_color T_rule] and [Δ0 = nil]
      via [d_consis_RHS_syn_color_eq] (needs HwfT); reconstruct
      d_sub__infer / d_sub__check via Hs's body directly.
    - [__forall_l_*]: vacuous via Hc inversion (d_consis's RHS grammar
      does not include [typ_all_etag]).
    - [__arg]: T0 must be arrow (forced by Hc's __arrow inversion); the
      recursive IH covers the function-result side at any shape.
    - [__forall_r]: closed via [d_sub_subst_mono] alpha-renaming. *)
Lemma d_consis_sub_trans : forall M Δ Δ' Γ T A B,
    Δ ⨟ Γ ⊨ T ≈ A ->
    Γ ⊢[ M ; Δ' ] A ⊑ B ->
    list_disjoint Δ Δ' ->                      (* linearity: cross-disjoint *)
    (M = mode_ti -> Δ = nil) ->
    d_wf_typ Γ T ->
    exists Δc, Permutation Δc (Δ ++ Δ') /\ Γ ⊢[ M ; Δc ] T ⊑ B.
Proof.
  intros M Δ Δ' Γ T A B Hc Hs.
  generalize dependent T. generalize dependent Δ.
  induction Hs; intros Δ0 T0 Hc Hdis Hti HwfT.
  - (* d_sub__infer: M = mode_ti, Δ' = nil. Pin T0 = syn_color T and
       Δ0 = nil via [d_consis_RHS_syn_color_eq] (uses HwfT); then the
       goal collapses to Hs's body via d_sub__infer. *)
    edestruct d_consis_RHS_syn_color_eq as [HT0eq HΔ0eq];
      [ exact Hc | exact HwfT | ]; subst.
    exists nil. split; [reflexivity |].
    apply d_sub__infer. exact H.
  - (* d_sub__check: M = mode_tc. Pin T0 = syn_color T and Δ0 = nil
       similarly; reconstruct d_sub__check via Hs's body + guarded_typ. *)
    edestruct d_consis_RHS_syn_color_eq as [HT0eq HΔ0eq];
      [ exact Hc | exact HwfT | ]; subst.
    exists Δ. split; [reflexivity |].
    apply d_sub__check; assumption.
  - (* d_sub__forall_r: B = typ_all_col colour_inh A.
       Closed via [d_sub_subst_mono]: pick fresh X0, get IH at X0 with
       canonical Δc, then alpha-rename X0 → X' for arbitrary X'. *)
    pick fresh X0 for
      (L `union` dom Γ `union` ftvar_in_typ A `union` ftvar_in_typ T0).
    assert (HX0 : X0 `notin` L) by fsetdec.
    edestruct (H0 X0 HX0 Δ0 T0) as [Δc [Hperm Hsub_X0]].
    + apply d_consis_weakening_head; exact Hc.
    + exact Hdis.
    + intros HM_ti. discriminate.
    + apply d_wf_typ_weakening_head; exact HwfT.
    + exists Δc. split; [exact Hperm |].
      apply d_sub__forall_r with
        (L := L `union` dom Γ `union` ftvar_in_typ A `union` ftvar_in_typ T0
              `union` singleton X0).
      intros X' HX'.
      (* Step 1: weaken Hsub_X0 to insert (X'~tvar). *)
      assert (Hsub_weak : d_sub mode_tc Δc ((X0 ~ dbind_tvar)
        ++ (X' ~ dbind_tvar) ++ Γ) T0 (open_typ_wrt_typ A (typ_var_f X0))).
      { rewrite_env (((X0 ~ dbind_tvar) ++ nil) ++ (X' ~ dbind_tvar) ++ Γ).
        apply d_sub_weakening; auto. }
      (* Step 2: apply d_sub_subst_mono with B = typ_var_f X' to rename X0 → X'. *)
      apply d_sub_subst_mono
        with (Γ1 := nil) (X := X0) (Γ2 := (X' ~ dbind_tvar) ++ Γ)
             (B := typ_var_f X') in Hsub_weak; auto.
      * (* Simplify the substituted types:
           - subst (typ_var_f X') X0 T0 = T0  (since X0 ∉ ftv T0)
           - subst (typ_var_f X') X0 (open A X0) = open A X' (via _intro reverse)
        *)
        rewrite (subst_typ_in_typ_fresh_eq T0 (typ_var_f X') X0) in Hsub_weak
          by fsetdec.
        rewrite <- (subst_typ_in_typ_intro X0) in Hsub_weak by fsetdec.
        exact Hsub_weak.
      * apply mono_typ__var.
      * apply d_wf_typ__var. left; reflexivity.
  - (* d_sub__arg: M = mode_fn m, A = typ_arrow A1 A2.
       CLOSED via [d_consis_compose_nil_RHS] (m_inner = mode_ti → Δc02 = nil)
       and the recursive IH on the function-result side. The inversion
       pattern now has 8 alternatives (7 bars before [__arrow]) due to
       the new [d_consis__forall_inh] constructor. *)
    inversion Hc as
      [| | | | | | Δc01 Δc02 ? T01 T02 A01 A02 Hca Hcb Hcdisarr];
      subst.
    apply list_disjoint_app_l_iff in Hdis as [Hdisa Hdisb].
    apply list_disjoint_app_r_iff in Hdisa as [Hd_a_1 Hd_a_2].
    apply list_disjoint_app_r_iff in Hdisb as [Hd_b_1 Hd_b_2].
    edestruct d_consis_compose as [Δd1 [Hperm1 Hccarg]];
      [exact Hca | exact H | exact Hd_a_1 |].
    (* Derive m = mode_ti → Δc02 = nil from Hs body at mode_ti = __infer. *)
    assert (HΔc02_ti : m = mode_ti -> Δc02 = nil).
    { intro Hm. subst m.
      inversion Hs; subst.
      - (* Hs body: d_consis nil Γ (syn_color T0) (syn_color A0).
           Derive [is_syn_typ (syn_color T0)] from the body's structure
           via [d_consis_lhs_syn_color_is_syn_typ] (no mono needed). *)
        eapply d_consis_compose_nil_RHS; eauto.
        eapply d_consis_lhs_syn_color_is_syn_typ; eauto.
      - match goal with H : mode_ti <> mode_ti |- _ => exfalso; apply H; reflexivity end. }
    (* Apply recursive IH on the function-result side. *)
    inversion HwfT; subst.
    edestruct IHHs as [Δd2 [Hperm2 Hsubres]];
      [exact Hcb | exact Hd_b_2 | exact HΔc02_ti | assumption |].
    exists (Δd1 ++ Δd2). split.
    + transitivity ((Δc01 ++ Δ1) ++ (Δc02 ++ Δ2)).
      * apply Permutation_app; assumption.
      * apply list_swap_middle.
    + apply d_sub__arg; assumption.
  - (* d_sub__forall_l_tagged: A = typ_all_etag, but d_consis RHS is
       never typ_all_etag. *)
    inversion Hc.
Qed.

(** Narrowed corollary: both Δ-sides nil. The [d_wf_typ Γ T]
    precondition is now actively used by [d_consis_sub_trans] to
    pin [T = syn_color X] in the __infer / __check cases via
    [d_consis_RHS_syn_color_eq]. Permutation Δc (nil ++ nil) forces
    Δc = nil. *)
Lemma d_consis_sub_trans_nil : forall M Γ T A B,
    nil ⨟ Γ ⊨ T ≈ A ->
    Γ ⊢[ M ; nil ] A ⊑ B ->
    d_wf_typ Γ T ->
    Γ ⊢[ M ; nil ] T ⊑ B.
Proof.
  intros M Γ T A B Hc Hs HwfT.
  edestruct d_consis_sub_trans as [Δc [Hperm Hsub]];
    [ exact Hc | exact Hs | apply list_disjoint_nil_l
    | intros _; reflexivity
    | exact HwfT
    | ].
  apply Permutation_sym in Hperm. apply Permutation_nil in Hperm.
  subst Δc. exact Hsub.
Qed.

