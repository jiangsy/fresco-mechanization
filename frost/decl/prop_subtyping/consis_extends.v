(** Frost — declarative subtyping metatheory: consistency extends subtyping
    (paper D.5) and [d_typing_lift_mono]. *)

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
Require Import src.frost.decl.prop_subtyping.basics.
Require Import src.frost.decl.prop_subtyping.consis_compose.

Set Implicit Arguments.

(** Paper Lemma D.5 (Consistency extends subtyping) — [paper-ref: lemma:consis-sub].
    The declarative version of the algorithmic "Consistency-Subtyping
    Transitivity" (paper Lemma B.3).

    Stated modulo [Permutation] since the conclusion's Δ depends on
    arrow-structural shuffling (same issue as [d_consis_compose]).

    Lone remaining side condition [M = mode_ti -> Δ = nil] is encoding
    only: d_sub__infer rigidly fixes [Δ = nil] on the conclusion, which
    the paper handles silently via the [syn{·}]-painting discipline on
    the typing context. The earlier T-shape side conditions
    ([T ≠ typ_all_etag] / [T ≠ typ_all_plain]) and the [ctyp]-era
    [is_typ T] contract are both gone:

    - [__infer] / [__check]: Hs's body is itself a [d_consis] with a
      [syn_color] LHS, so [d_consis_LHS_syn_color_mono] forces the
      middle type ([A] of the lemma = Hc's RHS) to be [mono_typ]; then
      [d_consis_mono_RHS] applied to Hc gives T = A and T mono.
    - [__forall_l_*]: vacuous via Hc inversion (d_consis's RHS grammar
      does not include [typ_all_etag] / [typ_all_plain]).
    - [__arg]: T must be arrow (forced by Hc's __arrow inversion); the
      recursive IH covers the function-result side at any shape. *)
Lemma d_consis_extends_d_sub : forall M Δ Δ' Γ T A B,
    Δ ⨟ Γ ⊨ T ≈ A ->
    Γ ⊢[ M ; Δ' ] A ⊑ B ->
    list_disjoint Δ Δ' ->                      (* linearity: cross-disjoint *)
    (M = mode_ti -> Δ = nil) ->
    exists Δc, Permutation Δc (Δ ++ Δ') /\ Γ ⊢[ M ; Δc ] T ⊑ B.
Proof.
  intros M Δ Δ' Γ T A B Hc Hs.
  generalize dependent T. generalize dependent Δ.
  induction Hs; intros Δ0 T0 Hc Hdis Hti.
  - (* d_sub__infer: M = mode_ti, Δ' = nil. POST-REFACTOR: the body
       H : d_consis nil Γ (syn_color T) (syn_color A) no longer pins T
       mono (the new __forall_syn rule allows non-mono LHS), so the
       chain that derived T0 mono from Hc + Hs is broken. Closure would
       require adding [d_wf_typ Γ T] premise so [d_consis_gen_RHS_syn_color_eq]
       (lives in prop_typing.v — forward reference) can pin T0 syn-shape. *)
    admit.
  - (* d_sub__check: M = mode_tc. Same post-refactor mono gap. *)
    admit.
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
    edestruct IHHs as [Δd2 [Hperm2 Hsubres]];
      [exact Hcb | exact Hd_b_2 | exact HΔc02_ti |].
    exists (Δd1 ++ Δd2). split.
    + transitivity ((Δc01 ++ Δ1) ++ (Δc02 ++ Δ2)).
      * apply Permutation_app; assumption.
      * apply list_swap_middle.
    + apply d_sub__arg; assumption.
  - (* d_sub__forall_l_tagged: A = typ_all_etag, but d_consis RHS is
       never typ_all_etag. *)
    inversion Hc.
Admitted.
(** d_consis_extends_d_sub: post the [d_consis__forall_inh] addition,
    the [d_sub__arg] case inherits a [is_syn_typ A] admit through the
    chain [d_consis_compose_nil_RHS] needs (where A is the mid type
    coming from [d_sub__infer]'s body). The standalone fact
    [d_wf_typ Γ (syn_color C) → is_syn_typ (syn_color C)] is
    derivable but the helper isn't currently in scope here.

    Otherwise Qed in the paper-faithful form (no
    [is_typ T] contract). All 6 d_sub cases close:
    - __infer / __check: derive mono_typ T0 by chaining
      [d_consis_LHS_syn_color_mono] (on Hs body's syn_color LHS) into
      [d_consis_mono_RHS] (on Hc); the resulting equality T0 = A pins
      the conclusion's LHS, and Hs body discharges the d_consis premise.
    - __forall_l_*: vacuous via Hc inversion (d_consis RHS is never
      typ_all_etag/plain).
    - __arg: closed via [d_consis_compose_nil_RHS] (derives
      m_inner = mode_ti → Δc02 = nil) plus the recursive IH.
    - __forall_r: closed via [d_sub_subst_mono] alpha-renaming: pick
      fresh X0, get IH at X0 giving canonical Δc, then for each X' in
      the cofinite premise rename X0 → X' via mono substitution. *)

(** Narrowed corollary: both Δ-sides nil. The [d_wf_typ Γ T]
    precondition is kept for backward compatibility with call sites in
    [prop_typing.v] but is unused — the parent now needs no T-shape
    side conditions. Permutation Δc (nil ++ nil) forces Δc = nil. *)
Lemma d_consis_extends_d_sub_nil : forall M Γ T A B,
    nil ⨟ Γ ⊨ T ≈ A ->
    Γ ⊢[ M ; nil ] A ⊑ B ->
    d_wf_typ Γ T ->
    Γ ⊢[ M ; nil ] T ⊑ B.
Proof.
  intros M Γ T A B Hc Hs _.
  edestruct d_consis_extends_d_sub as [Δc [Hperm Hsub]];
    [ exact Hc | exact Hs | apply list_disjoint_nil_l
    | intros _; reflexivity
    | ].
  apply Permutation_sym in Hperm. apply Permutation_nil in Hperm.
  subst Δc. exact Hsub.
Qed.

(** Lift [d_typing] from [mode_ti] to any [m_target] at the SAME mono
    type, given the corresponding refl [d_sub m_target nil Γ A A].

    The signature is restricted to [m_orig = mode_ti] (sufficient for
    D1's __abs / __abs_anno body-conversion uses, where the body
    sits at [decr_mode mode_ti = mode_ti]).

    Closure cases:
    - __unit / __var / __anno: wrap via [d_typing__sub] at m_target.
    - __sub: compose the inner mode_ti d_sub with [Hrefl] using
      [d_consis_extends_d_sub_nil].
    - __forall: produces mode_tc; contradicts m_orig = mode_ti.
    - __abs / __abs_anno: re-apply at m_target. Body sits at
      [decr_mode mode_ti = mode_ti] (preserved). Inner refl on the
      body's result type derived via [d_sub_arrow_refl_inner] on
      mono LHS.
    - __app: requires the function's argument type to be mono, which
      is NOT automatic from d_typing__app's premises. Admitted; same
      research-grade gap as D1's __app case. *)
Lemma d_typing_lift_mono_mut :
    (forall m Γ e A,
        d_typing m Γ e A ->
        m = mode_ti ->
        forall m_target,
          mono_typ A ->
          d_wf_denv Γ ->
          d_sub m_target nil Γ A A ->
          d_typing m_target Γ e A)
 /\ (forall m Γ e P,
        d_pat m Γ e P -> True).
Proof.
  apply d_typing_pat_mut; intros; try trivial.
  - (* d_typing__unit *)
    apply d_typing__sub with (A := typ_unit); auto using is_base_term__unit.
    apply d_typing__unit; auto.
  - (* d_typing__var: var's type [A] is read straight out of [Γ]
       (already a [syn]-painting by the context invariant), so no
       painting is applied at the rule. *)
    apply d_typing__sub with (A := A); auto using is_base_term__var.
    apply d_typing__var; auto.
  - (* d_typing__anno: rule conclusion is [syn_color A] for the [ctyp]
       base [A]; route through [d_typing__sub] at that target. *)
    apply d_typing__sub with (A := syn_color A); auto using is_base_term__anno.
    apply d_typing__anno; auto.
  - (* d_typing__sub: compose inner mode_ti sub with Hrefl via
       [d_consis_extends_d_sub_nil]. The inner [d_sub mode_ti nil] is
       now [d_sub__infer], which after inversion + subst pins both its
       indices to [syn_color] paintings; the mid type [M] is grabbed
       off the resulting [d_consis] by [match goal]. *)
    subst.
    apply d_typing__sub with (A := A); auto.
    match goal with
    | Hs : d_sub mode_ti nil _ _ _ |- _ =>
        inversion Hs; subst;
        try (match goal with H' : ?m0 <> ?m0 |- _ =>
               exfalso; apply H'; reflexivity end)
    end.
    match goal with
    | Hc : d_consis nil Γ _ ?M |- _ =>
        apply d_consis_extends_d_sub_nil with (A := M);
        [ exact Hc | assumption
        | eapply (proj1 d_typing_pat_preserves_wf); eauto ]
    end.
  - (* d_typing__freeze: rule produces mode_tc, contradicts m = mode_ti. *)
    discriminate.
  - (* d_typing__forall: rule produces mode_tc, contradicts m = mode_ti. *)
    discriminate.
  - (* d_typing__abs at outer m = mode_ti. The conclusion type is
       [typ_arrow (inh_color A) B] for the [ctyp] base [A]; the body
       binds [(x~typ syn_color A)]. Body's IH [H] provides the body
       lift at [decr_mode m_target], which is exactly what
       [d_sub_arrow_refl_inner] produces. *)
    subst.
    match goal with Hm : mono_typ (typ_arrow _ _) |- _ =>
      inversion Hm; subst
    end.
    apply d_typing__abs with (L := L `union` dom Γ); auto.
    intros x Hx. apply H; auto.
    + (* body context binds [syn_color A]; bridge from the rule's
         [d_wf_typ Γ (inh_color A)] via [d_wf_typ_inh_color_syn_color]. *)
      apply d_wf_denv__typ;
        [ assumption
        | fsetdec
        | apply d_wf_typ_inh_color_syn_color; assumption ].
    + (* d_sub (decr_mode m_target) nil ((x~typ syn_color A)++Γ) B B
         derived from Hrefl via d_sub_arrow_refl_inner + weakening. *)
      rewrite_env ((x ~ dbind_typ (syn_color A)) ++ Γ).
      apply d_sub_weakening_head.
      match goal with
      | Href : d_sub _ nil Γ (typ_arrow _ _) (typ_arrow _ _) |- _ =>
          apply (d_sub_arrow_refl_inner Href); assumption
      end.
  - (* d_typing__abs_anno: rule conclusion is [typ_arrow (syn_color A) B];
       body binds [(x~typ syn_color A)] (already the same colour as the
       wf premise). *)
    subst.
    match goal with Hm : mono_typ (typ_arrow _ _) |- _ =>
      inversion Hm; subst
    end.
    apply d_typing__abs_anno with (L := L `union` dom Γ); auto.
    intros x Hx. apply H; auto.
    + apply d_wf_denv__typ; [assumption | fsetdec | assumption].
    + rewrite_env ((x ~ dbind_typ (syn_color A)) ++ Γ).
      apply d_sub_weakening_head.
      match goal with
      | Href : d_sub _ nil Γ (typ_arrow _ _) (typ_arrow _ _) |- _ =>
          apply (d_sub_arrow_refl_inner Href); assumption
      end.
  - (* d_typing__app: research-grade gap (function's argument type mono
       not derivable from rule premises). Admit, same as D1's __app. *)
    admit.
Admitted.

(** Headline lemma: lift d_typing from mode_ti → any m_target at a fixed
    mono type. Derived from the mutual via [proj1]. *)
Lemma d_typing_lift_mono : forall Γ e A m_target,
    d_typing mode_ti Γ e A ->
    mono_typ A ->
    d_wf_denv Γ ->
    d_sub m_target nil Γ A A ->
    d_typing m_target Γ e A.
Proof.
  intros Γ e A m_target Hty Hmono Hwfd Hrefl.
  eapply (proj1 d_typing_lift_mono_mut); eauto.
Qed.
