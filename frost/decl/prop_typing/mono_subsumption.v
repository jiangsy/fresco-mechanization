(** Frost — declarative typing metatheory: mono-RHS rigidity for consistency
    and subtyping, [d_sub_gen] transitivity, and base-term gen-subsumption. *)

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
Require Import src.frost.decl.prop_subtyping.
Require Import src.frost.decl.prop_typing.weakening.
Require Import src.frost.decl.prop_typing.gen.

Set Implicit Arguments.

(** ** Mono-RHS rigidity for consistency / subtyping.

    If a [d_consis] / [d_sub] (or their generalised variants) has a
    [mono_typ] RHS, the LHS is forced equal to it: the polymorphic
    LHS rules all produce a non-mono ([typ_all_col] / quantified) RHS,
    so they are vacuous against [mono_typ B]; the [d_sub] [forall_l]
    rules (LHS [typ_all_etag] / [typ_all_plain]) are excluded by
    [d_wf_typ] on the LHS. Used in [d_sub_gen_trans]'s
    [Hsub_gen = __refl_mono] case: a mono target collapses the
    composition to reflexivity. *)
Lemma d_consis_mono_RHS_eq : forall Γ A B,
    d_consis nil Γ A B ->
    mono_typ B ->
    A = B.
Proof.
  intros Γ A B Hc.
  remember (@nil atom) as Δ_nil eqn:HeqΔ.
  induction Hc; intros Hmono; try discriminate HeqΔ.
  - reflexivity.
  - reflexivity.
  - (* __forall_syn_tagged: B = typ_all_col colour_syn — not mono. *)
    inversion Hmono.
  - (* __forall_syn (post-refactor): B = typ_all_col colour_syn — not mono. *)
    inversion Hmono.
  - (* __forall_inh: B = typ_all_col colour_inh — not mono. *)
    inversion Hmono.
  - apply app_eq_nil in HeqΔ. destruct HeqΔ as [HΔ1 HΔ2]. subst.
    inversion Hmono; subst.
    f_equal.
    + apply IHHc1; auto.
    + apply IHHc2; auto.
Qed.

Lemma d_consis_gen_mono_RHS_eq : forall Γ A B,
    d_consis_gen nil Γ A B ->
    mono_typ B ->
    A = B.
Proof.
  intros Γ A B Hc.
  remember (@nil atom) as Δ_nil eqn:HeqΔ.
  induction Hc; intros Hmono; try discriminate HeqΔ.
  - reflexivity.
  - reflexivity.
  - inversion Hmono.
  - inversion Hmono.
  - inversion Hmono.
  - apply app_eq_nil in HeqΔ. destruct HeqΔ as [HΔ1 HΔ2]. subst.
    inversion Hmono; subst.
    f_equal.
    + apply IHHc1; auto.
    + apply IHHc2; auto.
Qed.

Lemma d_sub_mono_RHS_eq : forall m Γ A B,
    d_sub m nil Γ A B ->
    d_wf_typ Γ A ->
    mono_typ B ->
    A = B.
Proof.
  intros m Γ A B Hs.
  remember (@nil atom) as Δ_nil eqn:HeqΔ.
  induction Hs; intros HwfA Hmono; try discriminate HeqΔ.
  - (* __infer: d_consis nil Γ T A. *)
    eapply d_consis_mono_RHS_eq; eauto.
  - (* __check: d_consis Δ Γ T A, Δ = nil. *)
    subst. eapply d_consis_mono_RHS_eq; eauto.
  - (* __forall_r: B = typ_all_col — not mono. *)
    inversion Hmono.
  - (* __arg: A = typ_arrow T1 T2, B = typ_arrow A1 A2. *)
    apply app_eq_nil in HeqΔ. destruct HeqΔ as [HΔ1 HΔ2]. subst.
    inversion HwfA; subst.
    inversion Hmono; subst.
    f_equal.
    + eapply d_consis_mono_RHS_eq; eauto.
    + apply IHHs; auto.
  - (* __forall_l_tagged: A = typ_all_etag — not wf. *)
    inversion HwfA.
Qed.

Lemma d_sub_gen_mono_RHS_eq : forall m Γ A B,
    d_sub_gen m nil Γ A B ->
    d_wf_typ Γ A ->
    mono_typ B ->
    A = B.
Proof.
  intros m Γ A B Hs.
  remember (@nil atom) as Δ_nil eqn:HeqΔ.
  induction Hs; intros HwfA Hmono; try discriminate HeqΔ.
  - (* __embed: d_sub m nil Γ A B. *)
    subst. eapply d_sub_mono_RHS_eq; eauto.
  - (* __infer_gen: d_consis_gen nil Γ A B + mono B. *)
    eapply d_consis_gen_mono_RHS_eq; eauto.
  - (* __check_gen: d_consis_gen Δ Γ A B (Δ = nil) + mono B. *)
    subst. eapply d_consis_gen_mono_RHS_eq; eauto.
  - (* __refl_mono: A = B. *)
    reflexivity.
  - (* __forall_r: B = typ_all_col — not mono. *)
    inversion Hmono.
  - (* __arg: A = typ_arrow T1 T2, B = typ_arrow A1 A2. *)
    apply app_eq_nil in HeqΔ. destruct HeqΔ as [HΔ1 HΔ2]. subst.
    inversion HwfA; subst.
    inversion Hmono; subst.
    f_equal.
    + eapply d_consis_gen_mono_RHS_eq; eauto.
    + apply IHHs; auto.
Qed.

(** [d_consis_gen_extends_d_sub_nil]: compose a [d_consis_gen] on the
    LHS of a [d_sub] (the non-generalised subtyping). By induction on
    the [d_sub] — crucially this gives IHs for the [__forall_r] /
    [__arg] sub-derivations, so those reconstruct cleanly. The
    [__infer]/[__check] cases chain via [d_consis_gen_trans] +
    [d_consis_gen__embed] and land in the new [d_sub_gen__infer_gen] /
    [__check_gen]; [__forall_l_*] are vacuous ([d_consis_gen] has no
    [typ_all_etag]/[typ_all_plain] RHS). *)
(* [d_consis_gen_RHS_syn_color_eq] moved up before
   [d_consis_extends_d_sub_gen_nil] which now uses it. *)

Lemma d_consis_gen_extends_d_sub_nil : forall m Γ B C,
    d_sub m nil Γ B C ->
    forall A,
      d_consis_gen nil Γ A B ->
      d_wf_typ Γ A ->
      d_sub_gen m nil Γ A C.
Proof.
  intros m Γ B C Hd.
  remember (@nil atom) as Δ_nil eqn:HeqΔ.
  induction Hd; intros A0 Hcg HwfA0.
  - (* __infer: B = syn_color T, C = syn_color A.
       [d_consis_gen_RHS_syn_color_eq] pins A0 = syn_color T;
       reuse [Hd]'s premise. *)
    assert (HeqA0 : A0 = syn_color _)
      by (eapply d_consis_gen_RHS_syn_color_eq; eauto); subst A0.
    apply d_sub_gen__infer_gen.
    eapply d_consis_gen_trans; [ exact Hcg | apply d_consis_gen__embed; eassumption ].
  - (* __check: B = syn_color T, C = inh_color A. Same chain. *)
    subst.
    assert (HeqA0 : A0 = syn_color _)
      by (eapply d_consis_gen_RHS_syn_color_eq; eauto); subst A0.
    apply d_sub_gen__check_gen; auto.
    eapply d_consis_gen_trans; [ exact Hcg | apply d_consis_gen__embed; eassumption ].
  - (* __forall_r: per-X recursion via the d_sub IH H0. *)
    subst.
    apply d_sub_gen__forall_r with (L := L `union` dom Γ).
    intros X HX.
    eapply H0; eauto.
    + apply d_consis_gen_weakening_head; auto.
    + apply d_wf_typ_weakening_head; auto.
  - (* __arg: B = typ_arrow T1 T2; Hcg forces A0 = typ_arrow A0_1 A0_2. *)
    apply app_eq_nil in HeqΔ. destruct HeqΔ as [HΔ1 HΔ2]. subst.
    inversion Hcg; subst.
    match goal with
    | H : _ ++ _ = nil |- _ =>
        apply app_eq_nil in H; destruct H as [HΔ1a HΔ2a]; subst
    end.
    inversion HwfA0; subst.
    rewrite_env (@nil atom ++ @nil atom).
    apply d_sub_gen__arg.
    + eapply d_consis_gen_trans;
        [ eassumption | apply d_consis_gen__embed; eassumption ].
    + eapply IHHd; eauto.
  - (* __forall_l_tagged: B = typ_all_etag — no d_consis_gen RHS. *)
    inversion Hcg.
Qed.

(** [d_consis_gen_extends_d_sub_gen_nil]: same, on the LHS of a
    [d_sub_gen]. By induction on [d_sub_gen]; [__embed] routes through
    [d_consis_gen_extends_d_sub_nil] (which handles the embedded
    [d_sub]'s internal structure), the gen rules chain via
    [d_consis_gen_trans], [__forall_r]/[__arg] recurse. *)
Lemma d_consis_gen_extends_d_sub_gen_nil : forall m Γ B C,
    d_sub_gen m nil Γ B C ->
    forall A,
      d_consis_gen nil Γ A B ->
      d_wf_typ Γ A ->
      d_sub_gen m nil Γ A C.
Proof.
  intros m Γ B C Hs.
  remember (@nil atom) as Δ_nil eqn:HeqΔ.
  induction Hs; intros A0 Hcg HwfA0.
  - (* __embed *)
    subst. eapply d_consis_gen_extends_d_sub_nil; eauto.
  - (* __infer_gen: B = syn_color T, C = syn_color A. *)
    assert (HeqA0 : A0 = syn_color _)
      by (eapply d_consis_gen_RHS_syn_color_eq; eauto); subst A0.
    apply d_sub_gen__infer_gen.
    eapply d_consis_gen_trans; eauto.
  - (* __check_gen: B = syn_color T, C = inh_color A. *)
    subst.
    assert (HeqA0 : A0 = syn_color _)
      by (eapply d_consis_gen_RHS_syn_color_eq; eauto); subst A0.
    apply d_sub_gen__check_gen.
    + assumption.
    + eapply d_consis_gen_trans; eauto.
  - (* __refl_mono: B = C mono ⟹ A0 = B by mono-RHS rigidity. *)
    subst.
    assert (Heq : A0 = A) by (eapply d_consis_gen_mono_RHS_eq; eauto).
    subst. apply d_sub_gen__refl_mono; auto.
  - (* __forall_r: per-X recursion via IH H0. *)
    subst.
    apply d_sub_gen__forall_r with (L := L `union` dom Γ).
    intros X HX.
    eapply H0; eauto.
    + apply d_consis_gen_weakening_head; auto.
    + apply d_wf_typ_weakening_head; auto.
  - (* __arg: B = typ_arrow B1 B2; Hcg forces A0 = typ_arrow A0_1 A0_2. *)
    apply app_eq_nil in HeqΔ. destruct HeqΔ as [HΔ1 HΔ2]. subst.
    inversion Hcg; subst.
    match goal with
    | H : _ ++ _ = nil |- _ =>
        apply app_eq_nil in H; destruct H as [HΔ1a HΔ2a]; subst
    end.
    inversion HwfA0; subst.
    rewrite_env (@nil atom ++ @nil atom).
    apply d_sub_gen__arg.
    + eapply d_consis_gen_trans; eauto.
    + eapply IHHs; eauto.
Qed.

(** [d_sub_gen_trans_arrow]: the arrow-shaped continuation shared by
    [d_sub_gen_trans]'s [Hso = __embed] and [Hso = __arg] cases. Both
    yield [A = typ_arrow A1 A2], [B = typ_arrow B1 B2] with arg-side
    [d_consis_gen] and ret-side [d_sub_gen]; this lemma dispatches on
    the second derivation [Hsg]:
    - [Hsg = __embed]/[__arg]: reconstruct [d_sub_gen__arg], composing
      the arg sides via [d_consis_gen_trans] and the ret sides via the
      passed-in IH.
    - [Hsg = __refl_mono]: the target [typ_arrow B1 B2] is mono, so
      [d_sub_gen_mono_RHS_eq] collapses [typ_arrow A1 A2 = typ_arrow
      B1 B2] and the result is reflexivity. *)
Lemma d_sub_gen_trans_arrow : forall m m_new Γ A1 A2 B1 B2 C,
    d_wf_typ Γ A1 ->
    d_wf_typ Γ A2 ->
    d_consis_gen nil Γ A1 B1 ->
    d_sub_gen m nil Γ A2 B2 ->
    d_sub_gen (mode_fn (mode_fn_n_subst m m_new)) nil Γ (typ_arrow B1 B2) C ->
    (forall Γ' A' B' C',
       d_wf_typ Γ' A' ->
       d_sub_gen m nil Γ' A' B' ->
       d_sub_gen (mode_fn_n_subst m m_new) nil Γ' B' C' ->
       d_sub_gen (mode_fn_n_subst m m_new) nil Γ' A' C') ->
    d_sub_gen (mode_fn (mode_fn_n_subst m m_new)) nil Γ (typ_arrow A1 A2) C.
Proof.
  intros m m_new Γ A1 A2 B1 B2 C HwfA1 HwfA2 Hca_gen Hsa_gen Hsg IH.
  inversion Hsg; subst.
  - (* __embed: d_sub _ nil Γ (typ_arrow B1 B2) C → __arg. *)
    match goal with H : d_sub _ nil Γ (typ_arrow B1 B2) _ |- _ =>
      inversion H; subst
    end.
    match goal with
    | H : _ ++ _ = nil |- _ =>
        apply app_eq_nil in H; destruct H as [HΔ1 HΔ2]; subst
    end.
    rewrite_env (@nil atom ++ @nil atom).
    apply d_sub_gen__arg.
    + eapply d_consis_gen_trans;
        [ exact Hca_gen | apply d_consis_gen__embed; eassumption ].
    + eapply IH;
        [ exact HwfA2 | exact Hsa_gen | apply d_sub_gen__embed; eassumption ].
  - (* __refl_mono: typ_arrow B1 B2 = C, mono. *)
    assert (Harrow : d_sub_gen (mode_fn m) nil Γ (typ_arrow A1 A2) (typ_arrow B1 B2)).
    { rewrite_env (@nil atom ++ @nil atom).
      apply d_sub_gen__arg; assumption. }
    assert (Heq : typ_arrow A1 A2 = typ_arrow B1 B2).
    { eapply d_sub_gen_mono_RHS_eq;
        [ exact Harrow | apply d_wf_typ__arrow; assumption | eassumption ]. }
    rewrite Heq.
    apply d_sub_gen__refl_mono; assumption.
  - (* __arg: C = typ_arrow C1 C2, gen sub-derivations directly. *)
    match goal with
    | H : _ ++ _ = nil |- _ =>
        apply app_eq_nil in H; destruct H as [HΔ1 HΔ2]; subst
    end.
    rewrite_env (@nil atom ++ @nil atom).
    apply d_sub_gen__arg.
    + eapply d_consis_gen_trans; [ exact Hca_gen | eassumption ].
    + eapply IH; [ exact HwfA2 | exact Hsa_gen | eassumption ].
Qed.

(** [d_sub_gen_trans]: transitivity of [d_sub_gen] along the FN^n
    mode-stack. With [m1] in [is_fn_n_ti] form and the second
    derivation at [mode_fn_n_subst m1 m_new] (the innermost TI
    replaced by [m_new]), the composite lives at the second mode.

    Induction on [is_fn_n_ti m1]:
    - [m1 = mode_ti]: the first sub is [__infer] (compose via
      [d_consis_extends_d_sub_gen_nil]) or [__refl_mono] (identity).
    - [m1 = mode_fn m]: the first sub is [__refl_mono] (identity) or
      arrow-shaped ([__embed]→[d_sub__arg], or [__arg]); the arrow
      cases route through [d_sub_gen_trans_arrow] with the IH.

    This closes the D12 [__sub] [m = mode_fn _] case (mode-changing
    subtyping transitivity). *)
Lemma d_sub_gen_trans : forall m1 Γ A B C m_new,
    is_fn_n_ti m1 ->
    d_wf_typ Γ A ->
    d_sub_gen m1 nil Γ A B ->
    d_sub_gen (mode_fn_n_subst m1 m_new) nil Γ B C ->
    d_sub_gen (mode_fn_n_subst m1 m_new) nil Γ A C.
Proof.
  intros m1 Γ A B C m_new Hfn.
  generalize dependent C. generalize dependent B.
  generalize dependent A. generalize dependent Γ.
  induction Hfn; intros Γ A B C HwfA Hso Hsg.
  - (* m1 = mode_ti: mode_fn_n_subst mode_ti m_new = m_new. *)
    simpl in Hsg |- *.
    inversion Hso; subst.
    + (* __embed: d_sub mode_ti nil Γ A B. Only __infer applies;
         the forall_l rules carry [m <> mode_ti], contradictory here. *)
      match goal with H : d_sub mode_ti nil Γ _ _ |- _ =>
        inversion H
      end; subst; try (exfalso; congruence).
      eapply d_consis_extends_d_sub_gen_nil; eauto.
    + (* __infer_gen: d_consis_gen nil Γ A B; compose with Hsg via
         the d_consis_gen-LHS extension lemma. *)
      eapply d_consis_gen_extends_d_sub_gen_nil; eauto.
    + (* __refl_mono: A = B. *)
      exact Hsg.
  - (* m1 = mode_fn m: mode_fn_n_subst (mode_fn m) m_new
       = mode_fn (mode_fn_n_subst m m_new). *)
    simpl in Hsg |- *.
    inversion Hso; subst.
    + (* __embed: d_sub (mode_fn m) nil Γ A B. A wf ⟹ only __arg. *)
      match goal with H : d_sub (mode_fn m) nil Γ _ _ |- _ =>
        inversion H; subst
      end.
      * (* d_sub__arg *)
        match goal with
        | H : _ ++ _ = nil |- _ =>
            apply app_eq_nil in H; destruct H as [HΔ1 HΔ2]; subst
        end.
        inversion HwfA; subst.
        eapply d_sub_gen_trans_arrow;
          [ eassumption | eassumption
          | apply d_consis_gen__embed; eassumption
          | apply d_sub_gen__embed; eassumption
          | exact Hsg | exact IHHfn ].
      * (* d_sub__forall_l_tagged: A = typ_all_etag — not wf. *)
        inversion HwfA.
    + (* __refl_mono: A = B. *)
      exact Hsg.
    + (* __arg: gen sub-derivations directly. *)
      match goal with
      | H : _ ++ _ = nil |- _ =>
          apply app_eq_nil in H; destruct H as [HΔ1 HΔ2]; subst
      end.
      inversion HwfA; subst.
      eapply d_sub_gen_trans_arrow;
        [ eassumption | eassumption | eassumption | eassumption
        | exact Hsg | exact IHHfn ].
Qed.

(** [d_sub_gen] analogue of [d_sub_arrow_refl_inner]: a reflexive
    [d_sub_gen] on a mono arrow type yields a reflexive [d_sub_gen] on
    the result type at [decr_mode]. The [__embed] case routes through
    [d_sub_arrow_refl_inner]; [__refl_mono] rebuilds via
    [d_sub_gen__refl_mono] (mode-compat / wf from inverting the arrow
    premises); [__arg] hands back its ret-side directly. *)
Lemma d_sub_gen_arrow_refl_inner : forall Γ A B m,
    d_sub_gen m nil Γ (typ_arrow A B) (typ_arrow A B) ->
    mono_typ A ->
    mono_typ B ->
    d_sub_gen (decr_mode m) nil Γ B B.
Proof.
  intros Γ A B m Hrefl HmonoA HmonoB.
  assert (Hwf_arr : d_wf_typ Γ (typ_arrow A B))
    by (eapply d_sub_gen_preserves_wf; eauto).
  inversion Hwf_arr; subst.
  inversion Hrefl; subst.
  - (* __embed: route through [d_sub_arrow_refl_inner]. *)
    apply d_sub_gen__embed. eapply d_sub_arrow_refl_inner; eauto.
  - (* __infer_gen: m = mode_ti. Build [__refl_mono] on B with
       [is_syn_typ B] from mono. *)
    simpl.
    apply d_sub_gen__refl_mono; auto.
    apply mode_typ_compat__ti. apply mono_typ_is_syn_typ; auto.
  - (* __check_gen: m = mode_tc. Same with [is_inh_typ B]. *)
    simpl.
    apply d_sub_gen__refl_mono; auto.
    apply mode_typ_compat__tc. apply mono_typ_is_inh_typ; auto.
  - (* __refl_mono: invert [mode_typ_compat m (typ_arrow A B)] to
       extract compat at [decr_mode m] on B. *)
    apply d_sub_gen__refl_mono; auto.
    match goal with
    | H : mode_typ_compat _ (typ_arrow _ _) |- _ =>
        inversion H; subst; simpl;
          [ apply mode_typ_compat__ti;
            match goal with Hsy : is_syn_typ (typ_arrow _ _) |- _ =>
              inversion Hsy; assumption
            end
          | apply mode_typ_compat__tc;
            match goal with Hih : is_inh_typ (typ_arrow _ _) |- _ =>
              inversion Hih; assumption
            end
          | assumption ]
    end.
  - (* __arg: m = mode_fn k, body sub gives the result directly. *)
    match goal with
    | H : _ ++ _ = nil |- _ =>
        apply app_eq_nil in H; destruct H as [HΔ1 HΔ2]; subst
    end.
    simpl. assumption.
Qed.

(** Mono-type mode-lift for [d_typing_gen] — the [d_typing_gen]
    analogue of [d_typing_lift_mono]. By induction on the typing.
    Base terms close via [d_typing_gen__sub]; [__sub] composes the
    inner mode_ti d_sub_gen with Hrefl via [d_sub_gen_trans];
    [__abs]/[__abs_anno] reconstruct with body lifted by the IH and
    [d_sub_gen_arrow_refl_inner]; [__app] is research-grade
    (same gap as [d_typing_lift_mono]'s [__app] — function arg-type
    mono not derivable from the rule). *)
Lemma d_typing_gen_lift_mono : forall Γ e A m_target,
    d_typing_gen mode_ti Γ e A ->
    mono_typ A ->
    d_wf_denv Γ ->
    d_sub_gen m_target nil Γ A A ->
    d_typing_gen m_target Γ e A.
Proof.
  intros Γ e A m_target H.
  remember mode_ti as m0 eqn:Hm0.
  generalize dependent m_target.
  induction H; intros m_target Hmono Hwfd Hrefl.
  - (* __unit *)
    apply d_typing_gen__sub with (A := typ_unit); auto using is_base_term__unit.
    apply d_typing_gen__unit; auto.
  - (* __var *)
    apply d_typing_gen__sub with (A := A); auto using is_base_term__var.
    apply d_typing_gen__var; auto.
  - (* __anno: rule conclusion is [syn_color A]; route through
       [d_typing_gen__sub] at that target. *)
    apply d_typing_gen__sub with (A := syn_color A);
      auto using is_base_term__anno.
    apply d_typing_gen__anno; auto.
  - (* __sub: m = mode_ti (in context), inner mode_ti at A, sub
       d_sub_gen mode_ti A B. Compose with Hrefl (d_sub_gen m_target B B)
       via d_sub_gen_trans at m1 = mode_ti. *)
    subst.
    apply d_typing_gen__sub with (A := A); auto.
    eapply d_sub_gen_trans with (m1 := mode_ti) (B := B).
    + apply is_fn_n_ti__ti.
    + eapply d_typing_gen_preserves_wf; eauto.
    + exact H1.
    + exact Hrefl.
  - (* __freeze: produces mode_tc, contradicts m0 = mode_ti. *)
    discriminate.
  - (* __forall: produces mode_tc, contradicts. *)
    discriminate.
  - (* __abs at outer m = mode_ti. Conclusion: typ_arrow (inh_color A) B.
       Mono ⇒ both arms mono. Body lifts via IH H1 with body refl from
       [d_sub_gen_arrow_refl_inner] + weakening. *)
    subst.
    inversion Hmono; subst.
    apply d_typing_gen__abs with (L := L `union` dom Γ); auto.
    intros x Hx. apply H1; auto.
    + apply d_wf_denv__typ;
        [ assumption | fsetdec
        | apply d_wf_typ_inh_color_syn_color; assumption ].
    + rewrite_env ((x ~ dbind_typ (syn_color A)) ++ Γ).
      apply d_sub_gen_weakening_head.
      eapply d_sub_gen_arrow_refl_inner; eauto.
  - (* __abs_anno: conclusion typ_arrow (syn_color A) B; body binding is
       (x ~ dbind_typ (syn_color A)) — same colour, identity. *)
    subst.
    inversion Hmono; subst.
    apply d_typing_gen__abs_anno with (L := L `union` dom Γ); auto.
    intros x Hx. apply H1; auto.
    + apply d_wf_denv__typ; [assumption | fsetdec | assumption].
    + rewrite_env ((x ~ dbind_typ (syn_color A)) ++ Γ).
      apply d_sub_gen_weakening_head.
      eapply d_sub_gen_arrow_refl_inner; eauto.
  - (* __app: CONCRETE OBSTRUCTION (2026-05-16 discovery).

       Lift requires function-side mode shift: from
         H1 : d_typing_gen (mode_fn mode_ti) Γ e1 (typ_arrow P' B)
       produce
         d_typing_gen (mode_fn m_target) Γ e1 (typ_arrow P' B).

       The reconstruction via __sub would need
         d_sub_gen (mode_fn m_target) nil Γ A0 (typ_arrow P' B)
       for the same A0 used in the original __sub. The three rules of
       d_sub_gen at mode_fn _:
       - __refl_mono : requires typ_arrow P' B mono, i.e., P' mono.
         FAILS for P' = typ_all_col colour_syn _ (from d_refine_syn__hole
         with an is_syn_skel polytype Q — a valid refinement output).
       - __arg : requires d_consis_gen Δ1 Γ A0_arg P'. The d_consis_gen
         refl on P' via [d_consis_gen_refl] requires [is_inh_typ P'],
         which FAILS for typ_all_col colour_syn (only colour_inh quantifier
         heads satisfy is_inh_typ__all).
       - __embed via d_sub : same constraint via d_sub__arg → d_consis.

       CONCRETE WITNESS: P = ctyp_hole; P' = typ_all_col colour_syn
       (typ_arrow typ_unit typ_unit) (polytype); B = typ_unit (mono).
       Original derivation EXISTS (e.g., via __abs_anno with syn-painted
       binding). LIFT via these rules FAILS.

       This is NOT a counter-example to the typing's lift property — the
       property holds semantically — but it IS a concrete obstruction in
       the d_sub_gen / d_consis_gen rule set. The fix requires one of:
       (a) Add d_consis_gen__forall_syn rule (mirror of __forall_inh) for
           typ_all_col colour_syn LHS — paper-aligned.
       (b) Restrict d_refine_syn__hole to is_inh_typ outputs (rule
           strengthening with cascading impact).
       (c) Joint mutual induction over D12 + lift_mono with multiple
           invariants (paper appendix B.5 approach, ~500+ line refactor). *)
    admit.
Admitted.

(** Aux lemmas specialising the gen-subsumption theorem to specific
    Hty constructors. *)

(** With [d_typing_gen], the base-term subsumption helpers are trivial:
    [d_typing_gen__sub] takes the [d_sub_gen] directly, so no induction
    on the subtyping derivation and no gen→sub bridge are needed. This
    is exactly the structural payoff of mirroring the paper's
    syntax-directed [Sub] rule (which uses the generalised subtyping). *)
Lemma d_typing_unit_gen_subsumption : forall Γ A m,
    d_wf_denv Γ ->
    d_sub_gen m nil Γ typ_unit A ->
    d_typing_gen m Γ exp_unit A.
Proof.
  intros Γ A m Hwfd Hs.
  apply d_typing_gen__sub with (A := typ_unit).
  - apply is_base_term__unit.
  - apply d_typing_gen__unit. apply mode_typ_compat__ti.
    apply is_syn_typ__unit.
  - exact Hs.
Qed.

(** Post-re-encoding: [d_typing_gen__var] returns the bound type raw,
    so the gen-subsumption helper for variables takes the [d_sub_gen]
    on [Avar] directly (no [syn_color_t] wrap). *)
Lemma d_typing_var_gen_subsumption : forall Γ xv Avar A m,
    d_wf_denv Γ ->
    binds xv (dbind_typ Avar) Γ ->
    d_sub_gen m nil Γ Avar A ->
    d_typing_gen m Γ (exp_var_f xv) A.
Proof.
  intros Γ xv Avar A m Hwfd Hb Hs.
  apply d_typing_gen__sub with (A := Avar).
  - apply is_base_term__var.
  - apply d_typing_gen__var; exact Hb.
  - exact Hs.
Qed.

(** [d_typing_anno_gen_subsumption]: subsume an annotated check-mode
    typing across a [d_sub_gen]. Post-re-encoding the helper is
    naturally stated over a [ctyp] base [C] (matching the
    [d_typing_gen__anno] rule shape): the inner check is at
    [inh_color C], the synthesised result is at [syn_color C], and the
    outer [d_sub_gen] subsumes the [syn_color C] conclusion to any [A].
    The old [typ]-domain statement (`Aann : typ` with [is_inh_typ Aann]
    plus a [d_sub_gen] from [Aann] to [A]) is unprovable post-re-encoding:
    the rule produces [syn_color C] not [Aann], so the d_sub_gen
    composition no longer lines up. *)
Lemma d_typing_anno_gen_subsumption : forall Γ e0 C A m,
    d_wf_denv Γ ->
    d_typing_gen mode_tc Γ e0 (inh_color C) ->
    d_sub_gen m nil Γ (syn_color C) A ->
    d_typing_gen m Γ (exp_anno e0 (inh_color C)) A.
Proof.
  intros Γ e0 C A m Hwfd Hinner Hs.
  apply d_typing_gen__sub with (A := syn_color C).
  - apply is_base_term__anno.
  - apply d_typing_gen__anno; assumption.
  - exact Hs.
Qed.

(** Mono-extraction helpers (used in __check_gen closure). *)

Lemma is_inh_typ_syn_color_mono_pre : forall A C,
    is_inh_typ A ->
    A = syn_color C ->
    mono_typ A.
Proof.
  intros A C Hinh. revert C. induction Hinh; intros C HC.
  - apply mono_typ__unit.
  - apply mono_typ__var.
  - destruct C; simpl in HC; inversion HC; subst.
    apply mono_typ__arrow.
    + eapply IHHinh1; reflexivity.
    + eapply IHHinh2; reflexivity.
  - destruct C; simpl in HC; discriminate.
Qed.

(** [d_consis_syn_inh_mono]: when d_consis has a syn-painted LHS and an
    inh-painted RHS, the LHS must be mono.

    Proof by induction on d_consis. The new __forall_syn rule is vacuous
    in this context because its RHS shape (typ_all_col colour_syn) cannot
    equal an inh_color painting (inh_color paints colour_inh exclusively).
    The other forall cases (tagged / colour_inh LHS) are vacuous via
    syn_color injectivity (syn_color never produces typ_all_etag or
    typ_all_col colour_inh). Unit/var/arrow recurse structurally. *)
Lemma d_consis_syn_inh_mono : forall Γ Δ T A,
    d_consis Δ Γ (syn_color T) (inh_color A) ->
    mono_typ (syn_color T).
Proof.
  intros Γ Δ T A H.
  remember (syn_color T) as A_lhs eqn:HeqLHS.
  remember (inh_color A) as A_rhs eqn:HeqRHS.
  revert T A HeqLHS HeqRHS.
  induction H; intros T0 A0 HeqLHS HeqRHS.
  - (* __unit *) apply mono_typ__unit.
  - (* __var *) destruct T0; simpl in HeqLHS; try discriminate.
    inversion HeqLHS; subst. apply mono_typ__var.
  - (* __forall_inh_tagged: LHS typ_all_etag — syn_color never paints etag. *)
    destruct T0; simpl in HeqLHS; discriminate.
  - (* __forall_syn_tagged: LHS typ_all_etag — vacuous as above. *)
    destruct T0; simpl in HeqLHS; discriminate.
  - (* __forall_syn (post-refactor): LHS = typ_all_col colour_syn = syn_color
       (ctyp_all _). RHS = typ_all_col colour_syn — but inh_color paints
       colour_inh, never colour_syn. Vacuous via HeqRHS inversion. *)
    destruct A0; simpl in HeqRHS; discriminate.
  - (* __forall_inh: LHS = typ_all_col colour_inh — syn_color never paints
       colour_inh. Vacuous via HeqLHS. *)
    destruct T0; simpl in HeqLHS; try discriminate.
  - (* __arrow *)
    destruct T0; simpl in HeqLHS; try discriminate.
    destruct A0; simpl in HeqRHS; try discriminate.
    inversion HeqLHS; inversion HeqRHS; subst.
    apply mono_typ__arrow.
    + eapply IHd_consis1; reflexivity.
    + eapply IHd_consis2; reflexivity.
Qed.

(** [d_consis_gen_syn_inh_mono]: d_consis_gen analogue. Same structure as
    [d_consis_syn_inh_mono]; the new [__forall_syn] rule in [d_consis_gen]
    is vacuous for the same reason (RHS colour mismatch with inh_color). *)
Lemma d_consis_gen_syn_inh_mono : forall Γ Δ T A,
    d_consis_gen Δ Γ (syn_color T) (inh_color A) ->
    mono_typ (syn_color T).
Proof.
  intros Γ Δ T A H.
  remember (syn_color T) as A_lhs eqn:HeqLHS.
  remember (inh_color A) as A_rhs eqn:HeqRHS.
  revert T A HeqLHS HeqRHS.
  induction H; intros T0 A0 HeqLHS HeqRHS.
  - apply mono_typ__unit.
  - destruct T0; simpl in HeqLHS; try discriminate.
    inversion HeqLHS; subst. apply mono_typ__var.
  - destruct T0; simpl in HeqLHS; discriminate.
  - destruct T0; simpl in HeqLHS; discriminate.
  - destruct A0; simpl in HeqRHS; discriminate.
  - destruct T0; simpl in HeqLHS; try discriminate.
  - destruct T0; simpl in HeqLHS; try discriminate.
    destruct A0; simpl in HeqRHS; try discriminate.
    inversion HeqLHS; inversion HeqRHS; subst.
    apply mono_typ__arrow.
    + eapply IHd_consis_gen1; reflexivity.
    + eapply IHd_consis_gen2; reflexivity.
Qed.
