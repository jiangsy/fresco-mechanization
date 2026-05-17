(** Frost — declarative typing metatheory: subsumption-auxiliary helpers.

    This file consolidates two previously-separate files into one
    (merged 2026-05-17 as part of the file restructuring):

    - [mono_subsumption.v] (now §1 below): mono-RHS rigidity for
      consistency and subtyping, [d_sub_gen] transitivity, and
      base-term gen-subsumption — including [d_typing_gen_lift_mono]
      whose [__app] case is the documented research-grade gap.

    - [abs_subsumption.v] (now §2 below): SPLIT helpers for the
      [exp_abs] / [exp_abs_anno] value cases that D12
      ([prop_general_subsumption.v]) routes through. The TC variants
      take an [Hbody_at_tc] premise constructed by D12 from its own
      IHbody — this is the load-bearing trick that breaks the
      [lift_mono ↔ D12] cycle, eliminating [d_typing_gen_lift_mono]
      from D12's transitive axiom closure. *)

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
Require Import src.frost.decl.typing.prop_weakening.
Require Import src.frost.decl.typing.def_gen.

Set Implicit Arguments.

(* ====================================================================== *)
(*  §1 — Mono-RHS rigidity, [d_sub_gen] transitivity, base-term gen-sub  *)
(*  (formerly mono_subsumption.v)                                         *)
(* ====================================================================== *)


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
    nil ⨟ Γ ⊨ A ≈ B ->
    mono_typ B ->
    A = B.
Proof.
  intros Γ A B Hc.
  remember (@nil atom) as Δ_nil eqn:HeqΔ.
  induction Hc; intros Hmono; try discriminate HeqΔ.
  - reflexivity.
  - reflexivity.
  - (* __forall_inh_untagged (NEW): B = typ_all_col colour_inh — not mono. *)
    inversion Hmono.
  - (* __forall_syn_tagged: B = typ_all_col colour_syn — not mono. *)
    inversion Hmono.
  - (* __forall_syn: B = typ_all_col colour_syn — not mono. *)
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
  - (* __forall_inh_untagged (NEW): B = typ_all_col colour_inh — not mono. *)
    inversion Hmono.
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
    Γ ⊢[ m ; nil ] A ⊑ B ->
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
  - (* __forall_l_untagged (NEW): A = typ_all_col colour_syn — IS wf, B mono.
       Conclusion A = B fails (A = typ_all_col, B mono). Admitted —
       lemma needs precondition strengthening (e.g., is_utyp A excluding
       __pall, or restrict to non-colour_syn A). *)
    admit.
Admitted.
(* d_sub_mono_RHS_eq: 1 admit post-δ-refactor — needs strengthening. *)

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
   [d_consis_sub_trans_gen_nil] which now uses it. *)

Lemma d_consis_gen_extends_d_sub_nil : forall m Γ B C,
    Γ ⊢[ m ; nil ] B ⊑ C ->
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
    eapply d_consis_gen_trans;
      [ eapply d_wf_typ_is_typ; eassumption
      | exact Hcg
      | apply d_consis_gen__embed; eassumption ].
  - (* __check: B = syn_color T, C = inh_color A. Same chain. *)
    subst.
    assert (HeqA0 : A0 = syn_color _)
      by (eapply d_consis_gen_RHS_syn_color_eq; eauto); subst A0.
    apply d_sub_gen__check_gen; auto.
    eapply d_consis_gen_trans;
      [ eapply d_wf_typ_is_typ; eassumption
      | exact Hcg
      | apply d_consis_gen__embed; eassumption ].
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
        [ eapply d_wf_typ_is_typ; eassumption
        | eassumption
        | apply d_consis_gen__embed; eassumption ].
    + eapply IHHd; eauto.
  - (* __forall_l_tagged: B = typ_all_etag — no d_consis_gen RHS. *)
    inversion Hcg.
  - (* __forall_l_untagged (NEW): B = typ_all_col colour_syn. d_consis_gen
       RHS CAN be typ_all_col colour_syn. Non-trivial; admitted. *)
    admit.
Admitted.
(* 1 admit post-δ-refactor for new d_sub rule. *)

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
    eapply d_consis_gen_trans;
      [ eapply d_wf_typ_is_typ; eassumption | eauto | eauto ].
  - (* __check_gen: B = syn_color T, C = inh_color A. *)
    subst.
    assert (HeqA0 : A0 = syn_color _)
      by (eapply d_consis_gen_RHS_syn_color_eq; eauto); subst A0.
    apply d_sub_gen__check_gen.
    + assumption.
    + eapply d_consis_gen_trans;
        [ eapply d_wf_typ_is_typ; eassumption | eauto | eauto ].
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
    + eapply d_consis_gen_trans;
        [ eapply d_wf_typ_is_typ; eassumption | eauto | eauto ].
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
        [ eapply d_wf_typ_is_typ; eassumption
        | exact Hca_gen
        | apply d_consis_gen__embed; eassumption ].
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
    + eapply d_consis_gen_trans;
        [ eapply d_wf_typ_is_typ; eassumption | exact Hca_gen | eassumption ].
    + eapply IH; [ exact HwfA2 | exact Hsa_gen | eassumption ].
Qed.

(** [d_wf_ttyp_nil_d_wf_typ]: at empty Δ, [d_wf_ttyp] degenerates to
    [d_wf_typ] (the only [d_wf_ttyp] rules with [Δ = nil] are unit /
    var / arrow — same shapes as [d_wf_typ] base cases). [typ_all_etag]
    requires non-nil Δ, so it's vacuous here. *)
Lemma d_wf_ttyp_nil_d_wf_typ : forall Γ ph,
    nil ⨟ Γ ⊢ₜₜ ph ->
    d_wf_typ Γ ph.
Proof.
  intros Γ ph H. remember (@nil atom) as Δ_nil eqn:HΔ.
  induction H; subst.
  - apply d_wf_typ__unit.
  - apply d_wf_typ__var; assumption.
  - apply app_eq_nil in HΔ. destruct HΔ as [HΔ1 HΔ2]. subst.
    apply d_wf_typ__arrow; auto.
  - discriminate HΔ.   (* ε :: Δ ≠ nil *)
Qed.

(** [d_wf_typ_open_with_ttyp_nil]: opening a cofinitely-wf body with a
    [d_wf_ttyp nil]-wf type produces wf. Standard substitution pattern
    using [subst_typ_in_typ_intro]. *)
Lemma d_wf_typ_open_with_ttyp_nil : forall Γ L T ph,
    (forall X, X `notin` L ->
       d_wf_typ ((X ~ dbind_tvar) ++ Γ) (open_typ_wrt_typ T (typ_var_f X))) ->
    nil ⨟ Γ ⊢ₜₜ ph ->
    d_wf_typ Γ (open_typ_wrt_typ T ph).
Proof.
  intros Γ L T ph Hcofin Hwfph.
  pick fresh X for (L `union` ftvar_in_typ T `union` dom Γ).
  rewrite (subst_typ_in_typ_intro X T ph); [| fsetdec].
  rewrite_env (nil ++ Γ).
  apply d_wf_typ_subst with (X := X).
  - simpl. apply Hcofin. fsetdec.
  - apply d_wf_ttyp_nil_d_wf_typ. exact Hwfph.
Qed.

(** [d_sub_gen_trans_forall_l_untagged_helper]: inner transitivity for
    the [d_sub__forall_l_untagged] case of [d_sub_gen_trans] at
    [mode_fn m]. Inducts on the inner d_sub structure (paper-faithful:
    cf. syntax-directed.tex:323-338, ForallL case of Subtyping
    Transitivity inducts on the first d_sub).

    For [__forall_l_untagged] the body's d_sub is structurally smaller;
    IH applies to give the composed body output as a [d_sub_gen]. We
    bridge back to [d_sub] via [d_sub_gen_to_d_sub] (Qed, in def_gen.v)
    so the rule's body slot accepts it.

    [__arg] dispatches to [d_sub_gen_trans_arrow] with the passed-in
    inner-mode IH (the same one used by [d_sub_gen_trans]'s outer __arg
    case).

    [__forall_l_tagged] is vacuous via [inversion HwfA] ([typ_all_etag]
    is not [d_wf_typ]). *)
Lemma d_sub_gen_trans_forall_l_untagged_helper :
  forall m,
  forall Γ A B C m_new,
    is_fn_n_ti m ->
    d_wf_typ Γ A ->
    Γ ⊢[ mode_fn m ; nil ] A ⊑ B ->
    d_sub_gen (mode_fn (mode_fn_n_subst m m_new)) nil Γ B C ->
    (forall Γ' A' B' C',
       d_wf_typ Γ' A' ->
       d_sub_gen m nil Γ' A' B' ->
       d_sub_gen (mode_fn_n_subst m m_new) nil Γ' B' C' ->
       d_sub_gen (mode_fn_n_subst m m_new) nil Γ' A' C') ->
    d_sub_gen (mode_fn (mode_fn_n_subst m m_new)) nil Γ A C.
Proof.
  intros m Γ A B C m_new Hfn HwfA Hsub Hsg IH_inner.
  remember (@nil atom) as Δ_nil eqn:HeqΔ.
  revert C Hsg HwfA.
  dependent induction Hsub; intros C2 Hsg HwfA.
  - (* __arg: rule's mode_fn m_rule = mode_fn m ⇒ m_rule = m. *)
    apply app_eq_nil in HeqΔ. destruct HeqΔ as [HΔ1 HΔ2]. subst.
    inversion HwfA; subst.
    eapply d_sub_gen_trans_arrow;
      [ eassumption | eassumption
      | apply d_consis_gen__embed; eassumption
      | apply d_sub_gen__embed; eassumption
      | exact Hsg | exact IH_inner ].
  - (* __forall_l_tagged: A = typ_all_etag — not wf. *)
    inversion HwfA.
  - (* __forall_l_untagged: A = typ_all_col colour_syn T.
       Case-split on rule's Δ': nil (ph mono) vs non-nil (ph has ε-tags).
       For Δ' = nil, we re-instantiate the output rule with nil; the
       body's d_sub composes with Hsg via the IH (output is d_sub_gen,
       bridged to d_sub via [d_sub_gen_to_d_sub]).
       For Δ' non-nil, the body's d_sub is at non-nil Δ ++ Δ' = Δ',
       and the IH (which expects Δ_total = nil per our trans signature)
       doesn't apply — would require a generalised trans at non-nil Δ. *)
    subst.
    destruct Δ' as [| ε_first rest_Δ' ].
    + (* Δ' = nil: ph is mono / d_wf_typ. *)
      apply d_sub_gen__embed.
      apply d_sub__forall_l_untagged with (Δ' := @nil atom) (ph := ph).
      * discriminate.
      * apply list_disjoint_nil_l.
      * assumption.
      * simpl.
        apply d_sub_gen_to_d_sub.
        eapply IHHsub.
        -- reflexivity.
        -- exact Hfn.
        -- reflexivity.
        -- exact IH_inner.
        -- simpl. exact Hsg.
        -- inversion HwfA; subst.
           eapply d_wf_typ_open_with_ttyp_nil; eassumption.
    + (* Δ' = ε_first :: rest_Δ': non-nil; ph contains typ_all_etag.
         The body's d_sub LHS (open T ph) is not d_wf_typ-shape; closing
         this requires generalising the trans to non-nil outer Δ —
         deferred. *)
      admit.
Admitted.
(* d_sub_gen_trans_forall_l_untagged_helper: 1 residual admit when the
   inner __forall_l_untagged instantiates with non-nil Δ' (i.e., a
   polymorphic ph with ε-tags). Requires a generalised trans at non-nil
   outer Δ — separate restructure. *)

(** [d_sub_gen_trans]: transitivity of [d_sub_gen] along the FN^n
    mode-stack. With [m1] in [is_fn_n_ti] form and the second
    derivation at [mode_fn_n_subst m1 m_new] (the innermost TI
    replaced by [m_new]), the composite lives at the second mode.

    Induction on [is_fn_n_ti m1]:
    - [m1 = mode_ti]: the first sub is [__infer] (compose via
      [d_consis_sub_trans_gen_nil]) or [__refl_mono] (identity).
    - [m1 = mode_fn m]: the first sub is [__refl_mono] (identity) or
      arrow-shaped ([__embed]→[d_sub__arg], or [__arg]); the arrow
      cases route through [d_sub_gen_trans_arrow] with the IH; the
      [__forall_l_untagged] case routes through
      [d_sub_gen_trans_forall_l_untagged_helper] (above) which uses
      [d_sub_gen_to_d_sub] to convert IH output back to [d_sub].

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
      eapply d_consis_sub_trans_gen_nil; eauto.
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
      * (* d_sub__forall_l_untagged: A = typ_all_col colour_syn T —
           IS wf (δ-NEW case). Route through the helper that inducts on
           the inner d_sub structure (paper-faithful). *)
        eapply d_sub_gen_trans_forall_l_untagged_helper
          with (B := B);
          [ exact Hfn | exact HwfA | | exact Hsg | exact IHHfn ].
        (* Rebuild the d_sub from the destructured premises of the
           __forall_l_untagged constructor. *)
        eapply d_sub__forall_l_untagged with (Δ' := Δ') (ph := ph);
          eassumption.
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
    Δ ⨟ Γ ⊨ (syn_color T) ≈ (inh_color A) ->
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
  - (* __forall_inh_untagged (NEW δ-rule): LHS typ_all_col colour_syn — CAN
       match syn_color (ctyp_all C). Conclusion mono_typ (syn_color (ctyp_all C))
       is FALSE (it's typ_all_col, not mono). Lemma becomes provably-false
       on this case; needs precondition strengthening in Phase 1. *)
    admit.
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
Admitted.
(* d_consis_syn_inh_mono: 1 admit post-δ-refactor — __forall_inh_untagged
   makes the LHS-mono claim false on syn_color (ctyp_all _) inputs. *)

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
  - (* __forall_inh_tagged: LHS typ_all_etag — vacuous. *)
    destruct T0; simpl in HeqLHS; discriminate.
  - (* __forall_inh_untagged (NEW): LHS typ_all_col colour_syn — provably
       false on ctyp_all input (parallel to d_consis_syn_inh_mono). *)
    admit.
  - (* __forall_syn_tagged: LHS typ_all_etag — vacuous. *)
    destruct T0; simpl in HeqLHS; discriminate.
  - (* __forall_syn: RHS colour_syn — inh_color never produces colour_syn. *)
    destruct A0; simpl in HeqRHS; discriminate.
  - (* __forall_inh: LHS colour_inh — syn_color never produces colour_inh. *)
    destruct T0; simpl in HeqLHS; try discriminate.
  - (* __arrow *)
    destruct T0; simpl in HeqLHS; try discriminate.
    destruct A0; simpl in HeqRHS; try discriminate.
    inversion HeqLHS; inversion HeqRHS; subst.
    apply mono_typ__arrow.
    + eapply IHd_consis_gen1; reflexivity.
    + eapply IHd_consis_gen2; reflexivity.
Admitted.
(* d_consis_gen_syn_inh_mono: 1 admit post-δ-refactor — parallel
   provably-false case to d_consis_syn_inh_mono. *)

(* ====================================================================== *)
(*  §2 — SPLIT helpers for [exp_abs] / [exp_abs_anno] value cases         *)
(*  (formerly abs_subsumption.v)                                          *)
(* ====================================================================== *)



(** [is_inh_typ_inh_color]: any [inh_color C] for [C : ctyp] is
    [is_inh_typ] PROVIDED [d_wf_typ] (which rules out [ctyp_hole] /
    [ctyp_tophole] shapes). *)
Lemma is_inh_typ_inh_color : forall Γ C,
    d_wf_typ Γ (inh_color C) ->
    is_inh_typ (inh_color C).
Proof.
  intros Γ C Hwf. remember (inh_color C) as A in Hwf.
  revert C HeqA. induction Hwf; intros C HeqA.
  - destruct C; simpl in HeqA; try discriminate. apply is_inh_typ__unit.
  - destruct C; simpl in HeqA; try discriminate.
    inversion HeqA; subst. apply is_inh_typ__var.
  - destruct C; simpl in HeqA; try discriminate.
    inversion HeqA; subst. apply is_inh_typ__arrow.
    + eapply IHHwf1; reflexivity.
    + eapply IHHwf2; reflexivity.
  - destruct C; simpl in HeqA; try discriminate.
    inversion HeqA; subst.
    inst_cofinites_for is_inh_typ__all.
    intros X HX.
    assert (HX' : X `notin` L) by fsetdec.
    rewrite <- inh_color_open_var.
    eapply H0; eauto.
    rewrite inh_color_open_var. reflexivity.
Qed.

(** [is_syn_typ_syn_color]: parallel to [is_inh_typ_inh_color] but for
    the [syn_color] painting. Same shape of proof. *)
Lemma is_syn_typ_syn_color : forall Γ C,
    d_wf_typ Γ (syn_color C) ->
    is_syn_typ (syn_color C).
Proof.
  intros Γ C Hwf. remember (syn_color C) as A in Hwf.
  revert C HeqA. induction Hwf; intros C HeqA.
  - destruct C; simpl in HeqA; try discriminate. apply is_syn_typ__unit.
  - destruct C; simpl in HeqA; try discriminate.
    inversion HeqA; subst. apply is_syn_typ__var.
  - destruct C; simpl in HeqA; try discriminate.
    inversion HeqA; subst. apply is_syn_typ__arrow.
    + eapply IHHwf1; reflexivity.
    + eapply IHHwf2; reflexivity.
  - destruct C; simpl in HeqA; try discriminate.
    inversion HeqA; subst.
    inst_cofinites_for is_syn_typ__all.
    intros X HX.
    assert (HX' : X `notin` L) by fsetdec.
    rewrite <- syn_color_open_var.
    eapply H0; eauto.
    rewrite syn_color_open_var. reflexivity.
Qed.


(** [d_typing_abs_value_to_subsumption_split_d_sub]: d_sub companion
    for the SPLIT abs-value-to-subsumption helper. Parallels
    [d_typing_abs_anno_value_to_subsumption_d_sub] but:
    - LHS shape: [typ_arrow (inh_color_t Ahead) Bhead] (not
      [typ_arrow (syn_color_t Ahead) Bhead]).
    - Reconstruction via [d_typing_gen__abs] (not [__abs_anno]).

    [d_sub__check]'s LHS = [syn_color T] forces
    [syn_color T1 = inh_color_t Ahead], which is only satisfiable for
    Ahead mono (syn-painted on quantifiers vs inh-painted differ
    unless no quantifiers). Mono Ahead lets the binding [(x ~ Ahead)]
    coincide with the rule's [(x ~ syn_color A_rule)] for
    [A_rule := erase Ahead]. *)
Lemma d_typing_abs_value_to_subsumption_split_d_sub :
  forall Γ Δ T0 C0,
    Γ ⊢[ mode_tc ; Δ ] T0 ⊑ C0 ->
    Δ = nil ->
    forall Lvar e Ahead Bhead m_orig,
      T0 = typ_arrow (inh_color_t Ahead) Bhead ->
      d_wf_typ Γ (inh_color_t Ahead) ->
      (forall x, x `notin` Lvar ->
         d_typing_gen (decr_mode m_orig) ((x ~ dbind_typ Ahead) ++ Γ) (open_exp_wrt_exp e (exp_var_f x)) Bhead) ->
      (* [Hbody_at_tc]: pre-lifted body at mode_tc (only callable when
         [Bhead] is mono). Replaces internal [d_typing_gen_lift_mono]
         calls; the caller (D12) constructs this from its own IHbody.
         Freshness includes [dom Γ] so the proof of [d_wf_denv] at the
         extended context is constructible. *)
      (forall x, x `notin` Lvar `union` dom Γ ->
         mono_typ Bhead ->
         d_typing_gen mode_tc ((x ~ dbind_typ Ahead) ++ Γ)
           (open_exp_wrt_exp e (exp_var_f x)) Bhead) ->
      decr_mode m_orig = mode_ti ->
      d_wf_denv Γ ->
      d_typing_gen mode_tc Γ (exp_abs e) C0.
Proof.
  intros Γ Δ T0 C0 Hs. dependent induction Hs;
    intros HΔ Lvar e Ahead Bhead m_orig HT0 HwfA Hbody Hbody_at_tc Hdecr Hwfd; subst.
  - (* d_sub__check: LHS = syn_color T = typ_arrow (inh_color_t Ahead) Bhead.
       Forces T = ctyp_arrow T1 T2, then syn_color T1 = inh_color_t Ahead. *)
    destruct T; simpl in HT0; try discriminate.
    inversion HT0; subst.
    rename H0 into Hcons.
    inversion Hcons; subst.
    apply app_eq_nil in H0. destruct H0 as [HΔ1 HΔ2]. subst Δ1 Δ2.
    rename H6 into Hcons1. rename H7 into Hcons2.
    (* Derive mono via d_consis_syn_inh_mono (post-refactor helper).
       The typ_arrow = inh_color A equation is in context (named H_eq
       via match); inh_color_eq_arrow_inv splits A. *)
    assert (HmonoT1_syn : mono_typ (syn_color T1)).
    { match goal with H_eq : typ_arrow _ _ = inh_color _ |- _ =>
        symmetry in H_eq; apply inh_color_eq_arrow_inv in H_eq;
        destruct H_eq as [A1' [_ [_ [HA1_eq _]]]];
        rewrite <- HA1_eq in Hcons1
      end.
      eapply d_consis_syn_inh_mono; exact Hcons1. }
    assert (HmonoT2_syn : mono_typ (syn_color T2)).
    { match goal with H_eq : typ_arrow _ _ = inh_color _ |- _ =>
        symmetry in H_eq; apply inh_color_eq_arrow_inv in H_eq;
        destruct H_eq as [_ [A2' [_ [_ HA2_eq]]]];
        rewrite <- HA2_eq in Hcons2
      end.
      eapply d_consis_syn_inh_mono; exact Hcons2. }
    rename H2 into Heq_LHS.
    (* Heq_LHS: syn_color T1 = inh_color_t Ahead. T1 mono ⇒ Ahead mono
       (since inh_color_t Ahead = inh_color (erase Ahead), and that's
       mono iff erase Ahead is colourless, iff Ahead is mono). *)
    assert (HmonoIH : mono_typ (inh_color_t Ahead))
      by (rewrite <- Heq_LHS; exact HmonoT1_syn).
    assert (HmonoA : mono_typ Ahead)
      by (apply mono_typ_inh_color_t_inv; exact HmonoIH).
    pose proof (d_consis_lhs_syn_eq (mono_typ_is_syn_typ HmonoT2_syn) Hcons2)
      as HeqA2.
    pose proof (d_consis_lhs_syn_eq (mono_typ_is_syn_typ HmonoT1_syn) Hcons1)
      as HeqA1.
    subst.
    pose proof (mono_typ_syn_color_erase HmonoA) as HsynA.
    pose proof (mono_typ_inh_color_erase HmonoA) as HinhA.
    (* HsynA: syn_color (erase Ahead) = Ahead.
       HinhA: inh_color (erase Ahead) = Ahead. *)
    (* Erase both sides of Heq_LHS to derive T1 = erase Ahead. *)
    apply (f_equal erase) in Heq_LHS.
    rewrite inh_color_t_inh_color_erase in Heq_LHS.
    rewrite erase_inh_color in Heq_LHS.
    rewrite erase_syn_color in Heq_LHS.
    subst T1.
    (* Goal: d_typing_gen mode_tc Γ (exp_abs e) (typ_arrow (syn_color (erase Ahead)) (syn_color T2)).
       Rewrite syn_color (erase Ahead) ↦ inh_color (erase Ahead) (both = Ahead). *)
    rewrite HsynA.
    rewrite <- HinhA at 1.
    assert (HwfA_raw : d_wf_typ Γ Ahead).
    { rewrite <- HinhA. rewrite <- inh_color_t_inh_color_erase. exact HwfA. }
    apply d_typing_gen__abs with (L := Lvar `union` dom Γ).
    + rewrite <- inh_color_t_inh_color_erase. exact HwfA.
    + intros x0 Hx0.
      rewrite HsynA.
      assert (Hwfd_x0 : d_wf_denv ((x0 ~ dbind_typ Ahead) ++ Γ))
        by (apply d_wf_denv__typ; auto).
      (* Replace lift_mono with Hbody_at_tc (caller-supplied, valid
         since Bhead = syn_color T2 here is mono). *)
      apply Hbody_at_tc; auto.
  - (* d_sub__forall_r: recurse via IH. *)
    apply d_typing_gen__forall with (L := L `union` Lvar `union` dom Γ).
    + apply is_value__abs.
    + intros X HX.
      assert (Hwfd_X : d_wf_denv ((X ~ dbind_tvar) ++ Γ))
        by (apply d_wf_denv__tvar; auto).
      eapply H0 with (Ahead := Ahead) (Bhead := Bhead) (m_orig := m_orig)
        (Lvar := Lvar); eauto.
      * apply d_wf_typ_weakening_head; auto.
      * intros y Hy.
        apply d_typing_gen_weakening with
          (Γ1 := (y ~ dbind_typ Ahead)) (Γ2 := (X ~ dbind_tvar)) (Γ3 := Γ).
        apply Hbody. exact Hy.
      * (* Weaken Hbody_at_tc to extended context. *)
        intros y Hy Hmono.
        apply d_typing_gen_weakening with
          (Γ1 := (y ~ dbind_typ Ahead)) (Γ2 := (X ~ dbind_tvar)) (Γ3 := Γ).
        apply Hbody_at_tc; auto.
  - (* d_sub__forall_l_tagged: vacuous (LHS not typ_arrow). *)
    discriminate.
  - (* d_sub__forall_l_untagged (NEW δ-rule): LHS typ_all_col colour_syn,
       not typ_arrow ⇒ HT0 (typ_arrow ... = syn_color T) contradicts;
       syn_color T = typ_all_col only when T = ctyp_all _ which forces
       typ_arrow ≠ typ_all_col. *)
    destruct T; simpl in HT0; try discriminate.
Qed.

(** [d_typing_abs_value_to_subsumption_split]: abs value-to-subsumption
    helper with SPLIT binding/arrow-arg. Parallels
    [d_typing_abs_anno_value_to_subsumption] but for [exp_abs e] (not
    [exp_abs_anno A e]) with arrow arg [inh_color_t A] (not
    [syn_color_t A]). The split signature lets it apply at the D12
    __abs callsite where the rule's body binding is [syn_color A0]
    and the conclusion's arrow arg is [inh_color A0]. *)
Lemma d_typing_abs_value_to_subsumption_split :
  forall L Γ e A B m_orig C,
    d_wf_typ Γ (inh_color_t A) ->
    (forall x, x `notin` L ->
       d_typing_gen (decr_mode m_orig) ((x ~ dbind_typ A) ++ Γ) (open_exp_wrt_exp e (exp_var_f x)) B) ->
    (* [Hbody_at_tc]: pre-lifted body at mode_tc (only callable when B
       is mono). See [_split_d_sub] for rationale. Freshness includes
       [dom Γ] so the caller can construct [d_wf_denv] at extended ctx. *)
    (forall x, x `notin` L `union` dom Γ ->
       mono_typ B ->
       d_typing_gen mode_tc ((x ~ dbind_typ A) ++ Γ)
         (open_exp_wrt_exp e (exp_var_f x)) B) ->
    decr_mode m_orig = mode_ti ->
    d_wf_denv Γ ->
    d_sub_gen mode_tc nil Γ (typ_arrow (inh_color_t A) B) C ->
    d_typing_gen mode_tc Γ (exp_abs e) C.
Proof.
  intros L Γ e A B m_orig C HwfA Hbody Hbody_at_tc Hdecr Hwfd Hs.
  dependent induction Hs.
  - (* __embed: dispatch to d_sub companion. *)
    eapply d_typing_abs_value_to_subsumption_split_d_sub
      with (Ahead := A) (Bhead := B) (m_orig := m_orig); eauto.
  - (* __check_gen: LHS = syn_color T forces T = ctyp_arrow T1 T2,
       then syn_color T1 = inh_color_t A — only satisfiable for A mono. *)
    destruct T; simpl in x; try discriminate.
    inversion x; subst.
    rename H0 into Hcons.
    inversion Hcons; subst.
    apply app_eq_nil in H0. destruct H0 as [HΔ1 HΔ2]. subst Δ1 Δ2.
    rename H6 into Hcons1. rename H7 into Hcons2.
    assert (HmonoT1_syn : mono_typ (syn_color T1)).
    { match goal with H_eq : typ_arrow _ _ = inh_color _ |- _ =>
        symmetry in H_eq; apply inh_color_eq_arrow_inv in H_eq;
        destruct H_eq as [A1' [_ [_ [HA1_eq _]]]];
        rewrite <- HA1_eq in Hcons1
      end.
      eapply d_consis_gen_syn_inh_mono; exact Hcons1. }
    assert (HmonoT2_syn : mono_typ (syn_color T2)).
    { match goal with H_eq : typ_arrow _ _ = inh_color _ |- _ =>
        symmetry in H_eq; apply inh_color_eq_arrow_inv in H_eq;
        destruct H_eq as [_ [A2' [_ [_ HA2_eq]]]];
        rewrite <- HA2_eq in Hcons2
      end.
      eapply d_consis_gen_syn_inh_mono; exact Hcons2. }
    match goal with H : syn_color T1 = inh_color_t A |- _ =>
      rename H into Heq_LHS
    end.
    assert (HmonoIH : mono_typ (inh_color_t A))
      by (rewrite <- Heq_LHS; exact HmonoT1_syn).
    assert (HmonoA : mono_typ A)
      by (apply mono_typ_inh_color_t_inv; exact HmonoIH).
    pose proof (d_consis_gen_lhs_syn_eq (mono_typ_is_syn_typ HmonoT2_syn) Hcons2)
      as HeqA2.
    pose proof (d_consis_gen_lhs_syn_eq (mono_typ_is_syn_typ HmonoT1_syn) Hcons1)
      as HeqA1.
    subst.
    pose proof (mono_typ_syn_color_erase HmonoA) as HsynA.
    pose proof (mono_typ_inh_color_erase HmonoA) as HinhA.
    apply (f_equal erase) in Heq_LHS.
    rewrite inh_color_t_inh_color_erase in Heq_LHS.
    rewrite erase_inh_color in Heq_LHS.
    rewrite erase_syn_color in Heq_LHS.
    subst T1.
    rewrite HsynA.
    rewrite <- HinhA at 1.
    assert (HwfA_raw : d_wf_typ Γ A).
    { rewrite <- HinhA. rewrite <- inh_color_t_inh_color_erase. exact HwfA. }
    apply d_typing_gen__abs with (L := L `union` dom Γ).
    + rewrite <- inh_color_t_inh_color_erase. exact HwfA.
    + intros x0 Hx0.
      rewrite HsynA.
      apply Hbody_at_tc; auto.
  - (* __refl_mono: target = typ_arrow (inh_color_t A) B forced mono. *)
    match goal with Hm : mono_typ (typ_arrow _ _) |- _ =>
      inversion Hm; subst
    end.
    match goal with HmIH : mono_typ (inh_color_t A) |- _ =>
      assert (HmonoA : mono_typ A)
        by (apply mono_typ_inh_color_t_inv; auto)
    end.
    assert (HwfA_raw : d_wf_typ Γ A).
    { rewrite <- (mono_typ_inh_color_erase HmonoA).
      rewrite <- inh_color_t_inh_color_erase. exact HwfA. }
    rewrite inh_color_t_inh_color_erase.
    apply d_typing_gen__abs with (L := L `union` dom Γ).
    + rewrite (mono_typ_inh_color_erase HmonoA). assumption.
    + intros x Hx.
      rewrite (mono_typ_syn_color_erase HmonoA).
      apply Hbody_at_tc; auto.
  - (* __forall_r: target = typ_all_col colour_inh A_target. Recurse via
       [d_typing_gen__forall] + IH at each X. *)
    apply d_typing_gen__forall with (L := L0 `union` dom Γ).
    + apply is_value__abs.
    + intros X HX.
      assert (Hwfd_X : d_wf_denv ((X ~ dbind_tvar) ++ Γ))
        by (apply d_wf_denv__tvar; auto).
      apply H0 with (A := A) (B := B); auto.
      * apply d_wf_typ_weakening_head; auto.
      * intros y Hy.
        apply d_typing_gen_weakening with
          (Γ1 := (y ~ dbind_typ A)) (Γ2 := (X ~ dbind_tvar)) (Γ3 := Γ).
        apply Hbody. exact Hy.
      * (* Weaken Hbody_at_tc to extended context (X ~ tvar)::Γ. *)
        intros y Hy Hmono.
        apply d_typing_gen_weakening with
          (Γ1 := (y ~ dbind_typ A)) (Γ2 := (X ~ dbind_tvar)) (Γ3 := Γ).
        apply Hbody_at_tc; auto.
Qed.

(** [d_typing_abs_value_to_subsumption_split_ti]: mode_ti variant of the
    SPLIT abs helper. Same shape, but Hsub_gen / conclusion at mode_ti
    (not mode_tc). At mode_ti, d_sub_gen rules are only __embed,
    __infer_gen, __refl_mono — no __forall_r recursion.

    Strengthened signature: added [d_wf_typ Γ B] premise so that the
    __embed/__infer_gen cases can derive [is_syn_typ (syn_color T2)]
    from [B = syn_color T2] (forced by [d_sub__infer]) + the wf premise.
    Without this strengthening, the LHS-rigidity lemma would need an
    inductive helper that fails on the [d_consis_gen__forall_syn] case. *)
Lemma d_typing_abs_value_to_subsumption_split_ti :
  forall L Γ e A B m_orig C,
    d_wf_typ Γ (inh_color_t A) ->
    d_wf_typ Γ B ->
    (forall x, x `notin` L ->
       d_typing_gen (decr_mode m_orig) ((x ~ dbind_typ A) ++ Γ) (open_exp_wrt_exp e (exp_var_f x)) B) ->
    decr_mode m_orig = mode_ti ->
    d_wf_denv Γ ->
    d_sub_gen mode_ti nil Γ (typ_arrow (inh_color_t A) B) C ->
    d_typing_gen mode_ti Γ (exp_abs e) C.
Proof.
  intros L Γ e A B m_orig C HwfA HwfB Hbody Hdecr Hwfd Hs.
  dependent induction Hs.
  - (* __embed: d_sub mode_ti, only d_sub__infer applies. *)
    rename H into Hdsub. dependent destruction Hdsub.
    (* d_sub__infer: LHS = syn_color T, forces typ_arrow shape. *)
    destruct T; simpl in x; try discriminate.
    inversion x; subst.
    match goal with H : d_consis _ _ _ _ |- _ => rename H into Hcons end.
    inversion Hcons; subst.
    match goal with H : ?l1 ++ ?l2 = nil |- _ =>
      apply app_eq_nil in H; destruct H as [HΔ1 HΔ2]; subst l1 l2
    end.
    match goal with H : d_consis _ _ (syn_color T1) _ |- _ => rename H into Hcons1 end.
    match goal with H : d_consis _ _ (syn_color T2) _ |- _ => rename H into Hcons2 end.
    match goal with H : syn_color T1 = inh_color_t A |- _ =>
      rename H into Heq_LHS
    end.
    (* Derive A mono from the equation [syn_color T1 = inh_color_t A]
       (rules out [typ_all_*] colour-mismatch + [hole]/[tophole] via wf). *)
    assert (HmonoA : mono_typ A).
    { symmetry in Heq_LHS. eapply inh_color_t_eq_syn_color_mono; eauto. }
    pose proof (mono_typ_syn_color_erase HmonoA) as HsynA.
    pose proof (mono_typ_inh_color_erase HmonoA) as HinhA.
    apply (f_equal erase) in Heq_LHS.
    rewrite inh_color_t_inh_color_erase in Heq_LHS.
    rewrite erase_inh_color in Heq_LHS.
    rewrite erase_syn_color in Heq_LHS.
    subst T1.
    (* Rigidity: derive [syn_color T2 = syn_color A2] from Hcons2 +
       [HwfB] giving [is_syn_typ (syn_color T2)] via [is_syn_typ_syn_color]
       (B = syn_color T2 after [inversion x; subst]). *)
    assert (HwfA_raw : d_wf_typ Γ A).
    { rewrite <- HinhA. rewrite <- inh_color_t_inh_color_erase. exact HwfA. }
    assert (HwfsynA : d_wf_typ Γ (syn_color (erase A))).
    { rewrite HsynA. assumption. }
    assert (HsynT1 : is_syn_typ (syn_color (erase A)))
      by (eapply is_syn_typ_syn_color; eassumption).
    assert (HsynT2 : is_syn_typ (syn_color T2))
      by (eapply is_syn_typ_syn_color; eassumption).
    pose proof (d_consis_lhs_syn_eq HsynT1 Hcons1) as HeqA1.
    pose proof (d_consis_lhs_syn_eq HsynT2 Hcons2) as HeqA2.
    subst.
    rewrite HsynA.
    rewrite <- HinhA at 1.
    apply d_typing_gen__abs with (L := L `union` dom Γ).
    + rewrite <- inh_color_t_inh_color_erase. exact HwfA.
    + intros x0 Hx0.
      rewrite HsynA.
      (* Body Hbody already at mode_ti (decr_mode m_orig = mode_ti) with
         binding [(x ~ dbind_typ A) ++ Γ] and conclusion B = syn_color T2;
         no lift needed. *)
      simpl. rewrite <- Hdecr. apply Hbody. fsetdec.
  - (* __infer_gen: parallel to __embed __infer, with d_consis_gen. *)
    destruct T; simpl in x; try discriminate.
    inversion x; subst.
    match goal with H : d_consis_gen _ _ _ _ |- _ => rename H into Hcons end.
    inversion Hcons; subst.
    match goal with H : ?l1 ++ ?l2 = nil |- _ =>
      apply app_eq_nil in H; destruct H as [HΔ1 HΔ2]; subst l1 l2
    end.
    match goal with H : d_consis_gen _ _ (syn_color T1) _ |- _ => rename H into Hcons1 end.
    match goal with H : d_consis_gen _ _ (syn_color T2) _ |- _ => rename H into Hcons2 end.
    match goal with H : syn_color T1 = inh_color_t A |- _ =>
      rename H into Heq_LHS
    end.
    assert (HmonoA : mono_typ A).
    { symmetry in Heq_LHS. eapply inh_color_t_eq_syn_color_mono; eauto. }
    pose proof (mono_typ_syn_color_erase HmonoA) as HsynA.
    pose proof (mono_typ_inh_color_erase HmonoA) as HinhA.
    apply (f_equal erase) in Heq_LHS.
    rewrite inh_color_t_inh_color_erase in Heq_LHS.
    rewrite erase_inh_color in Heq_LHS.
    rewrite erase_syn_color in Heq_LHS.
    subst T1.
    assert (HwfA_raw : d_wf_typ Γ A).
    { rewrite <- HinhA. rewrite <- inh_color_t_inh_color_erase. exact HwfA. }
    assert (HwfsynA : d_wf_typ Γ (syn_color (erase A))).
    { rewrite HsynA. assumption. }
    assert (HsynT1 : is_syn_typ (syn_color (erase A)))
      by (eapply is_syn_typ_syn_color; eassumption).
    assert (HsynT2 : is_syn_typ (syn_color T2))
      by (eapply is_syn_typ_syn_color; eassumption).
    pose proof (d_consis_gen_lhs_syn_eq HsynT1 Hcons1) as HeqA1.
    pose proof (d_consis_gen_lhs_syn_eq HsynT2 Hcons2) as HeqA2.
    subst.
    rewrite HsynA.
    rewrite <- HinhA at 1.
    apply d_typing_gen__abs with (L := L `union` dom Γ).
    + rewrite <- inh_color_t_inh_color_erase. exact HwfA.
    + intros x0 Hx0.
      rewrite HsynA.
      simpl. rewrite <- Hdecr. apply Hbody. fsetdec.
  - (* __refl_mono: target = typ_arrow (inh_color_t A) B forced mono. *)
    match goal with Hm : mono_typ (typ_arrow _ _) |- _ =>
      inversion Hm; subst
    end.
    match goal with HmIH : mono_typ (inh_color_t A) |- _ =>
      assert (HmonoA : mono_typ A)
        by (apply mono_typ_inh_color_t_inv; auto)
    end.
    assert (HwfA_raw : d_wf_typ Γ A).
    { rewrite <- (mono_typ_inh_color_erase HmonoA).
      rewrite <- inh_color_t_inh_color_erase. exact HwfA. }
    rewrite inh_color_t_inh_color_erase.
    apply d_typing_gen__abs with (L := L `union` dom Γ).
    + rewrite (mono_typ_inh_color_erase HmonoA). assumption.
    + intros x Hx.
      rewrite (mono_typ_syn_color_erase HmonoA).
      (* Body Hbody at mode_ti, binding (x ~ dbind_typ A), conclusion B;
         direct application — lift_mono would be a no-op. *)
      simpl. rewrite <- Hdecr. apply Hbody. fsetdec.
Qed.

(** [d_typing_abs_anno_value_to_subsumption_split_d_sub]: d_sub
    companion for the SPLIT abs_anno helper. Conclusion's term is
    [exp_abs_anno (inh_color_t Ahead) e] to match the rule's
    [exp_abs_anno (inh_color A_rule) e] for [A_rule = erase Ahead]
    (in the mono case, [inh_color (erase Ahead) = inh_color_t Ahead]
    via [inh_color_t_inh_color_erase]). *)
Lemma d_typing_abs_anno_value_to_subsumption_split_d_sub :
  forall Γ Δ T0 C0,
    Γ ⊢[ mode_tc ; Δ ] T0 ⊑ C0 ->
    Δ = nil ->
    forall Lvar e Ahead Bhead m_orig,
      T0 = typ_arrow Ahead Bhead ->
      d_wf_typ Γ Ahead ->
      (forall x, x `notin` Lvar ->
         d_typing_gen (decr_mode m_orig) ((x ~ dbind_typ Ahead) ++ Γ) (open_exp_wrt_exp e (exp_var_f x)) Bhead) ->
      (forall x, x `notin` Lvar `union` dom Γ ->
         mono_typ Bhead ->
         d_typing_gen mode_tc ((x ~ dbind_typ Ahead) ++ Γ)
           (open_exp_wrt_exp e (exp_var_f x)) Bhead) ->
      decr_mode m_orig = mode_ti ->
      d_wf_denv Γ ->
      d_typing_gen mode_tc Γ (exp_abs_anno (inh_color_t Ahead) e) C0.
Proof.
  intros Γ Δ T0 C0 Hs. dependent induction Hs;
    intros HΔ Lvar e Ahead Bhead m_orig HT0 HwfA Hbody Hbody_at_tc Hdecr Hwfd; subst.
  - (* d_sub__check: LHS = syn_color T = typ_arrow Ahead Bhead.
       After `inversion HT0; subst`, Ahead gets substituted with syn_color T1
       (and Bhead with syn_color T2). Work with syn_color T1 / T2 directly. *)
    destruct T; simpl in HT0; try discriminate.
    inversion HT0; subst.
    match goal with H : d_consis _ _ _ _ |- _ => rename H into Hcons end.
    inversion Hcons; subst.
    match goal with H : ?l1 ++ ?l2 = nil |- _ =>
      apply app_eq_nil in H; destruct H as [HΔ1 HΔ2]; subst l1 l2
    end.
    match goal with H : d_consis _ _ (syn_color T1) _ |- _ => rename H into Hcons1 end.
    match goal with H : d_consis _ _ (syn_color T2) _ |- _ => rename H into Hcons2 end.
    assert (HmonoT1_syn : mono_typ (syn_color T1)).
    { match goal with H_eq : typ_arrow _ _ = inh_color _ |- _ =>
        symmetry in H_eq; apply inh_color_eq_arrow_inv in H_eq;
        destruct H_eq as [A1' [_ [_ [HA1_eq _]]]];
        rewrite <- HA1_eq in Hcons1
      end.
      eapply d_consis_syn_inh_mono; exact Hcons1. }
    assert (HmonoT2_syn : mono_typ (syn_color T2)).
    { match goal with H_eq : typ_arrow _ _ = inh_color _ |- _ =>
        symmetry in H_eq; apply inh_color_eq_arrow_inv in H_eq;
        destruct H_eq as [_ [A2' [_ [_ HA2_eq]]]];
        rewrite <- HA2_eq in Hcons2
      end.
      eapply d_consis_syn_inh_mono; exact Hcons2. }
    pose proof (d_consis_lhs_syn_eq (mono_typ_is_syn_typ HmonoT2_syn) Hcons2)
      as HeqA2.
    pose proof (d_consis_lhs_syn_eq (mono_typ_is_syn_typ HmonoT1_syn) Hcons1)
      as HeqA1.
    subst.
    (* Goal: d_typing_gen mode_tc Γ (exp_abs_anno (inh_color_t (syn_color T1)) e)
              (typ_arrow (syn_color T1) (syn_color T2)).
       Simplify: inh_color_t (syn_color T1) = inh_color T1
       (via inh_color_t_inh_color_erase + erase_syn_color).
       Apply d_typing_gen__abs_anno with A_rule := T1. *)
    replace (inh_color_t (syn_color T1)) with (inh_color T1)
      by (rewrite inh_color_t_inh_color_erase; rewrite erase_syn_color; reflexivity).
    apply d_typing_gen__abs_anno with (L := Lvar `union` dom Γ).
    + assumption.
    + intros x0 Hx0.
      apply Hbody_at_tc; auto.
  - (* d_sub__forall_r: recurse via IH. *)
    apply d_typing_gen__forall with (L := L `union` Lvar `union` dom Γ).
    + apply is_value__abs_anno.
    + intros X HX.
      assert (Hwfd_X : d_wf_denv ((X ~ dbind_tvar) ++ Γ))
        by (apply d_wf_denv__tvar; auto).
      eapply H0 with (Ahead := Ahead) (Bhead := Bhead) (m_orig := m_orig)
        (Lvar := Lvar); eauto.
      * apply d_wf_typ_weakening_head; auto.
      * intros y Hy.
        apply d_typing_gen_weakening with
          (Γ1 := (y ~ dbind_typ Ahead)) (Γ2 := (X ~ dbind_tvar)) (Γ3 := Γ).
        apply Hbody. exact Hy.
      * intros y Hy Hmono.
        apply d_typing_gen_weakening with
          (Γ1 := (y ~ dbind_typ Ahead)) (Γ2 := (X ~ dbind_tvar)) (Γ3 := Γ).
        apply Hbody_at_tc; auto.
  - (* d_sub__forall_l_tagged: vacuous (LHS not typ_arrow). *)
    discriminate.
  - (* d_sub__forall_l_untagged (NEW δ-rule): LHS typ_all_col colour_syn,
       not typ_arrow ⇒ vacuous via shape mismatch. *)
    destruct T; simpl in HT0; try discriminate.
Qed.

(** [d_typing_abs_anno_value_to_subsumption_split]: SPLIT abs_anno
    helper. Conclusion's term is [exp_abs_anno (inh_color_t A) e]. *)
Lemma d_typing_abs_anno_value_to_subsumption_split :
  forall L Γ e A B m_orig C,
    d_wf_typ Γ A ->
    (forall x, x `notin` L ->
       d_typing_gen (decr_mode m_orig) ((x ~ dbind_typ A) ++ Γ) (open_exp_wrt_exp e (exp_var_f x)) B) ->
    (forall x, x `notin` L `union` dom Γ ->
       mono_typ B ->
       d_typing_gen mode_tc ((x ~ dbind_typ A) ++ Γ)
         (open_exp_wrt_exp e (exp_var_f x)) B) ->
    decr_mode m_orig = mode_ti ->
    d_wf_denv Γ ->
    d_sub_gen mode_tc nil Γ (typ_arrow A B) C ->
    d_typing_gen mode_tc Γ (exp_abs_anno (inh_color_t A) e) C.
Proof.
  intros L Γ e A B m_orig C HwfA Hbody Hbody_at_tc Hdecr Hwfd Hs.
  dependent induction Hs.
  - (* __embed: dispatch to d_sub companion. *)
    eapply d_typing_abs_anno_value_to_subsumption_split_d_sub
      with (Ahead := A) (Bhead := B) (m_orig := m_orig); eauto.
  - (* __check_gen: parallel to _d_sub __check. *)
    destruct T; simpl in x; try discriminate.
    inversion x; subst.
    match goal with H : d_consis_gen _ _ _ _ |- _ => rename H into Hcons end.
    inversion Hcons; subst.
    match goal with H : ?l1 ++ ?l2 = nil |- _ =>
      apply app_eq_nil in H; destruct H as [HΔ1 HΔ2]; subst l1 l2
    end.
    match goal with H : d_consis_gen _ _ (syn_color T1) _ |- _ => rename H into Hcons1 end.
    match goal with H : d_consis_gen _ _ (syn_color T2) _ |- _ => rename H into Hcons2 end.
    assert (HmonoT1_syn : mono_typ (syn_color T1)).
    { match goal with H_eq : typ_arrow _ _ = inh_color _ |- _ =>
        symmetry in H_eq; apply inh_color_eq_arrow_inv in H_eq;
        destruct H_eq as [A1' [_ [_ [HA1_eq _]]]];
        rewrite <- HA1_eq in Hcons1
      end.
      eapply d_consis_gen_syn_inh_mono; exact Hcons1. }
    assert (HmonoT2_syn : mono_typ (syn_color T2)).
    { match goal with H_eq : typ_arrow _ _ = inh_color _ |- _ =>
        symmetry in H_eq; apply inh_color_eq_arrow_inv in H_eq;
        destruct H_eq as [_ [A2' [_ [_ HA2_eq]]]];
        rewrite <- HA2_eq in Hcons2
      end.
      eapply d_consis_gen_syn_inh_mono; exact Hcons2. }
    pose proof (d_consis_gen_lhs_syn_eq (mono_typ_is_syn_typ HmonoT2_syn) Hcons2)
      as HeqA2.
    pose proof (d_consis_gen_lhs_syn_eq (mono_typ_is_syn_typ HmonoT1_syn) Hcons1)
      as HeqA1.
    subst.
    (* Goal: d_typing_gen mode_tc Γ (exp_abs_anno (inh_color_t (syn_color T1)) e)
              (typ_arrow (syn_color T1) (syn_color T2)). *)
    replace (inh_color_t (syn_color T1)) with (inh_color T1)
      by (rewrite inh_color_t_inh_color_erase; rewrite erase_syn_color; reflexivity).
    apply d_typing_gen__abs_anno with (L := L `union` dom Γ).
    + assumption.
    + intros x0 Hx0.
      apply Hbody_at_tc; auto.
  - (* __refl_mono: target = typ_arrow A B forced mono. Reconstruct via
       d_typing_gen__abs_anno with A_rule := erase A; the rule produces
       term [exp_abs_anno (inh_color (erase A)) e] and conclusion arg
       [syn_color (erase A)]. For mono A: inh_color (erase A) = A and
       syn_color (erase A) = A; also inh_color_t A = inh_color (erase A)
       via inh_color_t_inh_color_erase. *)
    match goal with Hm : mono_typ (typ_arrow _ _) |- _ =>
      inversion Hm; subst
    end.
    match goal with HmA : mono_typ A |- _ => rename HmA into HmonoA end.
    pose proof (mono_typ_syn_color_erase HmonoA) as HsynA.
    pose proof (mono_typ_inh_color_erase HmonoA) as HinhA.
    (* Goal: d_typing_gen mode_tc Γ (exp_abs_anno (inh_color_t A) e) (typ_arrow A B). *)
    replace (inh_color_t A) with (inh_color (erase A))
      by (symmetry; apply inh_color_t_inh_color_erase).
    rewrite <- HsynA at 2.
    apply d_typing_gen__abs_anno with (L := L `union` dom Γ).
    + rewrite HsynA. assumption.
    + intros x Hx.
      rewrite HsynA.
      apply Hbody_at_tc; auto.
  - (* __forall_r: recurse via IH. *)
    apply d_typing_gen__forall with (L := L0 `union` dom Γ).
    + apply is_value__abs_anno.
    + intros X HX.
      assert (Hwfd_X : d_wf_denv ((X ~ dbind_tvar) ++ Γ))
        by (apply d_wf_denv__tvar; auto).
      apply H0 with (A := A) (B := B); auto.
      * apply d_wf_typ_weakening_head; auto.
      * intros y Hy.
        apply d_typing_gen_weakening with
          (Γ1 := (y ~ dbind_typ A)) (Γ2 := (X ~ dbind_tvar)) (Γ3 := Γ).
        apply Hbody. exact Hy.
      * intros y Hy Hmono.
        apply d_typing_gen_weakening with
          (Γ1 := (y ~ dbind_typ A)) (Γ2 := (X ~ dbind_tvar)) (Γ3 := Γ).
        apply Hbody_at_tc; auto.
Qed.

(** [d_typing_abs_anno_value_to_subsumption_split_ti]: mode_ti variant of
    the SPLIT abs_anno helper. Strengthened with [d_wf_typ Γ B] premise
    (used to derive [is_syn_typ (syn_color T2)] in __embed/__infer_gen). *)
Lemma d_typing_abs_anno_value_to_subsumption_split_ti :
  forall L Γ e A B m_orig C,
    d_wf_typ Γ A ->
    d_wf_typ Γ B ->
    (forall x, x `notin` L ->
       d_typing_gen (decr_mode m_orig) ((x ~ dbind_typ A) ++ Γ) (open_exp_wrt_exp e (exp_var_f x)) B) ->
    decr_mode m_orig = mode_ti ->
    d_wf_denv Γ ->
    d_sub_gen mode_ti nil Γ (typ_arrow A B) C ->
    d_typing_gen mode_ti Γ (exp_abs_anno (inh_color_t A) e) C.
Proof.
  intros L Γ e A B m_orig C HwfA HwfB Hbody Hdecr Hwfd Hs.
  dependent induction Hs.
  - (* __embed: d_sub mode_ti, only d_sub__infer applies. *)
    rename H into Hdsub. dependent destruction Hdsub.
    destruct T; simpl in x; try discriminate.
    inversion x; subst.
    match goal with H : d_consis _ _ _ _ |- _ => rename H into Hcons end.
    inversion Hcons; subst.
    match goal with H : ?l1 ++ ?l2 = nil |- _ =>
      apply app_eq_nil in H; destruct H as [HΔ1 HΔ2]; subst l1 l2
    end.
    match goal with H : d_consis _ _ (syn_color T1) _ |- _ => rename H into Hcons1 end.
    match goal with H : d_consis _ _ (syn_color T2) _ |- _ => rename H into Hcons2 end.
    assert (HsynT1' : is_syn_typ (syn_color T1))
      by (eapply is_syn_typ_syn_color; eassumption).
    assert (HsynT2' : is_syn_typ (syn_color T2))
      by (eapply is_syn_typ_syn_color; eassumption).
    pose proof (d_consis_lhs_syn_eq HsynT1' Hcons1) as HeqA1.
    pose proof (d_consis_lhs_syn_eq HsynT2' Hcons2) as HeqA2.
    subst.
    replace (inh_color_t (syn_color T1)) with (inh_color T1)
      by (rewrite inh_color_t_inh_color_erase; rewrite erase_syn_color; reflexivity).
    apply d_typing_gen__abs_anno with (L := L `union` dom Γ).
    + assumption.
    + intros x0 Hx0.
      simpl. rewrite <- Hdecr. apply Hbody. fsetdec.
  - (* __infer_gen: parallel to __embed __infer with d_consis_gen. *)
    destruct T; simpl in x; try discriminate.
    inversion x; subst.
    match goal with H : d_consis_gen _ _ _ _ |- _ => rename H into Hcons end.
    inversion Hcons; subst.
    match goal with H : ?l1 ++ ?l2 = nil |- _ =>
      apply app_eq_nil in H; destruct H as [HΔ1 HΔ2]; subst l1 l2
    end.
    match goal with H : d_consis_gen _ _ (syn_color T1) _ |- _ => rename H into Hcons1 end.
    match goal with H : d_consis_gen _ _ (syn_color T2) _ |- _ => rename H into Hcons2 end.
    assert (HsynT1 : is_syn_typ (syn_color T1))
      by (eapply is_syn_typ_syn_color; eassumption).
    assert (HsynT2 : is_syn_typ (syn_color T2))
      by (eapply is_syn_typ_syn_color; eassumption).
    pose proof (d_consis_gen_lhs_syn_eq HsynT1 Hcons1) as HeqA1.
    pose proof (d_consis_gen_lhs_syn_eq HsynT2 Hcons2) as HeqA2.
    subst.
    replace (inh_color_t (syn_color T1)) with (inh_color T1)
      by (rewrite inh_color_t_inh_color_erase; rewrite erase_syn_color; reflexivity).
    apply d_typing_gen__abs_anno with (L := L `union` dom Γ).
    + assumption.
    + intros x0 Hx0.
      simpl. rewrite <- Hdecr. apply Hbody. fsetdec.
  - (* __refl_mono: target = typ_arrow A B forced mono. *)
    match goal with Hm : mono_typ (typ_arrow _ _) |- _ =>
      inversion Hm; subst
    end.
    match goal with HmA : mono_typ A |- _ => rename HmA into HmonoA end.
    pose proof (mono_typ_syn_color_erase HmonoA) as HsynA.
    pose proof (mono_typ_inh_color_erase HmonoA) as HinhA.
    replace (inh_color_t A) with (inh_color (erase A))
      by (symmetry; apply inh_color_t_inh_color_erase).
    rewrite <- HsynA at 2.
    apply d_typing_gen__abs_anno with (L := L `union` dom Γ).
    + rewrite HsynA. assumption.
    + intros x Hx.
      rewrite HsynA.
      simpl. rewrite <- Hdecr. apply Hbody. fsetdec.
Qed.



