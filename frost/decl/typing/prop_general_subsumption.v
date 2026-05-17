(** Frost — declarative typing metatheory: D12 (Generalised General
    Subsumption, paper Lemma B.5), gen → original bridges, and D1
    (paper Lemma 3.1, General Subsumption) as a corollary. *)

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
Require Import src.frost.decl.typing.prop_subsumption_aux.

Set Implicit Arguments.

(** ** Generalised General Subsumption (paper Lemma B.5).

    The statement: for [Hty : d_typing_gen m_orig Γ e A] with [m_orig ∈ FN^n TI],
    and [Hsub_gen : d_sub_gen (mode_fn_n_subst m_orig m_new) nil Γ A B]
    (using the GENERALISED sub), we derive [d_typing_gen (mode_fn_n_subst
    m_orig m_new) Γ e B].

    The use of [d_sub_gen] (rather than the original [d_sub]) is what
    makes the __app function-side lift go through: that lift constructs
    a sub via [d_sub_gen__arg] with [d_consis_gen__refl_any] on the
    function's argument type A0 (no longer requiring A0 to be mono).

    Proof outline (per paper appendix Lemma B.5):
    - Induct on Hty via [d_typing_pat_mut].
    - For each Hty case, dispatch on Hsub_gen's shape.
    - __abs / __abs_anno: body IH from the mutual induction provides
      body's generalised subsumption at (x ~ A_arg) ++ Γ.
    - __app: function-side IH fires at [mode_fn m_orig] (which is also
      in [is_fn_n_ti] form). The sub for the IH is [d_sub_gen__arg]
      using [d_consis_gen__refl_any] on the argument type.

    Closure status (this commit):
    - Vacuous mode_tc cases (Hty ∈ {__freeze, __forall}): CLOSED.
    - Hty ∈ {__unit, __var, __anno} / Hsub_gen = __embed: CLOSED via
      [d_typing_gen__sub] at the corresponding [is_base_term].
    - Hty = __unit / Hsub_gen = __refl_any: CLOSED via case-split on
      [mode_typ_compat] (mode_ti, mode_tc; mode_fn auto-discharged).
    - Hty = __var / Hsub_gen = __refl_any: mode_ti subcase CLOSED;
      mode_tc / mode_fn admit (need non-mono d_consis refl).
    - Hty = __anno / Hsub_gen = __refl_any: mode_ti subcase CLOSED;
      mode_tc / mode_fn admit (same as __var).
    - Hty = __sub:
      * m = mode_ti: CLOSED for __embed, __refl_any (all 3 modes),
        __arg via helpers [d_consis_sub_trans_gen_nil] composing
        Hsub_orig's d_consis with reconstructed Hsub_gen.
      * m = mode_ti / __forall_r: CLOSED via
        d_consis_sub_trans_gen_nil + d_sub_gen__forall_r
        reconstruction.
      * m = mode_fn _: admit (mode-changing d_sub transitivity is
        research-grade — Hsub_orig is __arg, composition with outer
        Hsub_gen at different mode doesn't go through standard subs).
    - Hty = __app:
      * __embed: CLOSED via function-side lift (paper's central case).
      * __refl_any: CLOSED via d_sub_gen__refl_any at lifted arrow.
      * __forall_r: CLOSED via d_sub_gen__forall_r reconstruction at
        function-side return.
      * __arg: CLOSED via nested d_sub_gen__arg at function side.
    - Hty ∈ {__abs, __abs_anno}:
      * __refl_any: CLOSED for m = mode_fn k, and for m = mode_ti via
        case-split on m_new (mode_ti, mode_tc match orig body mode;
        mode_fn k lifts body via H1/H2 IH with refl_any sub).
      * __forall_r: CLOSED via wiring to
        [d_typing_abs_value_to_forall] /
        [d_typing_abs_anno_value_to_forall] aux lemmas. The aux
        lemmas' __forall_r recursion case is closed by dependent
        induction on the d_sub_gen at the generalised target shape.
        Their internal __embed / __refl_any cases admit due to
        body-lift (mode_ti → mode_tc) circularity.
      * __embed / __arg: admit (research-grade —
        embed needs narrowing on arg type, arg needs both narrowing
        and body subsumption).

    Remaining admits are structurally documented:
    - forall_r at atomic / value Hty cases (var/anno) — partly closed
      via dedicated aux lemmas with localised remaining admits.
    - narrowing (abs/abs_anno + embed/arg).
    - gen→sub bridge (var/anno + arg) — partial conversion.
    - mode-changing d_sub transitivity (sub mode_fn outer).

    Helpers are now fully Qed:
    - [d_consis_to_d_sub_gen]: lift d_consis to d_sub_gen at any
      compatible mode by induction on mode_typ_compat.
    - [d_consis_extends_d_consis_gen]: compose d_consis on LHS with
      d_consis_gen at Δ = nil; uses [d_consis_compose] and resolves
      the permutation via [Permutation Δc nil → Δc = nil].
    - [d_consis_sub_trans_gen_nil]: gen-relation analogue of
      [d_consis_sub_trans_nil]; statement has [T] after [Hs] so
      the [induction Hs] IH abstracts over [T] properly.

    [d_sub_gen__refl_any] requires [mode_typ_compat m A] (def-level
    fix); without this the rule was too permissive (e.g. allowed
    [d_sub_gen (mode_fn _) nil Γ typ_unit typ_unit] whose target
    d_typing is unreachable). *)
Theorem d_typing_general_subsumption_gen : forall m_orig Γ e A,
    d_typing_gen m_orig Γ e A ->
    is_fn_n_ti m_orig ->
    d_wf_denv Γ ->
    forall m_new B,
      d_sub_gen (mode_fn_n_subst m_orig m_new) nil Γ A B ->
      d_typing_gen (mode_fn_n_subst m_orig m_new) Γ e B.
Proof.
  intros m_orig Γ e A Hty.
  induction Hty; intros Hfn Hwfd m_new B_tgt Hsub_gen.
  - (* Hty = __unit (m_orig = mode_ti). Closes via [d_typing_gen__sub]
       directly through [d_typing_unit_gen_subsumption]. *)
    simpl in Hsub_gen |- *.
    apply d_typing_unit_gen_subsumption; assumption.
  - (* Hty = __var (m_orig = mode_ti). *)
    simpl in Hsub_gen |- *.
    eapply d_typing_var_gen_subsumption; eauto.
  - (* Hty = __anno (m_orig = mode_ti). Uses the restated (ctyp-base)
       [d_typing_anno_gen_subsumption]. *)
    simpl in Hsub_gen |- *.
    eapply d_typing_anno_gen_subsumption; eauto.
  - (* Hty = __sub: inner [d_typing_gen mode_ti Γ e A], outer
       [d_sub_gen m_orig A B]. Compose with [Hsub_gen] via
       [d_sub_gen_trans] at [m1 = m_orig]. *)
    apply d_typing_gen__sub with (A := A); auto.
    eapply d_sub_gen_trans with (m1 := m) (B := B); auto.
    eapply d_typing_gen_preserves_wf; eauto.
  - (* Hty = __freeze: m_orig = mode_tc ∉ is_fn_n_ti. Vacuous. *)
    inversion Hfn.
  - (* Hty = __forall: same. *)
    inversion Hfn.
  - (* Hty = __abs (m = m_orig ∈ FN^n TI). Use the SPLIT helper
       [d_typing_abs_value_to_subsumption_split] which takes the body
       binding type and arrow arg as DIFFERENT shapes (binding [A], arrow
       arg [inh_color_t A]). Passing [A := syn_color A0] (the rule's body
       binding type) gives arrow arg [inh_color_t (syn_color A0) =
       inh_color A0], matching Hsub_gen's LHS. The helper handles all
       Hsub_gen sub-cases internally; we only need to wire m_orig sub-cases.

       All m_orig / m_new combinations now closed inline:
         - m_orig = mode_ti, m_new ∈ {mode_ti, mode_tc}: via SPLIT helpers.
         - m_orig = mode_ti, m_new = mode_fn k: inline case-split on
           Hsub_gen ([__embed/__refl_mono/__arg]); inh-LHS rigidity gives
           [A1 = inh_color A] in [__arg].
         - m_orig = mode_fn m': same case-split but body IH is applied at
           [decr_mode m_orig = m'], yielding outer mode [mode_fn (mode_fn_n_subst m' m_new)]. *)
    inversion Hfn; subst.
    + (* m_orig = mode_ti. mode_fn_n_subst mode_ti m_new = m_new. *)
      simpl in Hsub_gen |- *.
      destruct m_new.
      * (* m_new = mode_ti. Wired via [d_typing_abs_value_to_subsumption_split_ti]
           — the mode_ti variant of the SPLIT helper. *)
        assert (HwfsynA' : d_wf_typ Γ (syn_color A))
          by (apply d_wf_typ_inh_color_syn_color; exact H).
        assert (HwfB : d_wf_typ Γ B).
        { pick fresh x for (L `union` dom Γ).
          assert (HwfBx : d_wf_typ ((x ~ dbind_typ (syn_color A)) ++ Γ) B).
          { eapply d_typing_gen_preserves_wf with (m := mode_ti).
            - apply H0. fsetdec.
            - apply d_wf_denv__typ; [assumption | fsetdec | assumption]. }
          rewrite_env (nil ++ (x ~ dbind_typ (syn_color A)) ++ Γ) in HwfBx.
          rewrite_env (nil ++ Γ).
          eapply d_wf_typ_strengthening_typ; eauto. }
        eapply d_typing_abs_value_to_subsumption_split_ti with
          (A := syn_color A) (B := B) (m_orig := mode_ti) (L := L); eauto.
        -- (* d_wf_typ Γ (inh_color_t (syn_color A)) — bridge to H. *)
           rewrite inh_color_t_inh_color_erase.
           rewrite erase_syn_color. exact H.
        -- (* d_sub_gen mode_ti nil Γ (typ_arrow (inh_color_t (syn_color A)) B) B_tgt
              — bridge to Hsub_gen. *)
           rewrite inh_color_t_inh_color_erase.
           rewrite erase_syn_color. exact Hsub_gen.
      * (* m_new = mode_tc. The split helper closes this directly.
           Pass Hbody_at_tc constructed from D12 IH on body (H1) at
           mode_tc, refl on mono B — breaks lift_mono dependency. *)
        assert (HwfsynA' : d_wf_typ Γ (syn_color A))
          by (apply d_wf_typ_inh_color_syn_color; exact H).
        assert (HwfB : d_wf_typ Γ B).
        { pick fresh x for (L `union` dom Γ).
          assert (HwfBx : d_wf_typ ((x ~ dbind_typ (syn_color A)) ++ Γ) B).
          { eapply d_typing_gen_preserves_wf with (m := mode_ti).
            - apply H0. fsetdec.
            - apply d_wf_denv__typ; [assumption | fsetdec | assumption]. }
          rewrite_env (nil ++ (x ~ dbind_typ (syn_color A)) ++ Γ) in HwfBx.
          rewrite_env (nil ++ Γ).
          eapply d_wf_typ_strengthening_typ; eauto. }
        eapply d_typing_abs_value_to_subsumption_split with
          (A := syn_color A) (B := B) (m_orig := mode_ti) (L := L); eauto.
        -- (* d_wf_typ Γ (inh_color_t (syn_color A)) — bridge to H. *)
           rewrite inh_color_t_inh_color_erase.
           rewrite erase_syn_color. exact H.
        -- (* Hbody_at_tc: invoke D12 IH on body (H1) at m_new = mode_tc
              with refl-mono d_sub_gen on B. *)
           intros x Hx Hmono.
           assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ (syn_color A)) ++ Γ))
             by (apply d_wf_denv__typ; [ assumption | fsetdec | assumption ]).
           apply H1 with (m_new := mode_tc) (B := B).
           ++ fsetdec.
           ++ apply is_fn_n_ti__ti.
           ++ assumption.
           ++ simpl. apply d_sub_gen__refl_mono.
              ** assumption.
              ** apply mode_typ_compat__tc. apply mono_typ_is_inh_typ; assumption.
              ** rewrite_env ((x ~ dbind_typ (syn_color A)) ++ Γ).
                 apply d_wf_typ_weakening_head. assumption.
        -- (* d_sub_gen mode_tc nil Γ (typ_arrow (inh_color_t (syn_color A)) B) B_tgt
              — bridge to Hsub_gen. *)
           rewrite inh_color_t_inh_color_erase.
           rewrite erase_syn_color. exact Hsub_gen.
      * (* m_new = mode_fn m_inner. Invert Hsub_gen on its mode_fn rules:
           __embed → d_sub (mode_fn m_inner) (__arg or __forall_l_tagged);
           __refl_mono → target same arrow, mono;
           __arg → target typ_arrow A1 A2 with d_consis_gen on inh-LHS,
                   forcing A1 = inh_color A by [d_consis_gen_lhs_inh_eq]. *)
        rename m_new into m_inner.
        rename H into HwfA.
        rename H0 into Hbody.
        rename H1 into IHbody.
        assert (HsynA : d_wf_typ Γ (syn_color A))
          by (apply d_wf_typ_inh_color_syn_color; assumption).
        assert (HinhA_inh : is_inh_typ (inh_color A))
          by (eapply is_inh_typ_inh_color; eassumption).
        dependent destruction Hsub_gen.
        -- (* __embed: d_sub (mode_fn m_inner) nil Γ (typ_arrow (inh_color A) B) B_tgt.
              Rename the auto-named d_sub hypothesis. *)
           match goal with Hd : d_sub _ _ _ _ _ |- _ => rename Hd into Hd_sub end.
           dependent destruction Hd_sub.
           ++ (* d_sub__arg *)
              match goal with HΔ : _ ++ _ = nil |- _ => rename HΔ into Heq_app end.
              apply app_eq_nil in Heq_app. destruct Heq_app; subst.
              match goal with Hc : d_consis _ _ (inh_color A) _ |- _ => rename Hc into Hcons end.
              match goal with Hs : d_sub _ _ _ B _ |- _ => rename Hs into Hbs end.
              assert (HA1_eq : inh_color A = A1)
                by (eapply d_consis_lhs_inh_eq; eauto).
              subst A1.
              simpl.
              apply d_typing_gen__abs with (L := L `union` dom Γ); auto.
              intros x Hx.
              assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ (syn_color A)) ++ Γ))
                by (apply d_wf_denv__typ; auto; fsetdec).
              match type of Hbs with d_sub _ _ _ _ ?A2_ =>
                apply IHbody with (x := x) (m_new := m_inner) (B := A2_)
              end.
              ** fsetdec.
              ** apply is_fn_n_ti__ti.
              ** assumption.
              ** apply d_sub_gen__embed.
                 rewrite_env (nil ++ (x ~ dbind_typ (syn_color A)) ++ Γ).
                 apply d_sub_weakening; simpl; exact Hbs.
        -- (* __refl_mono: target = typ_arrow (inh_color A) B (unchanged), both arms mono. *)
           match goal with Hm : mono_typ (typ_arrow _ _) |- _ =>
             inversion Hm; subst
           end.
           match goal with Hmc : mode_typ_compat (mode_fn _) (typ_arrow _ _) |- _ =>
             inversion Hmc; subst
           end.
           match goal with Hwa : d_wf_typ Γ (typ_arrow _ _) |- _ =>
             inversion Hwa; subst
           end.
           apply d_typing_gen__abs with (L := L `union` dom Γ); auto.
           intros x Hx.
           assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ (syn_color A)) ++ Γ))
             by (apply d_wf_denv__typ; auto; fsetdec).
           simpl.
           (* Replace lift_mono with IHbody (D12 IH on body) at m_inner,
              refl-mono on B. Body's mode is decr_mode (mode_fn m_inner)
              = m_inner; IHbody at m_new := m_inner gives the lifted body. *)
           apply IHbody with (m_new := m_inner) (B := B).
           ++ fsetdec.
           ++ apply is_fn_n_ti__ti.
           ++ exact Hwfd_x.
           ++ simpl. apply d_sub_gen__refl_mono; auto.
              rewrite_env ((x ~ dbind_typ (syn_color A)) ++ Γ).
              apply d_wf_typ_weakening_head. assumption.
        -- (* __arg: B_tgt = typ_arrow A1 A2 with d_consis_gen + d_sub_gen. *)
           match goal with HΔ : _ ++ _ = nil |- _ => rename HΔ into Heq_app end.
           apply app_eq_nil in Heq_app. destruct Heq_app; subst.
           match goal with Hcg : d_consis_gen _ _ (inh_color A) _ |- _ => rename Hcg into Hcons end.
           match goal with Hs : d_sub_gen _ _ _ B _ |- _ => rename Hs into Hbs end.
           assert (HA1_eq : inh_color A = _) by (eapply d_consis_gen_lhs_inh_eq; eauto).
           match type of HA1_eq with inh_color A = ?A1 => subst A1 end.
           simpl.
           apply d_typing_gen__abs with (L := L `union` dom Γ); auto.
           intros x Hx.
           assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ (syn_color A)) ++ Γ))
             by (apply d_wf_denv__typ; auto; fsetdec).
           match type of Hbs with d_sub_gen _ _ _ _ ?A2_ =>
             apply IHbody with (x := x) (m_new := m_inner) (B := A2_)
           end.
           ++ fsetdec.
           ++ apply is_fn_n_ti__ti.
           ++ assumption.
           ++ rewrite_env ((x ~ dbind_typ (syn_color A)) ++ Γ).
              apply d_sub_gen_weakening_head; exact Hbs.
    + (* m_orig = mode_fn m'. Outer mode is [mode_fn (mode_fn_n_subst m' m_new)];
         same case-split on Hsub_gen as the m_orig=mode_ti case, but the
         body IH lifts at mode m' (decr_mode (mode_fn m') = m'), and the
         [is_fn_n_ti] premise to IHbody is the [is_fn_n_ti m'] from
         inverting Hfn. *)
      match goal with Hfn_m' : is_fn_n_ti _ |- _ => rename Hfn_m' into Hfn_inner end.
      simpl in Hsub_gen |- *.
      rename H into HwfA.
      rename H0 into Hbody.
      rename H1 into IHbody.
      assert (HsynA : d_wf_typ Γ (syn_color A))
        by (apply d_wf_typ_inh_color_syn_color; assumption).
      assert (HinhA_inh : is_inh_typ (inh_color A))
        by (eapply is_inh_typ_inh_color; eassumption).
      rename m0 into m'.
      dependent destruction Hsub_gen.
      * (* __embed: d_sub (mode_fn (mode_fn_n_subst m' m_new)) nil Γ ... *)
        match goal with Hd : d_sub _ _ _ _ _ |- _ => rename Hd into Hd_sub end.
        dependent destruction Hd_sub.
        -- (* d_sub__arg *)
           match goal with HΔ : _ ++ _ = nil |- _ => rename HΔ into Heq_app end.
           apply app_eq_nil in Heq_app. destruct Heq_app; subst.
           match goal with Hc : d_consis _ _ (inh_color A) _ |- _ => rename Hc into Hcons end.
           match goal with Hs : d_sub _ _ _ B _ |- _ => rename Hs into Hbs end.
           assert (HA1_eq : inh_color A = _) by (eapply d_consis_lhs_inh_eq; eauto).
           match type of HA1_eq with inh_color A = ?A1 => subst A1 end.
           simpl.
           apply d_typing_gen__abs with (L := L `union` dom Γ); auto.
           intros x Hx.
           assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ (syn_color A)) ++ Γ))
             by (apply d_wf_denv__typ; auto; fsetdec).
           match type of Hbs with d_sub _ _ _ _ ?A2_ =>
             apply IHbody with (x := x) (m_new := m_new) (B := A2_)
           end.
           ** fsetdec.
           ** exact Hfn_inner.
           ** assumption.
           ** apply d_sub_gen__embed.
              rewrite_env (nil ++ (x ~ dbind_typ (syn_color A)) ++ Γ).
              apply d_sub_weakening; simpl. exact Hbs.
      * (* __refl_mono *)
        match goal with Hm : mono_typ (typ_arrow _ _) |- _ =>
          inversion Hm; subst
        end.
        match goal with Hmc : mode_typ_compat (mode_fn _) (typ_arrow _ _) |- _ =>
          inversion Hmc; subst
        end.
        match goal with Hwa : d_wf_typ Γ (typ_arrow _ _) |- _ =>
          inversion Hwa; subst
        end.
        apply d_typing_gen__abs with (L := L `union` dom Γ); auto.
        intros x Hx.
        assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ (syn_color A)) ++ Γ))
          by (apply d_wf_denv__typ; auto; fsetdec).
        simpl.
        apply IHbody with (x := x) (m_new := m_new) (B := B).
        -- fsetdec.
        -- exact Hfn_inner.
        -- assumption.
        -- apply d_sub_gen_refl; auto.
           rewrite_env ((x ~ dbind_typ (syn_color A)) ++ Γ).
           apply d_wf_typ_weakening_head. assumption.
      * (* __arg *)
        match goal with HΔ : _ ++ _ = nil |- _ => rename HΔ into Heq_app end.
        apply app_eq_nil in Heq_app. destruct Heq_app; subst.
        match goal with Hcg : d_consis_gen _ _ (inh_color A) _ |- _ => rename Hcg into Hcons end.
        match goal with Hs : d_sub_gen _ _ _ B _ |- _ => rename Hs into Hbs end.
        assert (HA1_eq : inh_color A = _) by (eapply d_consis_gen_lhs_inh_eq; eauto).
        match type of HA1_eq with inh_color A = ?A1 => subst A1 end.
        simpl.
        apply d_typing_gen__abs with (L := L `union` dom Γ); auto.
        intros x Hx.
        assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ (syn_color A)) ++ Γ))
          by (apply d_wf_denv__typ; auto; fsetdec).
        match type of Hbs with d_sub_gen _ _ _ _ ?A2_ =>
          apply IHbody with (x := x) (m_new := m_new) (B := A2_)
        end.
        -- fsetdec.
        -- exact Hfn_inner.
        -- assumption.
        -- rewrite_env ((x ~ dbind_typ (syn_color A)) ++ Γ).
           apply d_sub_gen_weakening_head. exact Hbs.
  - (* Hty = __abs_anno. Parallel to __abs: use the SPLIT helper
       [d_typing_abs_anno_value_to_subsumption_split] whose conclusion
       term [exp_abs_anno (inh_color_t A_helper) e] matches the rule's
       term [exp_abs_anno (inh_color A0) e] for A_helper = syn_color A0
       (since inh_color_t (syn_color A0) = inh_color A0). *)
    inversion Hfn; subst.
    + (* m_orig = mode_ti. *)
      simpl in Hsub_gen |- *.
      destruct m_new.
      * (* m_new = mode_ti. Use the abs_anno_split_ti helper. *)
        assert (HwfB : d_wf_typ Γ B).
        { pick fresh x for (L `union` dom Γ).
          assert (HwfBx : d_wf_typ ((x ~ dbind_typ (syn_color A)) ++ Γ) B).
          { eapply d_typing_gen_preserves_wf with (m := mode_ti).
            - apply H0. fsetdec.
            - apply d_wf_denv__typ; [assumption | fsetdec | assumption]. }
          rewrite_env (nil ++ (x ~ dbind_typ (syn_color A)) ++ Γ) in HwfBx.
          rewrite_env (nil ++ Γ).
          eapply d_wf_typ_strengthening_typ; eauto. }
        replace (exp_abs_anno (inh_color A) e)
          with (exp_abs_anno (inh_color_t (syn_color A)) e)
          by (rewrite inh_color_t_inh_color_erase;
              rewrite erase_syn_color; reflexivity).
        eapply d_typing_abs_anno_value_to_subsumption_split_ti with
          (A := syn_color A) (B := B) (m_orig := mode_ti) (L := L); eauto.
      * (* m_new = mode_tc. *)
        replace (exp_abs_anno (inh_color A) e)
          with (exp_abs_anno (inh_color_t (syn_color A)) e)
          by (rewrite inh_color_t_inh_color_erase;
              rewrite erase_syn_color; reflexivity).
        assert (HwfB : d_wf_typ Γ B).
        { pick fresh x for (L `union` dom Γ).
          assert (HwfBx : d_wf_typ ((x ~ dbind_typ (syn_color A)) ++ Γ) B).
          { eapply d_typing_gen_preserves_wf with (m := mode_ti).
            - apply H0. fsetdec.
            - apply d_wf_denv__typ; [assumption | fsetdec | assumption]. }
          rewrite_env (nil ++ (x ~ dbind_typ (syn_color A)) ++ Γ) in HwfBx.
          rewrite_env (nil ++ Γ).
          eapply d_wf_typ_strengthening_typ; eauto. }
        eapply d_typing_abs_anno_value_to_subsumption_split with
          (A := syn_color A) (B := B) (m_orig := mode_ti) (L := L); eauto.
        (* Hbody_at_tc: invoke D12 IH on body (H1) at m_new = mode_tc
           with refl-mono d_sub_gen on B. *)
        intros x Hx Hmono.
        assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ (syn_color A)) ++ Γ))
          by (apply d_wf_denv__typ; [ assumption | fsetdec | assumption ]).
        apply H1 with (m_new := mode_tc) (B := B).
        -- fsetdec.
        -- apply is_fn_n_ti__ti.
        -- exact Hwfd_x.
        -- simpl. apply d_sub_gen__refl_mono.
           ++ assumption.
           ++ apply mode_typ_compat__tc. apply mono_typ_is_inh_typ; assumption.
           ++ rewrite_env ((x ~ dbind_typ (syn_color A)) ++ Γ).
              apply d_wf_typ_weakening_head. assumption.
      * (* m_new = mode_fn m_inner. Mirror of __abs case at mode_fn.
           Conclusion arrow-arg is [syn_color A] (not [inh_color A] like
           __abs), so we use [d_consis_gen_lhs_syn_eq] in the __arg case. *)
        rename m_new into m_inner.
        rename H into HwfA.
        rename H0 into Hbody.
        rename H1 into IHbody.
        assert (HsynA_syn : is_syn_typ (syn_color A))
          by (eapply is_syn_typ_syn_color; eassumption).
        dependent destruction Hsub_gen.
        -- (* __embed: d_sub (mode_fn m_inner) nil Γ (typ_arrow (syn_color A) B) B_tgt. *)
           match goal with Hd : d_sub _ _ _ _ _ |- _ => rename Hd into Hd_sub end.
           dependent destruction Hd_sub.
           ++ (* d_sub__arg *)
              match goal with HΔ : _ ++ _ = nil |- _ => rename HΔ into Heq_app end.
              apply app_eq_nil in Heq_app. destruct Heq_app; subst.
              match goal with Hc : d_consis _ _ (syn_color A) _ |- _ => rename Hc into Hcons end.
              match goal with Hs : d_sub _ _ _ B _ |- _ => rename Hs into Hbs end.
              assert (HA1_eq : syn_color A = _) by (eapply d_consis_lhs_syn_eq; eauto).
              match type of HA1_eq with syn_color A = ?A1 => subst A1 end.
              simpl.
              apply d_typing_gen__abs_anno with (L := L `union` dom Γ); auto.
              intros x Hx.
              assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ (syn_color A)) ++ Γ))
                by (apply d_wf_denv__typ; auto; fsetdec).
              match type of Hbs with d_sub _ _ _ _ ?A2_ =>
                apply IHbody with (x := x) (m_new := m_inner) (B := A2_)
              end.
              ** fsetdec.
              ** apply is_fn_n_ti__ti.
              ** assumption.
              ** apply d_sub_gen__embed.
                 rewrite_env (nil ++ (x ~ dbind_typ (syn_color A)) ++ Γ).
                 apply d_sub_weakening; simpl; exact Hbs.
        -- (* __refl_mono: target = typ_arrow (syn_color A) B (unchanged), both arms mono. *)
           match goal with Hm : mono_typ (typ_arrow _ _) |- _ =>
             inversion Hm; subst
           end.
           match goal with Hmc : mode_typ_compat (mode_fn _) (typ_arrow _ _) |- _ =>
             inversion Hmc; subst
           end.
           match goal with Hwa : d_wf_typ Γ (typ_arrow _ _) |- _ =>
             inversion Hwa; subst
           end.
           apply d_typing_gen__abs_anno with (L := L `union` dom Γ); auto.
           intros x Hx.
           assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ (syn_color A)) ++ Γ))
             by (apply d_wf_denv__typ; auto; fsetdec).
           simpl.
           (* Replace lift_mono with IHbody (D12 IH on body) at m_inner. *)
           apply IHbody with (m_new := m_inner) (B := B).
           ++ fsetdec.
           ++ apply is_fn_n_ti__ti.
           ++ exact Hwfd_x.
           ++ simpl. apply d_sub_gen__refl_mono; auto.
              rewrite_env ((x ~ dbind_typ (syn_color A)) ++ Γ).
              apply d_wf_typ_weakening_head. assumption.
        -- (* __arg: B_tgt = typ_arrow A1 A2 with d_consis_gen + d_sub_gen. *)
           match goal with HΔ : _ ++ _ = nil |- _ => rename HΔ into Heq_app end.
           apply app_eq_nil in Heq_app. destruct Heq_app; subst.
           match goal with Hcg : d_consis_gen _ _ (syn_color A) _ |- _ => rename Hcg into Hcons end.
           match goal with Hs : d_sub_gen _ _ _ B _ |- _ => rename Hs into Hbs end.
           assert (HA1_eq : syn_color A = _) by (eapply d_consis_gen_lhs_syn_eq; eauto).
           match type of HA1_eq with syn_color A = ?A1 => subst A1 end.
           simpl.
           apply d_typing_gen__abs_anno with (L := L `union` dom Γ); auto.
           intros x Hx.
           assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ (syn_color A)) ++ Γ))
             by (apply d_wf_denv__typ; auto; fsetdec).
           match type of Hbs with d_sub_gen _ _ _ _ ?A2_ =>
             apply IHbody with (x := x) (m_new := m_inner) (B := A2_)
           end.
           ++ fsetdec.
           ++ apply is_fn_n_ti__ti.
           ++ assumption.
           ++ rewrite_env ((x ~ dbind_typ (syn_color A)) ++ Γ).
              apply d_sub_gen_weakening_head; exact Hbs.
    + (* m_orig = mode_fn m'. Mirror of __abs (m_orig=mode_fn m') but
         arrow-arg is [syn_color A], using [d_consis_gen_lhs_syn_eq]. *)
      match goal with Hfn_m' : is_fn_n_ti _ |- _ => rename Hfn_m' into Hfn_inner end.
      simpl in Hsub_gen |- *.
      rename H into HwfA.
      rename H0 into Hbody.
      rename H1 into IHbody.
      assert (HsynA_syn : is_syn_typ (syn_color A))
        by (eapply is_syn_typ_syn_color; eassumption).
      rename m0 into m'.
      dependent destruction Hsub_gen.
      * (* __embed *)
        match goal with Hd : d_sub _ _ _ _ _ |- _ => rename Hd into Hd_sub end.
        dependent destruction Hd_sub.
        -- (* d_sub__arg *)
           match goal with HΔ : _ ++ _ = nil |- _ => rename HΔ into Heq_app end.
           apply app_eq_nil in Heq_app. destruct Heq_app; subst.
           match goal with Hc : d_consis _ _ (syn_color A) _ |- _ => rename Hc into Hcons end.
           match goal with Hs : d_sub _ _ _ B _ |- _ => rename Hs into Hbs end.
           assert (HA1_eq : syn_color A = _) by (eapply d_consis_lhs_syn_eq; eauto).
           match type of HA1_eq with syn_color A = ?A1 => subst A1 end.
           simpl.
           apply d_typing_gen__abs_anno with (L := L `union` dom Γ); auto.
           intros x Hx.
           assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ (syn_color A)) ++ Γ))
             by (apply d_wf_denv__typ; auto; fsetdec).
           match type of Hbs with d_sub _ _ _ _ ?A2_ =>
             apply IHbody with (x := x) (m_new := m_new) (B := A2_)
           end.
           ** fsetdec.
           ** exact Hfn_inner.
           ** assumption.
           ** apply d_sub_gen__embed.
              rewrite_env (nil ++ (x ~ dbind_typ (syn_color A)) ++ Γ).
              apply d_sub_weakening; simpl; exact Hbs.
      * (* __refl_mono *)
        match goal with Hm : mono_typ (typ_arrow _ _) |- _ =>
          inversion Hm; subst
        end.
        match goal with Hmc : mode_typ_compat (mode_fn _) (typ_arrow _ _) |- _ =>
          inversion Hmc; subst
        end.
        match goal with Hwa : d_wf_typ Γ (typ_arrow _ _) |- _ =>
          inversion Hwa; subst
        end.
        apply d_typing_gen__abs_anno with (L := L `union` dom Γ); auto.
        intros x Hx.
        assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ (syn_color A)) ++ Γ))
          by (apply d_wf_denv__typ; auto; fsetdec).
        simpl.
        apply IHbody with (x := x) (m_new := m_new) (B := B).
        -- fsetdec.
        -- exact Hfn_inner.
        -- assumption.
        -- apply d_sub_gen_refl; auto.
           rewrite_env ((x ~ dbind_typ (syn_color A)) ++ Γ).
           apply d_wf_typ_weakening_head. assumption.
      * (* __arg *)
        match goal with HΔ : _ ++ _ = nil |- _ => rename HΔ into Heq_app end.
        apply app_eq_nil in Heq_app. destruct Heq_app; subst.
        match goal with Hcg : d_consis_gen _ _ (syn_color A) _ |- _ => rename Hcg into Hcons end.
        match goal with Hs : d_sub_gen _ _ _ B _ |- _ => rename Hs into Hbs end.
        assert (HA1_eq : syn_color A = _) by (eapply d_consis_gen_lhs_syn_eq; eauto).
        match type of HA1_eq with syn_color A = ?A1 => subst A1 end.
        simpl.
        apply d_typing_gen__abs_anno with (L := L `union` dom Γ); auto.
        intros x Hx.
        assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ (syn_color A)) ++ Γ))
          by (apply d_wf_denv__typ; auto; fsetdec).
        match type of Hbs with d_sub_gen _ _ _ _ ?A2_ =>
          apply IHbody with (x := x) (m_new := m_new) (B := A2_)
        end.
        -- fsetdec.
        -- exact Hfn_inner.
        -- assumption.
        -- rewrite_env ((x ~ dbind_typ (syn_color A)) ++ Γ).
           apply d_sub_gen_weakening_head. exact Hbs.
  - (* Hty = __app. Closing this requires lifting the function-side
       sub-derivation H1 (at mode_fn m_orig) to mode_fn m_new via the
       IH (D12 on H1), composing with d_sub_gen__arg using:
       - d_consis_gen_refl_is_typ on P' (the function-arg type)
       - Hsub_gen on the result side.
       Then reconstruct __app at outer mode m_new. *)
    inversion Hfn; subst.
    + (* m_orig = mode_ti. mode_fn_n_subst mode_ti m_new = m_new. *)
      simpl in Hsub_gen |- *.
      (* Derive d_wf_typ Γ P' from d_typing_gen_preserves_wf on the
         function-side hypothesis Hty1 (renamed via match goal since the
         auto-named hypothesis may differ across cases). *)
      assert (HwfP' : d_wf_typ Γ P').
      { (* All four __app premises are in context; the function-side
           one has type d_typing_gen _ Γ _ (typ_arrow P' _). Pin it by
           inspecting d_typing_gen at the function expression e1. *)
        match goal with
        | Hfun : d_typing_gen _ _ e1 _ |- _ =>
            pose proof (d_typing_gen_preserves_wf Hfun Hwfd) as HwfArr
        end.
        inversion HwfArr; subst; assumption. }
      assert (HistypP' : is_typ P')
        by (eapply d_wf_typ_is_typ; eassumption).
      eapply d_typing_gen__app with (P := P) (P' := P').
      * exact H.
      * exact H0.
      * (* d_typing_gen (mode_fn m_new) Γ e1 (typ_arrow P' B_tgt).
           Lift H1 via IHHty1 (= D12 on H1). *)
        eapply IHHty1 with (m_new := m_new) (B := typ_arrow P' B_tgt); auto.
        -- apply is_fn_n_ti__fn. apply is_fn_n_ti__ti.
        -- (* d_sub_gen (mode_fn m_new) nil Γ (typ_arrow P' B) (typ_arrow P' B_tgt). *)
           rewrite_env (@nil atom ++ @nil atom).
           apply d_sub_gen__arg.
           ++ (* d_consis_gen nil Γ P' P' (refl). Use d_consis_gen_refl_is_typ;
                facts derived above from H1 + wf preservation. *)
              apply d_consis_gen_refl_is_typ; assumption.
           ++ exact Hsub_gen.
      * (* d_typing_gen mode_tc Γ e2 (inh_color (erase P')) — unchanged. *)
        match goal with
        | Harg : d_typing_gen mode_tc _ _ (inh_color (erase _)) |- _ => exact Harg
        end.
    + (* m_orig = mode_fn m'. Parallel to mode_ti case: lift function via
         IH, reconstruct __app at outer (mode_fn_n_subst m' m_new). *)
      simpl in Hsub_gen |- *.
      assert (HwfP' : d_wf_typ Γ P').
      { match goal with
        | Hfun : d_typing_gen _ _ e1 _ |- _ =>
            pose proof (d_typing_gen_preserves_wf Hfun Hwfd) as HwfArr
        end.
        inversion HwfArr; subst; assumption. }
      assert (HistypP' : is_typ P')
        by (eapply d_wf_typ_is_typ; eassumption).
      eapply d_typing_gen__app with (P := P) (P' := P').
      * exact H.
      * exact H0.
      * (* d_typing_gen (mode_fn (mode_fn_n_subst m m_new)) Γ e1
           (typ_arrow P' B_tgt). Lift via IHHty1 at m_new. *)
        eapply IHHty1 with (m_new := m_new) (B := typ_arrow P' B_tgt); auto.
        -- apply is_fn_n_ti__fn. apply is_fn_n_ti__fn. assumption.
        -- (* d_sub_gen (mode_fn (mode_fn (mode_fn_n_subst m m_new))) ...
              Need __arg again. *)
           simpl. rewrite_env (@nil atom ++ @nil atom).
           apply d_sub_gen__arg.
           ++ apply d_consis_gen_refl_is_typ; assumption.
           ++ exact Hsub_gen.
      * match goal with
        | Harg : d_typing_gen mode_tc _ _ (inh_color (erase _)) |- _ => exact Harg
        end.
Qed.

(** [d_consis_gen_to_d_consis_syn_lhs]: the SYN-LHS-restricted bridge,
    Qed. When the LHS is [is_syn_typ] (every quantifier is [colour_syn]),
    the [__forall_inh] case (LHS = [typ_all_col colour_inh]) is vacuous,
    so the bridge closes. Used internally by the [d_sub_gen → d_sub]
    bridge for [__infer_gen] / [__check_gen] (where the LHS is
    [syn_color T_base], hence [is_syn_typ]); kept as a standalone Qed
    helper for future work that can establish [is_syn_typ] at the call
    site. *)
Lemma d_consis_gen_to_d_consis_syn_lhs : forall T,
    is_syn_typ T ->
    forall Δ Γ A, d_consis_gen Δ Γ T A -> d_consis Δ Γ T A.
Proof.
  intros T Hsyn. induction Hsyn; intros Δ Γ A0 Hc.
  - (* typ_unit *) inversion Hc; subst. apply d_consis__unit.
  - (* typ_var_f X *) inversion Hc; subst. apply d_consis__var; assumption.
  - (* typ_arrow *)
    inversion Hc; subst.
    apply d_consis__arrow; auto.
  - (* typ_all_col colour_syn (post-refactor): d_consis_gen admits two
       rules with this LHS — __forall_syn (RHS colour_syn) and the new
       __forall_inh_untagged (RHS colour_inh). Both bridge to their
       d_consis counterparts via the IH on the opened body. *)
    inversion Hc; subst.
    + (* __forall_inh_untagged (NEW δ-rule) *)
      apply d_consis__forall_inh_untagged with (L := L `union` L0).
      intros X HX. apply H0; auto.
    + (* __forall_syn *)
      apply d_consis__forall_syn with (L := L `union` L0).
      intros X HX. apply H0; auto.
Qed.

(** [d_consis_gen_to_d_consis]: the gen→original bridge for
    consistency. Fully [Qed] post the structural fix.

    The fix: added [d_consis__forall_inh] to the base [d_consis]
    inductive (paper-faithful — paper's [typconsis] in
    [syntax-directed.tex:116] includes a structural [ForallInh] rule
    admitting [inh{∀α.}T] on the LHS). The cascading impact (transitivity,
    narrowing, weakening, mono-extraction) was absorbed in this pass:
    [d_consis_compose] gains 3 cofinite-rename cases (Paper Lemma B.2 /
    Consistency Transitivity);
    [d_consis_LHS_mono_wf] gains an [is_utyp T] precondition (rules out
    the new [typ_all_col colour_inh] LHS case which is wf but not mono);
    [d_consis_LHS_is_typ_mono] gets the same precondition;
    [d_consis_mono_RHS] / [d_consis_LHS_syn_color_mono] /
    [d_consis_compose_nil_RHS] / [d_consis_empty_eq] /
    [d_sub_not_lhs_typ_all_col] / [d_sub_LHS_mono_wf] each gain a
    case for the new constructor. *)
Lemma d_consis_gen_to_d_consis : forall Δ Γ T A,
    d_consis_gen Δ Γ T A ->
    Δ ⨟ Γ ⊨ T ≈ A.
Proof.
  intros Δ Γ T A H. induction H.
  - apply d_consis__unit.
  - apply d_consis__var; assumption.
  - apply d_consis__forall_inh_tagged with (L := L); assumption.
  - (* __forall_inh_untagged (NEW δ-rule): LHS typ_all_col colour_syn,
       RHS typ_all_col colour_inh. Mirrors the tagged case but on the
       untagged-syn LHS. *)
    apply d_consis__forall_inh_untagged with (L := L); assumption.
  - apply d_consis__forall_syn_tagged with (L := L); assumption.
  - apply d_consis__forall_syn with (L := L); assumption.
  - (* __forall_inh: LHS = typ_all_col colour_inh T, RHS =
       typ_all_col colour_inh A. With the new [d_consis__forall_inh]
       rule (added to the base [d_consis] in this pass), this case
       closes directly. *)
    apply d_consis__forall_inh with (L := L); assumption.
  - apply d_consis__arrow; assumption.
Qed.

(** [d_sub_gen_to_d_sub]: the [d_sub_gen → d_sub] bridge.

    Closed structurally for every rule shape using [d_consis_gen_to_d_consis]
    as the consistency-level bridge. The bridge's only admit is the
    [__forall_inh] case of [d_consis_gen_to_d_consis] — that admit
    propagates here implicitly via the [d_consis_gen → d_consis] calls in
    [__infer_gen], [__check_gen], and [__arg]; this lemma itself is [Qed]. *)
Lemma d_sub_gen_to_d_sub : forall m Δ Γ T A,
    d_sub_gen m Δ Γ T A ->
    Γ ⊢[ m ; Δ ] T ⊑ A.
Proof.
  intros m Δ Γ T A H. induction H.
  - (* __embed: trivial — the embed already carries a [d_sub]. *)
    assumption.
  - (* __infer_gen: rebuild [d_sub__infer] after [d_consis_gen → d_consis]
       bridge on the consistency premise. The bridge's residual admit
       case ([__forall_inh] LHS = [typ_all_col colour_inh]) is vacuous
       here because the LHS is [syn_color T], which never matches that
       shape, but the bridge lemma's signature doesn't expose this — so
       this clause is conservative w.r.t. the documented admit. *)
    apply d_sub__infer. apply d_consis_gen_to_d_consis. assumption.
  - (* __check_gen: same pattern; LHS [syn_color T] makes the bridge's
       residual admit case vacuous in practice. *)
    apply d_sub__check; auto. apply d_consis_gen_to_d_consis. assumption.
  - (* __refl_mono: route through [d_sub_refl_mono_mode] (Qed at d_sub
       level). *)
    apply d_sub_refl_mono_mode; auto.
  - (* __forall_r: structural — re-apply [d_sub__forall_r] with the
       cofinite-quant body lifted by the IH. *)
    apply d_sub__forall_r with (L := L); auto.
  - (* __arg: the ONLY case where the residual [d_consis_gen_to_d_consis
       __forall_inh] admit is structurally reachable. The d_consis_gen
       LHS [T1] is arbitrary here (it's the function's argument-type
       from the outer subtyping); when [T1 = typ_all_col colour_inh ...]
       the bridge's __forall_inh case fires. *)
    apply d_sub__arg; auto. apply d_consis_gen_to_d_consis. assumption.
Qed.

(** [d_typing_gen_collapse]: the generalised typing collapses back to
    the original. Structural except [__sub], which routes through the
    [d_sub_gen → d_sub] bridge ([d_sub_gen_to_d_sub] above). The whole
    D1-via-D12 development is therefore closed *modulo the single admit*
    in [d_consis_gen_to_d_consis]'s [__forall_inh] case. *)
Lemma d_typing_gen_collapse : forall m Γ e A,
    d_typing_gen m Γ e A ->
    Γ ⊢[ m ] e ⇒ A.
Proof.
  intros m Γ e A H. induction H.
  - apply d_typing__unit; assumption.
  - apply d_typing__var; assumption.
  - apply d_typing__anno; assumption.
  - (* __sub: close via [d_sub_gen_to_d_sub] bridge. The bridge's
       residual admit ([d_consis_gen_to_d_consis __forall_inh]) is the
       single structural gap of the D1-via-D12 development. *)
    apply d_typing__sub with (A := A); auto.
    apply d_sub_gen_to_d_sub; assumption.
  - apply d_typing__freeze; assumption.
  - apply d_typing__forall with (L := L); assumption.
  - apply d_typing__abs with (L := L); assumption.
  - apply d_typing__abs_anno with (L := L); assumption.
  - apply d_typing__app with (P := P) (P' := P'); assumption.
Qed.

(** [d_typing_general_subsumption_via_gen]: paper Lemma 3.1 (D1), as
    a one-line corollary of D12 ([d_typing_general_subsumption_gen])
    at [m_orig := mode_ti], threading the original [d_sub] in via
    [d_sub_gen__embed]. Stays [Admitted] because the body of D12
    is itself [Admitted] post-re-encoding, and the [d_typing_gen]
    collapse bottoms at the [d_consis_gen_to_d_consis] [__forall_inh]
    structural gap. Restored here as documentation of the intended
    bridge. *)
Theorem d_typing_general_subsumption_via_gen : forall Γ e A B m,
    d_wf_denv Γ ->
    Γ ⊢[ mode_ti ] e ⇒ A ->
    Γ ⊢[ m ; nil ] A ⊑ B ->
    Γ ⊢[ m ] e ⇒ B.
Proof.
  intros Γ e A B m Hwfd Hty Hsub.
  apply d_typing_gen_collapse.
  change m with (mode_fn_n_subst mode_ti m).
  apply d_typing_general_subsumption_gen with (A := A); auto.
  - apply d_typing_embed_gen; assumption.
  - apply is_fn_n_ti__ti.
  - simpl. apply d_sub_gen__embed. exact Hsub.
Qed.
