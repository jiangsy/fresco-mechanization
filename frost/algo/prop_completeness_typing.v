(** COMPLETENESS OF TYPE INFERENCE (section D, thm:complete-type-inference)
    — the landing file for theorem 4 and its kit.

    So far: [a_typing_rename_tm], theorem 4's K6 — the binder rows of
    [a_typing] are cofinite in the term variable and share their outputs
    across the family, so completeness must generate the family from the
    IH's one fresh instance.  Same HYBRID as [a_pat_rename_tm]
    (prop_completeness_pat.v): SWAP the type-level data, SUBSTITUTE in the
    term.

    ⭐ MEASURE SETTLED (2026-08-07 scouting): plain STRUCTURAL induction on
    [ad_sd_typing] suffices — NO height mirror [ad_sd_typing_n].  Every IH
    application in the paper's proof (proofs.tex:617-1395) is on a direct
    premise derivation, and the force that broke structural induction in
    theorem 3 — the binder entry being only ⪯-related to the rule's, needing
    [ad_ctx_precise_pat] on the DERIVATION — has no typing analogue:
    [a_inc__var] relates term entries up to [≡ᵗ] BY RULE (def_meta.v), which
    absorbs exactly the [θ''A' ≡ᵗ A] discrepancy the binder cases produce
    ("precision on types is equivalence", literally).  The [_step] rows'
    same-term recursion only kills [size_exp], which is not needed.

    The statement is [typ_complete_concl] below, factored like
    [pat_complete_concl]; the base rows feed [a_sub_complete_thm] at TY,
    with the run's output packaged as a painted [ptyp] by
    [a_sub_ty_ghost_free_output] (prop_ty_core.v) and the optimality
    conclusion converted by [ad_precise_painting_tyequiv]'s idiom (a
    precision between two type paintings IS a type equivalence, via
    [ad_refine_syn_inh_tyequiv]).

    ⛔ Still owed: the Var/Anno base rows (Anno consumes prop_ty_core's
    [a_typing_tc_rigid_output]), Freeze, the binder rows (term-binder
    family via [a_typing_rename_tm]; the two tvar-[_step] rows need a
    tvar family generation), App (invokes THEOREM 3), the glue, and
    §6.3's #2/#3 rule-level obligations. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_extra.
Require Import src.frost.ltac_utils.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.decorated_algo.def_decorated.
Require Import src.frost.decorated_algo.def_decl_algo.
Require Import src.frost.decorated_algo.def_decl_algo_sub.
Require Import src.frost.decorated_algo.def_decl_algo_sub_hyg.
Require Import src.frost.decorated_algo.def_decl_algo_typing.
Require Import src.frost.decorated_algo.prop_ctx_mono.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_metasubst.
Require Import src.frost.algo.prop_inc_strengthen.
Require Import src.frost.algo.prop_compose.
Require Import src.frost.decorated_algo.prop_decorate.
Require Import src.frost.algo.prop_sub_msubst_equiv.
Require Import src.frost.algo.prop_swap.
Require Import src.frost.algo.prop_completeness_sub_gen.
Require Import src.frost.algo.prop_completeness_sub.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_completeness_consis.
Require Import src.frost.algo.prop_precise.
Require Import src.frost.algo.prop_consis_rename.
Require Import src.frost.algo.prop_soundness_consis.
Require Import src.frost.algo.prop_wf_output.
Require Import src.frost.algo.prop_normal.

Set Implicit Arguments.
Require Import src.frost.algo.prop_soundness_sub.
Require Import src.frost.algo.prop_soundness_pat.
Require Import src.frost.algo.prop_suffix_erase.
Require Import src.frost.algo.prop_soundness_typing.
Require Import src.frost.algo.prop_precise_sub.
Require Import src.frost.algo.prop_completeness_pat.
Require Import src.frost.algo.prop_ty_core.

(* ===================================================================== *)
(*  Theorem 4's K6 — [a_typing]'s own term renaming, the same HYBRID as   *)
(*  [a_pat_rename_tm]: SWAP the type-level data, SUBSTITUTE in the term.  *)
(*  The four check rows' TYPE-variable families swap by the bijection     *)
(*  ([swap_atoms] avoid-set, instance at the preimage), their Barendregt  *)
(*  side conditions transport pointwise.                                  *)
(* ===================================================================== *)

Lemma a_typing_rename_tm : forall a b m Θ0 P0 e A Θ1,
  Θ0 ⊢ₐ[ m ; P0 ] e ⦂ A ⊣ Θ1 ->
  a `notin` ftvar_in_exp e -> b `notin` ftvar_in_exp e ->
  b `notin` fvar_in_exp e ->
  a_typing m (swap_aenv a b Θ0) (swap_pskl a b P0)
    (subst_exp_in_exp (exp_var_f b) a e) (swap_ptyp a b A)
    (swap_aenv a b Θ1).
Proof.
  intros a b m Θ0 P0 e A Θ1 H.
  induction H; intros Ha Hb Hbv;
    simpl in Ha, Hb, Hbv; cbn [subst_exp_in_exp].
  - (* unit *)
    apply a_typing__unit.
    pose proof (proj1 (a_sub_sub_flex_swap a b) _ _ _ _ _ _ _ H) as h.
    rewrite swap_pskl_ptyp_to_pskl in h.
    exact h.
  - (* var *)
    pose proof (proj1 (a_sub_sub_flex_swap a b) _ _ _ _ _ _ _ H0) as hsub.
    rewrite !swap_pskl_ptyp_to_pskl in hsub.
    pose proof (swap_aenv_binds a b _ _ _ H) as hb.
    cbn [swap_abind] in hb.
    destruct_if as [Heq | Hne].
    + subst x. rewrite swap_atom_l in hb.
      eapply a_typing__var; [ exact hb | exact hsub ].
    + assert (Hxb : x <> b) by (intros ->; clear - Hbv; fsetdec).
      rewrite (swap_atom_other a b x Hne Hxb) in hb.
      eapply a_typing__var; [ exact hb | exact hsub ].
  - (* anno *)
    pose proof (proj1 (a_sub_sub_flex_swap a b) _ _ _ _ _ _ _ H0) as hsub.
    rewrite !swap_pskl_ptyp_to_pskl in hsub.
    rewrite (swap_ptyp_fresh_id a b A) in hsub;
      [ | clear - Ha; fsetdec | clear - Hb; fsetdec ].
    apply a_typing__anno with (Θ1 := swap_aenv a b Θ1);
      [ | exact hsub ].
    pose proof (IHa_typing ltac:(clear - Ha; fsetdec)
                  ltac:(clear - Hb; fsetdec)
                  ltac:(clear - Hbv; fsetdec)) as IH.
    rewrite swap_pskl_ptyp_to_pskl in IH.
    rewrite (swap_ptyp_fresh_id a b A) in IH;
      [ | clear - Ha; fsetdec | clear - Hb; fsetdec ].
    exact IH.
  - (* freeze *)
    rewrite swap_pskl_ptyp_to_pskl.
    apply a_typing__freeze with (B := swap_ptyp a b B)
      (Θ1 := swap_aenv a b Θ1).
    + pose proof (IHa_typing Ha Hb Hbv) as IH. exact IH.
    + pose proof (a_consis_chk_swap a b _ _ _ _ H0) as hc.
      rewrite !swap_pskl_ptyp_to_pskl in hc.
      exact hc.
  - (* abs (guess^TY) *)
    rewrite !swap_aenv_app.
    eapply a_typing__abs
      with (L := L `union` singleton a `union` singleton b);
      [ assumption
      | apply a_split_swap; eassumption
      | apply a_guess_mono_swap; eassumption
      | rewrite <- swap_aenv_app; apply swap_aenv_uniq; assumption
      | apply a_suffix_swap; assumption
      | ].
    intros z Hz.
    rewrite subst_exp_in_exp_open_exp_wrt_exp_var;
      [ | clear - Hz; fsetdec | apply lc_exp_var_f ].
    assert (Hza : z <> a) by (clear - Hz; fsetdec).
    assert (Hzb : z <> b) by (clear - Hz; fsetdec).
    pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f z)) as hfu.
    pose proof (fvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f z)) as hvu.
    simpl in hfu, hvu.
    pose proof (H5 z ltac:(clear - Hz; fsetdec)
                  ltac:(clear - Ha hfu; fsetdec)
                  ltac:(clear - Hb hfu; fsetdec)
                  ltac:(clear - Hbv hvu Hzb; fsetdec)) as IH.
    rewrite !swap_aenv_app, !swap_aenv_one,
      (swap_atom_other a b z Hza Hzb) in IH.
    cbn [swap_abind] in IH.
    exact IH.
  - (* abs_anno *)
    rewrite swap_aenv_app.
    cbn [swap_ptyp].
    rewrite (swap_ptyp_fresh_id a b A);
      [ | clear - Ha; fsetdec | clear - Hb; fsetdec ].
    eapply a_typing__abs_anno
      with (L := L `union` singleton a `union` singleton b)
           (Θ1 := swap_aenv a b Θ1) (Θ2 := swap_aenv a b Θ2)
           (P := swap_pskl a b P);
      [ assumption
      | apply a_split_swap; eassumption
      | pose proof (a_consis_chk_swap a b _ _ _ _ H1) as hc;
        rewrite swap_pskl_ptyp_to_pskl in hc;
        rewrite (swap_ptyp_fresh_id a b A) in hc;
        [ exact hc | clear - Ha; fsetdec | clear - Hb; fsetdec ]
      | apply a_suffix_swap; assumption
      | ].
    intros z Hz.
    rewrite subst_exp_in_exp_open_exp_wrt_exp_var;
      [ | clear - Hz; fsetdec | apply lc_exp_var_f ].
    assert (Hza : z <> a) by (clear - Hz; fsetdec).
    assert (Hzb : z <> b) by (clear - Hz; fsetdec).
    pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f z)) as hfu.
    pose proof (fvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f z)) as hvu.
    simpl in hfu, hvu.
    pose proof (H4 z ltac:(clear - Hz; fsetdec)
                  ltac:(clear - Ha hfu; fsetdec)
                  ltac:(clear - Hb hfu; fsetdec)
                  ltac:(clear - Hbv hvu Hzb; fsetdec)) as IH.
    rewrite !swap_aenv_app, !swap_aenv_one,
      (swap_atom_other a b z Hza Hzb) in IH.
    cbn [swap_abind] in IH.
    rewrite (swap_ptyp_fresh_id a b A) in IH;
      [ | clear - Ha; fsetdec | clear - Hb; fsetdec ].
    exact IH.
  - (* abs_check_step : the TYPE-variable family swaps by the bijection *)
    rewrite swap_pskl_ptyp_to_pskl.
    cbn [swap_ptyp].
    eapply a_typing__abs_check_step
      with (L := swap_atoms a b L) (Ξ := swap_aenv a b Ξ);
      [ apply a_suffix_swap; assumption
      | rewrite <- swap_aenv_app; apply swap_aenv_uniq; assumption
      | intros γ Hγ;
        pose proof (swap_aenv_dom_in_rev a b Ξ _ Hγ) as hd;
        pose proof (H1 _ hd) as hf;
        pose proof (swap_ptyp_ftv_notin a b A _ hf) as hnf;
        rewrite swap_atom_invol in hnf; exact hnf
      | ].
    intros β Hβ.
    assert (hin : swap_atom a b β `notin` L)
      by (intro hc; apply Hβ; apply swap_atoms_iff; exact hc).
    pose proof (H3 _ hin Ha Hb Hbv) as IH.
    rewrite !swap_aenv_app, !swap_aenv_one in IH.
    cbn [swap_abind] in IH.
    rewrite swap_atom_invol in IH.
    rewrite swap_pskl_ptyp_to_pskl in IH.
    rewrite !swap_ptyp_open in IH.
    cbn [swap_ptyp] in IH.
    rewrite !swap_atom_invol in IH.
    exact IH.
  - (* abs_check_base *)
    rewrite swap_pskl_ptyp_to_pskl.
    cbn [swap_ptyp].
    eapply a_typing__abs_check_base
      with (L := L `union` singleton a `union` singleton b)
           (Θ1 := swap_aenv a b Θ1) (Ξ := swap_aenv a b Ξ);
      [ pose proof (a_split_swap a b H) as hs;
        rewrite !swap_pskl_ptyp_to_pskl in hs; exact hs
      | apply a_suffix_swap; assumption
      | rewrite <- swap_aenv_app; apply swap_aenv_uniq; assumption
      | intros γ Hγ;
        pose proof (swap_aenv_dom_in_rev a b Ξ _ Hγ) as hd;
        pose proof (H2 _ hd) as hf;
        pose proof (swap_ptyp_ftv_notin a b B _ hf) as hnf;
        rewrite swap_atom_invol in hnf; exact hnf
      | ].
    intros z Hz.
    rewrite subst_exp_in_exp_open_exp_wrt_exp_var;
      [ | clear - Hz; fsetdec | apply lc_exp_var_f ].
    assert (Hza : z <> a) by (clear - Hz; fsetdec).
    assert (Hzb : z <> b) by (clear - Hz; fsetdec).
    pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f z)) as hfu.
    pose proof (fvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f z)) as hvu.
    simpl in hfu, hvu.
    pose proof (H4 z ltac:(clear - Hz; fsetdec)
                  ltac:(clear - Ha hfu; fsetdec)
                  ltac:(clear - Hb hfu; fsetdec)
                  ltac:(clear - Hbv hvu Hzb; fsetdec)) as IH.
    rewrite !swap_aenv_app, !swap_aenv_one,
      (swap_atom_other a b z Hza Hzb) in IH.
    cbn [swap_abind] in IH.
    rewrite swap_pskl_ptyp_to_pskl in IH.
    exact IH.
  - (* abs_anno_check_step *)
    rewrite swap_pskl_ptyp_to_pskl.
    cbn [swap_ptyp].
    eapply a_typing__abs_anno_check_step
      with (L := swap_atoms a b L) (Ξ := swap_aenv a b Ξ);
      [ apply a_suffix_swap; assumption
      | rewrite <- swap_aenv_app; apply swap_aenv_uniq; assumption
      | intros γ Hγ;
        pose proof (swap_aenv_dom_in_rev a b Ξ _ Hγ) as hd;
        pose proof (H1 _ hd) as hf;
        pose proof (swap_ptyp_ftv_notin a b A _ hf) as hnf;
        rewrite swap_atom_invol in hnf; exact hnf
      | ].
    intros β Hβ.
    assert (hin : swap_atom a b β `notin` L)
      by (intro hc; apply Hβ; apply swap_atoms_iff; exact hc).
    pose proof (H3 _ hin Ha Hb Hbv) as IH.
    rewrite !swap_aenv_app, !swap_aenv_one in IH.
    cbn [swap_abind] in IH.
    rewrite swap_atom_invol in IH.
    rewrite swap_pskl_ptyp_to_pskl in IH.
    rewrite !swap_ptyp_open in IH.
    cbn [swap_ptyp] in IH.
    rewrite !swap_atom_invol in IH.
    exact IH.
  - (* abs_anno_check_base *)
    rewrite swap_pskl_ptyp_to_pskl.
    cbn [swap_ptyp].
    eapply a_typing__abs_anno_check_base
      with (L := L `union` singleton a `union` singleton b)
           (Θ1 := swap_aenv a b Θ1) (Θ2 := swap_aenv a b Θ2)
           (Ξ := swap_aenv a b Ξ);
      [ pose proof (a_split_swap a b H) as hs;
        rewrite !swap_pskl_ptyp_to_pskl in hs; exact hs
      | pose proof (a_consis_chk_swap a b _ _ _ _ H0) as hc;
        rewrite !swap_pskl_ptyp_to_pskl in hc;
        rewrite (swap_ptyp_fresh_id a b A) in hc;
        [ exact hc | clear - Ha; fsetdec | clear - Hb; fsetdec ]
      | apply a_suffix_swap; assumption
      | rewrite <- swap_aenv_app; apply swap_aenv_uniq; assumption
      | intros γ Hγ;
        pose proof (swap_aenv_dom_in_rev a b Ξ _ Hγ) as hd;
        pose proof (H3 _ hd) as hf;
        pose proof (swap_ptyp_ftv_notin a b B _ hf) as hnf;
        rewrite swap_atom_invol in hnf; exact hnf
      | ].
    intros z Hz.
    rewrite subst_exp_in_exp_open_exp_wrt_exp_var;
      [ | clear - Hz; fsetdec | apply lc_exp_var_f ].
    assert (Hza : z <> a) by (clear - Hz; fsetdec).
    assert (Hzb : z <> b) by (clear - Hz; fsetdec).
    pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f z)) as hfu.
    pose proof (fvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f z)) as hvu.
    simpl in hfu, hvu.
    pose proof (H5 z ltac:(clear - Hz; fsetdec)
                  ltac:(clear - Ha hfu; fsetdec)
                  ltac:(clear - Hb hfu; fsetdec)
                  ltac:(clear - Hbv hvu Hzb; fsetdec)) as IH.
    rewrite !swap_aenv_app, !swap_aenv_one,
      (swap_atom_other a b z Hza Hzb) in IH.
    cbn [swap_abind] in IH.
    rewrite swap_pskl_ptyp_to_pskl in IH.
    rewrite (swap_ptyp_fresh_id a b A) in IH;
      [ | clear - Ha; fsetdec | clear - Hb; fsetdec ].
    exact IH.
  - (* app *)
    eapply a_typing__app
      with (Θ1 := swap_aenv a b Θ1) (Θ2 := swap_aenv a b Θ2)
           (P := swap_pskl a b P) (A := swap_ptyp a b A).
    + pose proof (@a_pat_rename_tm a b _ _ _ _ _ _ H
                    ltac:(clear - Ha; fsetdec)
                    ltac:(clear - Hb; fsetdec)
                    ltac:(clear - Hbv; fsetdec)) as h.
      exact h.
    + pose proof (IHa_typing1 ltac:(clear - Ha; fsetdec)
                    ltac:(clear - Hb; fsetdec)
                    ltac:(clear - Hbv; fsetdec)) as IH.
      exact IH.
    + pose proof (IHa_typing2 ltac:(clear - Ha; fsetdec)
                    ltac:(clear - Hb; fsetdec)
                    ltac:(clear - Hbv; fsetdec)) as IH.
      rewrite swap_pskl_ptyp_to_pskl in IH.
      exact IH.
Qed.

(* ===================================================================== *)
(*  THEOREM 4 — the statement, factored like [pat_complete_concl]         *)
(* ===================================================================== *)

Definition typ_complete_concl (M : mode) (Θ0 : aenv) (P0 : pskl) (e : exp)
    (κ : metasubst) (Θ : aenv) (B : btyp) : Prop :=
  exists A1 Θ1,
    a_typing M Θ0 P0 e A1 Θ1 /\
    (forall κ1, is_id_msubst κ1 -> κ1 ∷ Θ0 ⊑ Θ1 ->
       exists ζ,
         ζ ∷ Θ1 ⊑ Θ /\
         a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ /\
         Θ ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B)).

(* ===================================================================== *)
(*  The two tails every base row shares                                   *)
(* ===================================================================== *)

(** The counterpart's wf, read off the fused rule's join: scope from
    [ad_pat_sub_target_wf], ghost-freeness structural (it is a [btyp]'s
    erasure). *)
Lemma typ_counterpart_wf : forall NM M Ψ Θ R (B : btyp),
  Ψ ⨟ Θ ⊢ₛᵃ[ NM | M ] R ⩽ (btyp_to_bskl B) ->
  Θ ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl (btyp_to_bskl B)).
Proof.
  intros NM M Ψ Θ R B Hj.
  rewrite bskl_to_pskl_btyp.
  apply a_wf_ptyp_to_wf_pskl.
  eapply a_wf_ptyp_of_scope_pskl;
    [ | rewrite <- bskl_to_pskl_btyp; reflexivity ].
  eapply ad_pat_sub_target_wf. exact Hj.
Qed.

(** The optimality tail every base row shares: a PRECISION between two
    type paintings IS the type equivalence the conclusion carries. *)
Lemma typ_opt_tail : forall Θ ζ A1 (B : btyp),
  a_wf_aenv Θ ->
  Θ ⨟ empty ⊢ₚᵣᵃ
    (bskl_to_pskl (msubst_bskl ζ (pskl_to_bskl_syn (ptyp_to_pskl A1))))
    ⊑ (bskl_to_pskl (btyp_to_bskl B)) ->
  Θ ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B).
Proof.
  intros Θ ζ A1 B HwfΘ Hprec.
  rewrite msubst_bskl_syn_erase, msubst_pskl_embed_ptyp, bskl_to_pskl_btyp
    in Hprec.
  unfold ad_precise in Hprec.
  rewrite (pskl_to_bskl_inh_ptyp (btyp_to_ptyp B)) in Hprec.
  pose proof (ad_refine_syn_inh_tyequiv Hprec HwfΘ
                (msubst_ptyp ζ A1) (ptyp_to_btyp_inh (btyp_to_ptyp B))
                eq_refl eq_refl) as Heqc.
  rewrite btyp_to_ptyp_ptyp_to_btyp_inh in Heqc.
  exact Heqc.
Qed.

(* ===================================================================== *)
(*  The Unit base row                                                     *)
(* ===================================================================== *)

Lemma a_typing_complete_unit : forall M Θ0 P0 κ Θ B,
  a_wf_aenv Θ0 -> a_wf_aenv Θ ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  a_ty_mode_compat M P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  Θ ⊢ˢᵃ[ M ] exp_unit ⦂ B ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (btyp_to_bskl B) ->
  typ_complete_concl M Θ0 P0 exp_unit κ Θ B.
Proof.
  intros M Θ0 P0 κ Θ B Hwf0 HwfΘ HwfP0 Hmod Hinc Hd Href.
  inversion Hd; subst.
  match goal with
  | H : ad_pat_sub_v _ _ _ _ _ _ |- _ => destruct H as [njoin Hjoin]
  end.
  assert (HwfQ : Θ ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl (btyp_to_bskl B)))
    by (eapply typ_counterpart_wf;
        exact (ad_pat_sub_of_v (ex_intro _ njoin Hjoin))).
  destruct (@a_sub_complete_thm njoin a_sub_mode_ty M Θ0 P0
              pskl_unit (ptyp_to_uskl_syn ptyp_unit) Θ κ (btyp_to_bskl B)
              Hwf0 HwfΘ HwfP0
              ltac:(apply a_wf_pskl__unit)
              ltac:(intros Hc; discriminate)
              ltac:(intros _; exact Hmod)
              Hinc
              (slack_unit Θ κ)
              Hjoin Href HwfQ
              ltac:(intros _; rewrite <- pskl_to_uskl_ptyp;
                    apply pskl_to_uskl_ptyp_ghost_free; apply lc_ptyp_unit))
    as [P1 [Θ1 [Hrun Hopt]]].
  (* the run's output is a painted type (T4-K1) *)
  assert (HgfP1 : pskl_ghost_free P1)
    by (eapply a_sub_ty_ghost_free_output; [ exact Hrun | exact I ]).
  destruct (pskl_ghost_free_to_ptyp P1 HgfP1) as [A1 ->].
  exists A1, Θ1. split; [ apply a_typing__unit; exact Hrun | ].
  intros κ1 Hid Hinc1.
  destruct (Hopt κ1 Hid Hinc1) as [ζ [Hζ [Heqv Hprec]]].
  exists ζ. split; [ exact Hζ | ]. split; [ exact Heqv | ].
  apply typ_opt_tail; [ exact HwfΘ | exact Hprec ].
Qed.

(* ===================================================================== *)
(*  The Var base row                                                      *)
(* ===================================================================== *)

Lemma a_typing_complete_var : forall M Θ0 P0 x κ Θ B,
  a_wf_aenv Θ0 -> a_wf_aenv Θ ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  a_ty_mode_compat M P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  Θ ⊢ˢᵃ[ M ] (exp_var_f x) ⦂ B ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (btyp_to_bskl B) ->
  typ_complete_concl M Θ0 P0 (exp_var_f x) κ Θ B.
Proof.
  intros M Θ0 P0 x κ Θ B Hwf0 HwfΘ HwfP0 Hmod Hinc Hd Href.
  inversion Hd; subst.
  match goal with
  | H : ad_pat_sub_v _ _ _ _ _ _ |- _ => destruct H as [njoin Hjoin]
  end.
  match goal with
  | H : binds x (abind_var_typ _) Θ |- _ => rename H into Hb
  end.
  (* K2 : the entry's preimage, with its ≡ᵗ slack *)
  destruct (@a_inc_binds_var_typ_rev Θ0 κ Θ x A Hinc Hwf0 Hb) as [A0 [Hb0 Heq]].
  assert (HwfA0 : a_wf_ptyp Θ0 A0)
    by (eapply a_wf_aenv_binds_var_typ_wf; eassumption).
  assert (HwfA : a_wf_ptyp Θ A)
    by (eapply a_wf_aenv_binds_var_typ_wf; eassumption).
  destruct (@a_sub_complete_thm njoin a_sub_mode_ty M Θ0 P0
              (ptyp_to_pskl A0) (ptyp_to_uskl_syn A) Θ κ (btyp_to_bskl B)
              Hwf0 HwfΘ HwfP0
              ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfA0)
              ltac:(intros Hc; discriminate)
              ltac:(intros _; exact Hmod)
              Hinc
              ltac:(rewrite pskl_to_uskl_ptyp, <- msubst_ptyp_to_uskl_syn;
                    apply a_tyequiv_to_uskl; [ exact Heq | exact HwfΘ ])
              Hjoin Href
              ltac:(eapply typ_counterpart_wf;
                    exact (ad_pat_sub_of_v (ex_intro _ njoin Hjoin)))
              ltac:(intros _; rewrite <- pskl_to_uskl_ptyp;
                    apply pskl_to_uskl_ptyp_ghost_free;
                    eapply a_wf_ptyp_lc; exact HwfA))
    as [P1 [Θ1 [Hrun Hopt]]].
  assert (HgfP1 : pskl_ghost_free P1)
    by (eapply a_sub_ty_ghost_free_output;
        [ exact Hrun | apply ptyp_to_pskl_ghost_free ]).
  destruct (pskl_ghost_free_to_ptyp P1 HgfP1) as [A1 ->].
  exists A1, Θ1.
  split; [ eapply a_typing__var; [ exact Hb0 | exact Hrun ] | ].
  intros κ1 Hid Hinc1.
  destruct (Hopt κ1 Hid Hinc1) as [ζ [Hζ [Heqv Hprec]]].
  exists ζ. split; [ exact Hζ | ]. split; [ exact Heqv | ].
  apply typ_opt_tail; [ exact HwfΘ | exact Hprec ].
Qed.

(* ===================================================================== *)
(*  The Anno base row — TWO stages: the body at [(TC, ⌈A⌉)] (the IH),     *)
(*  then the fused subtyping ([a_sub_complete_thm]).  ⭐ The body run      *)
(*  returns the annotation ITSELF ([a_typing_tc_rigid_output],            *)
(*  prop_ty_core.v) — the fact [AT-Anno]'s premise demands and the        *)
(*  paper's Anno case asserts by metavariable pun.  The optimality glues  *)
(*  the two factorings by [a_inc_equiv_glue]; the dom side condition is   *)
(*  [a_inc_id_flex_preserve] at the body run's own identity increase.     *)
(* ===================================================================== *)

Lemma a_typing_complete_anno : forall M Θ0 P0 e A κ Θ B,
  a_wf_aenv Θ0 -> a_wf_aenv Θ ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  a_ty_mode_compat M P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_anno e A) -> binds α abind_tvar Θ0) ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ0 -> Θ0 ⨟ empty ⊢ₚₛᵃ Ps) ->
  lc_exp (exp_anno e A) ->
  (forall M' Θ0' P0' κ' Θ' B',
     a_wf_aenv Θ0' -> a_wf_aenv Θ' ->
     Θ0' ⨟ empty ⊢ₚₛᵃ P0' ->
     a_ty_mode_compat M' P0' ->
     κ' ∷ Θ0' ⊑ Θ' ->
     (forall α, α `in` ftvar_in_exp e -> binds α abind_tvar Θ0') ->
     (forall y Ps, binds y (abind_var_skl Ps) Θ0' -> Θ0' ⨟ empty ⊢ₚₛᵃ Ps) ->
     lc_exp e ->
     Θ' ⊢ˢᵃ[ M' ] e ⦂ B' ->
     Θ' ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ' P0'))
       ⊳ (btyp_to_bskl B') ->
     typ_complete_concl M' Θ0' P0' e κ' Θ' B') ->
  Θ ⊢ˢᵃ[ M ] (exp_anno e A) ⦂ B ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (btyp_to_bskl B) ->
  typ_complete_concl M Θ0 P0 (exp_anno e A) κ Θ B.
Proof.
  intros M Θ0 P0 e A κ Θ B Hwf0 HwfΘ HwfP0 Hmod Hinc Hrig Hskl Hlc IH Hd Href.
  inversion Hd; subst.
  match goal with
  | H : ad_pat_sub_v _ _ _ _ _ _ |- _ => destruct H as [njoin Hjoin]
  end.
  match goal with
  | H : ad_sd_typing mode_tc Θ e _ |- _ => rename H into Hde
  end.
  simpl in Hrig.
  assert (Hrige : forall α, α `in` ftvar_in_exp e -> binds α abind_tvar Θ0)
    by (intros α Hα; apply Hrig; clear - Hα; fsetdec).
  assert (HrigA : forall α, α `in` ftvar_in_ptyp A -> binds α abind_tvar Θ0)
    by (intros α Hα; apply Hrig; clear - Hα; fsetdec).
  assert (Hlce : lc_exp e) by (inversion Hlc; assumption).
  assert (HlcA : lc_ptyp A) by (inversion Hlc; assumption).
  assert (HwfA0 : a_wf_ptyp Θ0 A)
    by (apply a_wf_ptyp_of_lc_tvarish;
        [ exact HlcA | intros α Hα; left; apply HrigA; exact Hα ]).
  assert (HwfAΘ : a_wf_ptyp Θ A)
    by (apply a_wf_ptyp_of_lc_tvarish;
        [ exact HlcA
        | intros α Hα; left; eapply a_inc_binds_tvar;
            [ exact Hinc | apply HrigA; exact Hα ] ]).
  assert (HmsA : msubst_ptyp κ A = A)
    by (eapply msubst_ptyp_rigid_id;
        [ exact Hinc | exact Hwf0 | exact HrigA ]).
  assert (HwfpA0 : Θ0 ⨟ empty ⊢ₚₛᵃ (ptyp_to_pskl A))
    by (apply a_wf_ptyp_to_wf_pskl; exact HwfA0).
  (* ---- 1. the BODY stage, by the IH at (TC, ⌈A⌉) ---- *)
  destruct (IH mode_tc Θ0 (ptyp_to_pskl A) κ Θ (ptyp_to_btyp_inh A)
              Hwf0 HwfΘ HwfpA0
              (a_ty_mode_compat__tc A)
              Hinc Hrige Hskl Hlce Hde
              ltac:(rewrite msubst_pskl_embed_ptyp, HmsA,
                      <- (pskl_to_bskl_inh_ptyp A);
                    apply ad_refine_syn_refl_inh;
                    apply a_wf_ptyp_to_wf_pskl; exact HwfAΘ))
    as [A1' [Θmid [HrunB HoptB]]].
  (* ⭐ the run returned the ANNOTATION ITSELF (prop_ty_core) *)
  assert (HA1' : A1' = A).
  { eapply a_typing_tc_rigid_output; [ exact HrunB | ].
    intros α Hα.
    pose proof (a_wf_aenv_uniq Hwf0) as Hu.
    split; [ apply HrigA; exact Hα | ].
    split.
    - intros Hb.
      pose proof (binds_unique _ _ _ _ _ Hb (HrigA α Hα) Hu) as Hc.
      discriminate Hc.
    - intros τ Hb.
      pose proof (binds_unique _ _ _ _ _ Hb (HrigA α Hα) Hu) as Hc.
      discriminate Hc. }
  subst A1'.
  (* the run's own identity increase + the mid context's wf *)
  assert (Hexpe : a_wf_exp Θ0 e)
    by (apply a_wf_exp_of_tvarish;
        [ exact Hlce | intros α Hα; left; apply Hrige; exact Hα ]).
  destruct (a_typing_sound HrunB Hwf0 Hskl HwfpA0
              (a_ty_mode_compat__tc A) Hexpe)
    as [HleB [Hwfmid _]].
  destruct HleB as [[κb [Hidb Hincb]] _].
  destruct (HoptB κb Hidb Hincb) as [ζb [Hζb [Heqvb _]]].
  assert (HrigMid : forall α, α `in` ftvar_in_ptyp A ->
             binds α abind_tvar Θmid)
    by (intros α Hα; eapply a_inc_binds_tvar;
        [ exact Hincb | apply HrigA; exact Hα ]).
  assert (HwfAmid : a_wf_ptyp Θmid A)
    by (apply a_wf_ptyp_of_lc_tvarish;
        [ exact HlcA | intros α Hα; left; apply HrigMid; exact Hα ]).
  assert (HmsAζb : msubst_ptyp ζb A = A)
    by (eapply msubst_ptyp_rigid_id;
        [ exact Hζb | exact Hwfmid | exact HrigMid ]).
  assert (HwfP0mid : Θmid ⨟ empty ⊢ₚₛᵃ P0).
  { pose proof (a_wf_pskl_msubst_inc Hincb Hwf0 HwfP0
                  ltac:(intros α Hα; clear - Hα; fsetdec)) as Hw.
    rewrite (msubst_pskl_id P0 Hidb) in Hw. exact Hw. }
  (* ---- 2. transport the refinement to ζb ---- *)
  assert (Hσ : msubst_compose ζb κb ∷ Θ0 ⊑ Θ)
    by (eapply a_inc_compose;
        [ exact Hincb | exact Hwf0 | exact Hwfmid | exact Hζb ]).
  assert (HwfQ : Θ ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl (btyp_to_bskl B)))
    by (eapply typ_counterpart_wf;
        exact (ad_pat_sub_of_v (ex_intro _ njoin Hjoin))).
  assert (Hpp : Θ ⨟ empty ⊢ₚᵣᵃ (msubst_pskl (msubst_compose ζb κb) P0)
                  ⊑ (msubst_pskl κ P0)).
  { eapply a_inc_equiv_precise_msubst_flip with (Θ0 := Θ0) (Δ0 := empty);
      [ exact HwfP0 | exact Hwf0 | exact HwfΘ | exact Hinc | exact Hσ
      | exact Heqvb | clear; fsetdec ]. }
  assert (HrefT : Θ ⨟ empty ⊢ᵣᵃ
                    (pskl_to_bskl_inh (msubst_pskl (msubst_compose ζb κb) P0))
                    ⊳ (btyp_to_bskl B)).
  { eapply ad_precise_preserves_refine;
      [ exact Hpp | exact Href | exact HwfΘ
      | intros α Hα; clear - Hα; fsetdec | exact HwfQ ]. }
  assert (Hms : msubst_pskl (msubst_compose ζb κb) P0 = msubst_pskl ζb P0).
  { eapply msubst_compose_id_pskl;
      [ exact Hwf0 | exact Hwfmid | exact Hidb | exact Hincb | exact Hζb
      | eapply a_wf_pskl_to_a_scope_pskl;
          [ exact HwfP0 | intros z b Hb; exact Hb
          | intros α Hα; clear - Hα; fsetdec ] ]. }
  rewrite Hms in HrefT.
  (* ---- 3. the SUB stage ---- *)
  destruct (@a_sub_complete_thm njoin a_sub_mode_ty M Θmid P0
              (ptyp_to_pskl A) (ptyp_to_uskl_syn A) Θ ζb (btyp_to_bskl B)
              Hwfmid HwfΘ HwfP0mid
              ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfAmid)
              ltac:(intros Hc; discriminate)
              ltac:(intros _; exact Hmod)
              Hζb
              ltac:(rewrite pskl_to_uskl_ptyp, <- msubst_ptyp_to_uskl_syn,
                      HmsAζb;
                    apply a_uskl_tyequiv_refl;
                    rewrite <- pskl_to_uskl_ptyp; apply pskl_to_uskl_lc;
                    apply lc_ptyp_to_pskl; exact HlcA)
              Hjoin HrefT HwfQ
              ltac:(intros _; rewrite <- pskl_to_uskl_ptyp;
                    apply pskl_to_uskl_ptyp_ghost_free; exact HlcA))
    as [P1 [Θ2 [HrunS HoptS]]].
  assert (HgfP1 : pskl_ghost_free P1)
    by (eapply a_sub_ty_ghost_free_output;
        [ exact HrunS | apply ptyp_to_pskl_ghost_free ]).
  destruct (pskl_ghost_free_to_ptyp P1 HgfP1) as [B1 ->].
  (* ---- 4. the run ---- *)
  exists B1, Θ2.
  split; [ eapply a_typing__anno; [ exact HrunB | exact HrunS ] | ].
  (* ---- 5. optimality: glue the two stages ---- *)
  intros κ1 Hid1 Hinc1.
  assert (Heqκ : κ1 = κb)
    by (eapply a_inc_id_msubst_unique;
        [ exact Hinc1 | exact Hincb | exact Hid1 | exact Hidb ]).
  destruct (proj1 a_sub_output_wf_bundle _ _ _ _ _ _ _ HrunS
              Hwfmid HwfP0mid
              ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfAmid))
    as [HleS [Hwf2 _]].
  destruct HleS as [[κs [Hids Hincs]] _].
  destruct (HoptS κs Hids Hincs) as [ζs [Hζs [Heqvs Hprecs]]].
  exists ζs.
  split; [ exact Hζs | ].
  split.
  { assert (Hglue : a_inc_equiv Θ0 κ (msubst_compose ζs κb) Θ).
    { eapply a_inc_equiv_glue with
        (Θmid := Θmid) (Θfin := Θ2) (κ1b := κs) (ζ1 := ζb);
        [ exact Hwf0 | exact Hwfmid | exact Hwf2 | exact HwfΘ
        | exact Hidb | exact Hids
        | intros α Hα;
          pose proof (a_inc_dom_flex Hincb Hα) as Hfα;
          eapply a_inc_flex_dom;
            [ exact Hincs | exact Hwfmid
            | eapply a_inc_id_flex_preserve;
                [ exact Hincb | exact Hidb | exact Hwf0 | exact Hfα ] ]
        | exact Hincb | exact Hincs | exact Hζb | exact Hζs
        | exact Heqvb | exact Heqvs ]. }
    rewrite Heqκ. exact Hglue. }
  apply typ_opt_tail; [ exact HwfΘ | exact Hprecs ].
Qed.

(* ===================================================================== *)
(*  The Freeze row's kit: coercion composite, the [≡ᵗ]→[≡ˢ] embedding,    *)
(*  wf transport along [≡ᵗ], and K1's typing analogue (target wf,         *)
(*  bottom-up).                                                            *)
(* ===================================================================== *)

(** The syn twin of [pskl_to_bskl_inh_ptyp]. *)
Lemma pskl_to_bskl_syn_ptyp : forall A,
  pskl_to_bskl_syn (ptyp_to_pskl A) = btyp_to_bskl (ptyp_to_btyp_syn A).
Proof. induction A; simpl; f_equal; auto. Qed.

(** [≡ᵗ] embeds into [≡ˢ] on the paintings (row for row). *)
Lemma a_tyequiv_embed_pskl : forall Θ A B,
  Θ ⊢ A ≡ᵗ B ->
  Θ ⊢ (ptyp_to_pskl A) ≡ˢ (ptyp_to_pskl B).
Proof.
  intros Θ A B H; induction H.
  - apply a_pskl_tyequiv__refl. apply lc_ptyp_to_pskl. exact H.
  - apply a_pskl_tyequiv__sym. exact IHa_tyequiv.
  - eapply a_pskl_tyequiv__trans; eassumption.
  - apply a_pskl_tyequiv__flex_def. exact H.
  - simpl. apply a_pskl_tyequiv__arrow; assumption.
  - simpl. apply a_pskl_tyequiv__all with (L := L).
    intros α Hα.
    rewrite <- !ptyp_to_pskl_open.
    apply H0. exact Hα.
Qed.

(** Well-formedness transports along [≡ᵗ], both ways (the flex-def row
    swaps a variable for its definition, both wf in a wf context).  Stated
    over any binds-including context so the ∀ row's extension composes. *)
Lemma a_tyequiv_wf_iff : forall Θ A B,
  Θ ⊢ A ≡ᵗ B ->
  forall Θ',
  (forall x (b : abind), binds x b Θ -> binds x b Θ') ->
  a_wf_aenv Θ' ->
  (a_wf_ptyp Θ' A -> a_wf_ptyp Θ' B) /\
  (a_wf_ptyp Θ' B -> a_wf_ptyp Θ' A).
Proof.
  intros Θ A B H; induction H; intros Θ' Hincl Hwf'.
  - split; intros HA; exact HA.
  - destruct (IHa_tyequiv Θ' Hincl Hwf') as [Hd1 Hd2].
    split; [ exact Hd2 | exact Hd1 ].
  - destruct (IHa_tyequiv1 Θ' Hincl Hwf') as [H1l H1r].
    destruct (IHa_tyequiv2 Θ' Hincl Hwf') as [H2l H2r].
    split;
      [ intros HA; exact (H2l (H1l HA))
      | intros HC; exact (H1r (H2r HC)) ].
  - split.
    + intros _. eapply a_wf_aenv_binds_def_wf; [ exact Hwf' | ].
      apply Hincl. exact H.
    + intros _. apply a_wf_ptyp__var.
      right; right. exists τ. apply Hincl. exact H.
  - split; intros HA; inversion HA; subst;
      apply a_wf_ptyp__arrow;
      first [ eapply (proj1 (IHa_tyequiv1 Θ' Hincl Hwf')); eassumption
            | eapply (proj2 (IHa_tyequiv1 Θ' Hincl Hwf')); eassumption
            | eapply (proj1 (IHa_tyequiv2 Θ' Hincl Hwf')); eassumption
            | eapply (proj2 (IHa_tyequiv2 Θ' Hincl Hwf')); eassumption ].
  - split; intros HA; inversion HA; subst;
    match goal with
    | Hfam : forall α, α `notin` ?L1 ->
               a_wf_ptyp _ (open_ptyp_wrt_ptyp _ _) |- _ =>
        apply a_wf_ptyp__all with (L := L `union` L1 `union` dom Θ');
        intros α Hα;
        (assert (Hwfx : a_wf_aenv ((α ~ abind_tvar) ++ Θ'))
          by (apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf' ]));
        (assert (Hinclx : forall x (b : abind),
                   binds x b Θ -> binds x b ((α ~ abind_tvar) ++ Θ'))
          by (intros x b Hb; apply binds_cons_3; apply Hincl; exact Hb));
        first
          [ eapply (proj1 (H0 α ltac:(clear - Hα; fsetdec) _ Hinclx Hwfx));
            apply Hfam; clear - Hα; fsetdec
          | eapply (proj2 (H0 α ltac:(clear - Hα; fsetdec) _ Hinclx Hwfx));
            apply Hfam; clear - Hα; fsetdec ]
    end.
Qed.

(** Strip a TERM entry off a type's wf (term entries are invisible to
    [a_binds_tvar]). *)
Lemma a_wf_ptyp_strip_tm_cons : forall x A0 Θ A,
  a_wf_ptyp ((x ~ abind_var_typ A0) ++ Θ) A ->
  a_wf_ptyp Θ A.
Proof.
  intros x A0 Θ A HwfA.
  apply a_wf_ptyp_of_lc_tvarish;
    [ eapply a_wf_ptyp_lc; exact HwfA | ].
  intros α Hα.
  pose proof (a_wf_ptyp_ftv_tvarish HwfA Hα) as Ht.
  destruct Ht as [Hr | [Hm | [τ Hd]]].
  - left. destruct (binds_cons_1 _ _ _ _ _ _ Hr) as [[_ Heq] | Hr'];
      [ discriminate Heq | exact Hr' ].
  - right; left.
    destruct (binds_cons_1 _ _ _ _ _ _ Hm) as [[_ Heq] | Hm'];
      [ discriminate Heq | exact Hm' ].
  - right; right. exists τ.
    destruct (binds_cons_1 _ _ _ _ _ _ Hd) as [[_ Heq] | Hd'];
      [ discriminate Heq | exact Hd' ].
Qed.

(** ⭐ K1's typing analogue, BOTTOM-UP: a syntax-directed typing's TARGET
    type is well formed (the base rows read it off their joins, the ≡ᵗ
    premises transport it, the binder rows strip their term entry). *)
Lemma ad_sd_typing_target_wf : forall M Θ e (B : btyp),
  Θ ⊢ˢᵃ[ M ] e ⦂ B ->
  a_wf_aenv Θ ->
  a_wf_ptyp Θ (btyp_to_ptyp B).
Proof.
  intros M Θ e B H; induction H; intros Hwf;
    try match goal with
        | Hj : ad_pat_sub_v _ _ _ _ _ _ |- _ =>
            destruct Hj as [n Hj];
            eapply a_wf_ptyp_of_scope_pskl;
              [ | rewrite <- bskl_to_pskl_btyp; reflexivity ];
            eapply ad_pat_sub_target_wf; exact (ad_pat_sub_of_gv Hj)
        end.
  - (* freeze *)
    rewrite btyp_to_ptyp_ptyp_to_btyp_inh.
    specialize (IHad_sd_typing Hwf).
    rewrite btyp_to_ptyp_ptyp_to_btyp_syn in IHad_sd_typing.
    eapply (proj1 (a_tyequiv_wf_iff H0 (fun x b h => h) Hwf)).
    exact IHad_sd_typing.
  - (* abs_check_step *)
    simpl.
    apply a_wf_ptyp__all with (L := L `union` dom Θ).
    intros α Hα.
    rewrite <- btyp_to_ptyp_open.
    apply H1; [ clear - Hα; fsetdec | ].
    apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ].
  - (* abs_check_base *)
    simpl.
    destruct (atom_fresh (L `union` dom Θ)) as [x Hx].
    apply a_wf_ptyp__arrow.
    + rewrite btyp_to_ptyp_ptyp_to_btyp_inh. exact H.
    + eapply a_wf_ptyp_strip_tm_cons with (x := x) (A0 := A).
      apply H2; [ clear - Hx; fsetdec | ].
      apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact H | exact Hwf ].
  - (* abs_anno_check_step *)
    simpl.
    apply a_wf_ptyp__all with (L := L `union` dom Θ).
    intros α Hα.
    rewrite <- btyp_to_ptyp_open.
    apply H1; [ clear - Hα; fsetdec | ].
    apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ].
  - (* abs_anno_check_base *)
    simpl.
    destruct (atom_fresh (L `union` dom Θ)) as [x Hx].
    apply a_wf_ptyp__arrow.
    + rewrite btyp_to_ptyp_ptyp_to_btyp_inh.
      eapply (proj1 (a_tyequiv_wf_iff H0 (fun y b h => h) Hwf)).
      exact H.
    + eapply a_wf_ptyp_strip_tm_cons with (x := x) (A0 := A).
      apply H3; [ clear - Hx; fsetdec | ].
      apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact H | exact Hwf ].
  - (* abs *)
    simpl.
    destruct (atom_fresh (L `union` dom Θ)) as [x Hx].
    apply a_wf_ptyp__arrow.
    + rewrite btyp_to_ptyp_ptyp_to_btyp_inh. exact H0.
    + eapply a_wf_ptyp_strip_tm_cons with (x := x) (A0 := A).
      apply H3; [ clear - Hx; fsetdec | ].
      apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact H0 | exact Hwf ].
  - (* abs_anno *)
    simpl.
    destruct (atom_fresh (L `union` dom Θ)) as [x Hx].
    apply a_wf_ptyp__arrow.
    + rewrite H2.
      eapply (proj1 (a_tyequiv_wf_iff H1 (fun y b h => h) Hwf)).
      exact H0.
    + eapply a_wf_ptyp_strip_tm_cons with (x := x) (A0 := A).
      apply H5; [ clear - Hx; fsetdec | ].
      apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact H0 | exact Hwf ].
  - (* app *)
    specialize (IHad_sd_typing1 Hwf).
    simpl in IHad_sd_typing1.
    inversion IHad_sd_typing1; subst.
    assumption.
Qed.


(* ===================================================================== *)
(*  The Freeze row — TWO stages: the body at [(TI, ◇)] (the IH), then     *)
(*  the consistency stage ([a_consis_complete_thm]) with the subject      *)
(*  transported along [≡ˢ] to the declarative types.  The conclusion's    *)
(*  [≡ᵗ] comes from the consis run's own subject-≡-input                  *)
(*  ([a_consis_chk_tyequiv]) pushed through the witnesses.                *)
(* ===================================================================== *)

Lemma a_typing_complete_freeze : forall Θ0 P0 e κ Θ B,
  a_wf_aenv Θ0 -> a_wf_aenv Θ ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  a_ty_mode_compat mode_tc P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_freeze e) -> binds α abind_tvar Θ0) ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ0 -> Θ0 ⨟ empty ⊢ₚₛᵃ Ps) ->
  lc_exp (exp_freeze e) ->
  (forall M' Θ0' P0' κ' Θ' B',
     a_wf_aenv Θ0' -> a_wf_aenv Θ' ->
     Θ0' ⨟ empty ⊢ₚₛᵃ P0' ->
     a_ty_mode_compat M' P0' ->
     κ' ∷ Θ0' ⊑ Θ' ->
     (forall α, α `in` ftvar_in_exp e -> binds α abind_tvar Θ0') ->
     (forall y Ps, binds y (abind_var_skl Ps) Θ0' -> Θ0' ⨟ empty ⊢ₚₛᵃ Ps) ->
     lc_exp e ->
     Θ' ⊢ˢᵃ[ M' ] e ⦂ B' ->
     Θ' ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ' P0'))
       ⊳ (btyp_to_bskl B') ->
     typ_complete_concl M' Θ0' P0' e κ' Θ' B') ->
  Θ ⊢ˢᵃ[ mode_tc ] (exp_freeze e) ⦂ B ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (btyp_to_bskl B) ->
  typ_complete_concl mode_tc Θ0 P0 (exp_freeze e) κ Θ B.
Proof.
  intros Θ0 P0 e κ Θ B Hwf0 HwfΘ HwfP0 Hmod Hinc Hrig Hskl Hlc IH Hd Href.
  inversion Hd; subst.
  match goal with
  | H : ad_sd_typing mode_ti Θ e (ptyp_to_btyp_syn ?BB) |- _ =>
      rename H into Hde; rename BB into B0
  end.
  match goal with
  | H : Θ ⊢ B0 ≡ᵗ ?AA |- _ => rename H into Heq0; rename AA into A
  end.
  inversion Hmod; subst.
  match goal with
  | |- typ_complete_concl _ _ (ptyp_to_pskl ?AP) _ _ _ _ => rename AP into Ap
  end.
  simpl in Hrig.
  assert (Hlce : lc_exp e) by (inversion Hlc; assumption).
  (* wf of the two declarative types at Θ, off the derivation (K1-typing) *)
  assert (HwfB0 : a_wf_ptyp Θ B0).
  { pose proof (ad_sd_typing_target_wf Hde HwfΘ) as Hw.
    rewrite btyp_to_ptyp_ptyp_to_btyp_syn in Hw. exact Hw. }
  assert (HwfA : a_wf_ptyp Θ A)
    by (eapply (proj1 (a_tyequiv_wf_iff Heq0 (fun x b h => h) HwfΘ));
        exact HwfB0).
  (* ---- 1. the BODY stage at (TI, ◇) ---- *)
  destruct (IH mode_ti Θ0 pskl_hole κ Θ (ptyp_to_btyp_syn B0)
              Hwf0 HwfΘ (a_wf_pskl__hole _ _) a_ty_mode_compat__ti Hinc
              Hrig Hskl Hlce Hde
              ltac:(cbn [msubst_pskl pskl_to_bskl_inh];
                    rewrite <- pskl_to_bskl_syn_ptyp;
                    apply ad_refine_syn__hole;
                    apply a_wf_ptyp_to_wf_pskl; exact HwfB0))
    as [B' [Θmid [HrunB HoptB]]].
  assert (Hexpe : a_wf_exp Θ0 e)
    by (apply a_wf_exp_of_tvarish;
        [ exact Hlce | intros α Hα; left; apply Hrig; exact Hα ]).
  destruct (a_typing_sound HrunB Hwf0 Hskl (a_wf_pskl__hole _ _)
              a_ty_mode_compat__ti Hexpe)
    as [HleB [Hwfmid [HwfB'mid _]]].
  destruct HleB as [[κb [Hidb Hincb]] _].
  destruct (HoptB κb Hidb Hincb) as [ζb [Hζb [Heqvb HeqB']]].
  rewrite btyp_to_ptyp_ptyp_to_btyp_syn in HeqB'.
  assert (HeqAll : Θ ⊢ (msubst_ptyp ζb B') ≡ᵗ A)
    by (eapply a_tyequiv__trans; [ exact HeqB' | exact Heq0 ]).
  assert (HwfApmid : Θmid ⨟ empty ⊢ₚₛᵃ (ptyp_to_pskl Ap)).
  { pose proof (a_wf_pskl_msubst_inc Hincb Hwf0 HwfP0
                  ltac:(intros α Hα; clear - Hα; fsetdec)) as Hw.
    rewrite (msubst_pskl_id _ Hidb) in Hw. exact Hw. }
  (* ---- 2. the transports for the consistency stage ---- *)
  assert (Hσ : msubst_compose ζb κb ∷ Θ0 ⊑ Θ)
    by (eapply a_inc_compose;
        [ exact Hincb | exact Hwf0 | exact Hwfmid | exact Hζb ]).
  set (Qb := btyp_to_bskl (ptyp_to_btyp_inh A)) in *.
  assert (HwfQb : Θ ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Qb)).
  { unfold Qb. rewrite bskl_to_pskl_btyp, btyp_to_ptyp_ptyp_to_btyp_inh.
    apply a_wf_ptyp_to_wf_pskl. exact HwfA. }
  assert (Hpp : Θ ⨟ empty ⊢ₚᵣᵃ
                  (msubst_pskl (msubst_compose ζb κb) (ptyp_to_pskl Ap))
                  ⊑ (msubst_pskl κ (ptyp_to_pskl Ap))).
  { eapply a_inc_equiv_precise_msubst_flip with (Θ0 := Θ0) (Δ0 := empty);
      [ exact HwfP0 | exact Hwf0 | exact HwfΘ | exact Hinc | exact Hσ
      | exact Heqvb | clear; fsetdec ]. }
  assert (HrefT : Θ ⨟ empty ⊢ᵣᵃ
                    (pskl_to_bskl_inh
                       (msubst_pskl (msubst_compose ζb κb) (ptyp_to_pskl Ap)))
                    ⊳ Qb).
  { eapply ad_precise_preserves_refine;
      [ exact Hpp | exact Href | exact HwfΘ
      | intros α Hα; clear - Hα; fsetdec | exact HwfQb ]. }
  assert (Hms : msubst_pskl (msubst_compose ζb κb) (ptyp_to_pskl Ap)
                = msubst_pskl ζb (ptyp_to_pskl Ap)).
  { eapply msubst_compose_id_pskl;
      [ exact Hwf0 | exact Hwfmid | exact Hidb | exact Hincb | exact Hζb
      | eapply a_wf_pskl_to_a_scope_pskl;
          [ exact HwfP0 | intros z b Hb; exact Hb
          | intros α Hα; clear - Hα; fsetdec ] ]. }
  rewrite Hms in HrefT.
  assert (Heqs : Θ ⊢ (ptyp_to_pskl (msubst_ptyp ζb B')) ≡ˢ (ptyp_to_pskl A))
    by (apply a_tyequiv_embed_pskl; exact HeqAll).
  assert (Hjoin : empty ⨟ Θ ⊢ₛᵃ
                    (pskl_to_uskl (msubst_pskl ζb (ptyp_to_pskl B'))) ∼ Qb).
  { rewrite msubst_pskl_embed_ptyp.
    eapply (proj2 (skl_tyequiv_consis_transport Heqs HwfΘ
                     (fun x b h => h))).
    rewrite pskl_to_uskl_ptyp.
    apply (ad_pat_consis_syn_bid HwfA (ptyp_to_btyp_inh A)
             (btyp_to_ptyp_ptyp_to_btyp_inh A)). }
  assert (Hrp : ad_refine_pskl_f empty Θ empty
                  (msubst_pskl ζb (ptyp_to_pskl B')) (bskl_to_pskl Qb)).
  { rewrite msubst_pskl_embed_ptyp.
    eapply (proj2 (skl_tyequiv_refine_pskl_f_transport Heqs HwfΘ
                     (fun x b h => h))).
    unfold Qb. rewrite bskl_to_pskl_btyp, btyp_to_ptyp_ptyp_to_btyp_inh.
    apply ad_refine_pskl_f_of_plain.
    apply ad_refine_pskl_refl.
    apply a_wf_ptyp_to_wf_pskl. exact HwfA. }
  (* ---- 3. the consistency stage ---- *)
  destruct (a_consis_complete_thm Hwfmid HwfApmid
              ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfB'mid)
              Hζb HwfΘ Hjoin
              ltac:(apply ad_refine_syn_f_of_plain; exact HrefT)
              Hrp)
    as [Qc [Θ2 [HcRun HoptC]]].
  (* ---- 4. the run ---- *)
  exists Ap, Θ2.
  split;
    [ eapply a_typing__freeze; [ exact HrunB | exists Qc; exact HcRun ] | ].
  (* ---- 5. optimality: glue the two stages ---- *)
  intros κ1 Hid1 Hinc1.
  assert (Heqκ : κ1 = κb)
    by (eapply a_inc_id_msubst_unique;
        [ exact Hinc1 | exact Hincb | exact Hid1 | exact Hidb ]).
  destruct (a_consis_isub_wf_nil HcRun Hwfmid HwfApmid
              ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfB'mid))
    as [HleC Hwf2].
  destruct HleC as [[κs [Hids Hincs]] _].
  destruct (HoptC κs Hids Hincs) as [ζs [Hζs [Heqvs _]]].
  exists ζs.
  split; [ exact Hζs | ].
  split.
  { assert (Hglue : a_inc_equiv Θ0 κ (msubst_compose ζs κb) Θ).
    { eapply a_inc_equiv_glue with
        (Θmid := Θmid) (Θfin := Θ2) (κ1b := κs) (ζ1 := ζb);
        [ exact Hwf0 | exact Hwfmid | exact Hwf2 | exact HwfΘ
        | exact Hidb | exact Hids
        | intros α Hα;
          pose proof (a_inc_dom_flex Hincb Hα) as Hfα;
          eapply a_inc_flex_dom;
            [ exact Hincs | exact Hwfmid
            | eapply a_inc_id_flex_preserve;
                [ exact Hincb | exact Hidb | exact Hwf0 | exact Hfα ] ]
        | exact Hincb | exact Hincs | exact Hζb | exact Hζs
        | exact Heqvb | exact Heqvs ]. }
    rewrite Heqκ. exact Hglue. }
  (* the ≡ᵗ conclusion via the run's own subject-≡-input *)
  assert (HwfApP : a_wf_ptyp Θmid Ap).
  { eapply a_wf_ptyp_of_scope_pskl; [ | reflexivity ].
    eapply a_wf_pskl_to_a_scope_pskl;
      [ exact HwfApmid | intros z b Hb; exact Hb
      | intros α Hα; clear - Hα; fsetdec ]. }
  assert (HeqIO : Θ2 ⊢ B' ≡ᵗ Ap)
    by (eapply a_consis_chk_tyequiv;
        [ exists Qc; exact HcRun | exact Hwfmid | exact HwfApP
        | exact HwfB'mid ]).
  assert (HeqIOΘ : Θ ⊢ (msubst_ptyp ζs B') ≡ᵗ (msubst_ptyp ζs Ap))
    by (eapply a_tyequiv_msubst; [ exact HeqIO | exact Hwf2 | exact Hζs ]).
  assert (HmsB' : msubst_ptyp (msubst_compose ζs κs) B' = msubst_ptyp ζs B')
    by (eapply msubst_compose_id_ptyp;
        [ exact Hwfmid | exact Hwf2 | exact Hids | exact Hincs | exact Hζs
        | exact HwfB'mid ]).
  assert (HeqW : Θ ⊢ (msubst_ptyp ζb B') ≡ᵗ (msubst_ptyp ζs B')).
  { rewrite <- HmsB'.
    apply (@a_inc_equiv_msubst_ptyp B' Θmid ζb (msubst_compose ζs κs) Θ
             HwfB'mid Heqvs Hwfmid
             ltac:(eapply a_inc_msubst_lc; exact Hζb)
             ltac:(apply msubst_lc_compose;
                   [ eapply a_inc_msubst_lc; exact Hζs
                   | exact (is_id_msubst_values_lc Hids) ])). }
  rewrite btyp_to_ptyp_ptyp_to_btyp_inh.
  eapply a_tyequiv__trans;
    [ apply a_tyequiv__sym; exact HeqIOΘ | ].
  eapply a_tyequiv__trans;
    [ apply a_tyequiv__sym; exact HeqW | exact HeqAll ].
Qed.

(* ===================================================================== *)
(*  The App row's glue helper                                             *)
(* ===================================================================== *)

(** Composing two IDENTITY metasubstitutions is the inner one VERBATIM
    (each entry (α, `α) maps to (α, κc·`α) = (α, `α)). *)
Lemma msubst_compose_id_id : forall κb κc,
  is_id_msubst κb ->
  is_id_msubst κc ->
  msubst_compose κc κb = κb.
Proof.
  intros κb κc Hb Hc.
  induction κb as [ | [α τ] κb' IH ]; [ reflexivity | ].
  apply is_id_msubst_inv in Hb as [-> Hb'].
  unfold msubst_compose in *. simpl.
  rewrite (IH Hb'). f_equal. f_equal.
  clear IH Hb'.
  induction κc as [ | [β σ] κc' IHc ]; [ reflexivity | ].
  apply is_id_msubst_inv in Hc as [-> Hc'].
  simpl. destruct (α == β) as [-> | Hne]; [ reflexivity | exact (IHc Hc') ].
Qed.

(* ===================================================================== *)
(*  The App row — THREE stages: the argument's SKELETON (THEOREM 3, at    *)
(*  (TC, ◇)), the function (the e1 IH at (fn M, P' → P0) — its domain     *)
(*  refinement is the paper's lemma:precision-preserves-refinement step,  *)
(*  its output a SYNTACTIC arrow by [a_typing_fn_arrow_shape]), and the   *)
(*  argument's CHECK (the e2 IH at (TC, ⌈Af⌉), the refinement subject-    *)
(*  transported along ≡ˢ).  The optimality glues all three factorings:    *)
(*  inner glue on stages 2+3, then the outer one with the composed        *)
(*  identity collapsed by [msubst_compose_id_id].                          *)
(* ===================================================================== *)

Lemma a_typing_complete_app : forall M Θ0 P0 e1 e2 κ Θ B,
  a_wf_aenv Θ0 -> a_wf_aenv Θ ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  a_ty_mode_compat M P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_app e1 e2) -> binds α abind_tvar Θ0) ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ0 -> Θ0 ⨟ empty ⊢ₚₛᵃ Ps) ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ -> Θ ⨟ empty ⊢ₚₛᵃ Ps) ->
  lc_exp (exp_app e1 e2) ->
  (* the e1 IH *)
  (forall M' Θ0' P0' κ' Θ' B',
     a_wf_aenv Θ0' -> a_wf_aenv Θ' ->
     Θ0' ⨟ empty ⊢ₚₛᵃ P0' ->
     a_ty_mode_compat M' P0' ->
     κ' ∷ Θ0' ⊑ Θ' ->
     (forall α, α `in` ftvar_in_exp e1 -> binds α abind_tvar Θ0') ->
     (forall y Ps, binds y (abind_var_skl Ps) Θ0' -> Θ0' ⨟ empty ⊢ₚₛᵃ Ps) ->
     (forall y Ps, binds y (abind_var_skl Ps) Θ' -> Θ' ⨟ empty ⊢ₚₛᵃ Ps) ->
     lc_exp e1 ->
     Θ' ⊢ˢᵃ[ M' ] e1 ⦂ B' ->
     Θ' ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ' P0'))
       ⊳ (btyp_to_bskl B') ->
     typ_complete_concl M' Θ0' P0' e1 κ' Θ' B') ->
  (* the e2 IH *)
  (forall M' Θ0' P0' κ' Θ' B',
     a_wf_aenv Θ0' -> a_wf_aenv Θ' ->
     Θ0' ⨟ empty ⊢ₚₛᵃ P0' ->
     a_ty_mode_compat M' P0' ->
     κ' ∷ Θ0' ⊑ Θ' ->
     (forall α, α `in` ftvar_in_exp e2 -> binds α abind_tvar Θ0') ->
     (forall y Ps, binds y (abind_var_skl Ps) Θ0' -> Θ0' ⨟ empty ⊢ₚₛᵃ Ps) ->
     (forall y Ps, binds y (abind_var_skl Ps) Θ' -> Θ' ⨟ empty ⊢ₚₛᵃ Ps) ->
     lc_exp e2 ->
     Θ' ⊢ˢᵃ[ M' ] e2 ⦂ B' ->
     Θ' ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ' P0'))
       ⊳ (btyp_to_bskl B') ->
     typ_complete_concl M' Θ0' P0' e2 κ' Θ' B') ->
  Θ ⊢ˢᵃ[ M ] (exp_app e1 e2) ⦂ B ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (btyp_to_bskl B) ->
  typ_complete_concl M Θ0 P0 (exp_app e1 e2) κ Θ B.
Proof.
  intros M Θ0 P0 e1 e2 κ Θ B Hwf0 HwfΘ HwfP0 Hmod Hinc Hrig Hskl HsklT
         Hlc IH1 IH2 Hd Href.
  inversion Hd; subst.
  match goal with
  | H : ad_pat mode_tc Θ e2 (pskl_to_bskl_syn ?PP) |- _ =>
      rename H into Hd2s; rename PP into P
  end.
  match goal with
  | H : Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh P) ⊳ (btyp_to_bskl ?BB) |- _ =>
      rename H into HrefP; rename BB into B1
  end.
  match goal with
  | H : ad_sd_typing (mode_fn M) Θ e1 (btyp_arrow B1 ?BB) |- _ =>
      rename H into Hd1; rename BB into B2
  end.
  match goal with
  | H : Θ ⊢ (btyp_to_ptyp B1) ≡ᵗ ?AA |- _ =>
      rename H into HeqA2; rename AA into A2
  end.
  match goal with
  | H : ad_sd_typing mode_tc Θ e2 (ptyp_to_btyp_inh A2) |- _ =>
      rename H into Hd2
  end.
  simpl in Hrig.
  assert (Hrig1 : forall α, α `in` ftvar_in_exp e1 -> binds α abind_tvar Θ0)
    by (intros α Hα; apply Hrig; clear - Hα; fsetdec).
  assert (Hrig2 : forall α, α `in` ftvar_in_exp e2 -> binds α abind_tvar Θ0)
    by (intros α Hα; apply Hrig; clear - Hα; fsetdec).
  assert (Hlc1 : lc_exp e1) by (inversion Hlc; assumption).
  assert (Hlc2 : lc_exp e2) by (inversion Hlc; assumption).
  assert (Hexp2 : a_wf_exp Θ0 e2)
    by (apply a_wf_exp_of_tvarish;
        [ exact Hlc2 | intros α Hα; left; apply Hrig2; exact Hα ]).
  (* the fn premise's target is wf — components pulled by inversion *)
  assert (HwfArr : a_wf_ptyp Θ (btyp_to_ptyp (btyp_arrow B1 B2)))
    by (eapply ad_sd_typing_target_wf; [ exact Hd1 | exact HwfΘ ]).
  simpl in HwfArr.
  inversion HwfArr; subst.
  match goal with
  | H1 : a_wf_ptyp Θ (btyp_to_ptyp B1),
    H2 : a_wf_ptyp Θ (btyp_to_ptyp B2) |- _ =>
      rename H1 into HwfB1; rename H2 into HwfB2
  end.
  assert (HwfP : Θ ⨟ empty ⊢ₚₛᵃ P).
  { pose proof (ad_pat_target_wf Hd2s HwfΘ) as Hw.
    rewrite bskl_to_pskl_pskl_to_bskl_syn in Hw. exact Hw. }
  (* ---- 1. the SKELETON stage : THEOREM 3 at (TC, ◇) ---- *)
  destruct (@a_pat_complete e2 mode_tc Θ0 pskl_hole κ Θ (pskl_to_bskl_syn P)
              Hwf0 HwfΘ (a_wf_pskl__hole _ _) a_sk_mode_compat__tc Hinc
              Hrig2 Hskl HsklT Hlc2 Hd2s
              ltac:(cbn [msubst_pskl pskl_to_bskl_inh];
                    apply ad_refine_syn__hole; exact HwfP))
    as [P' [Θ1' [Hrun1 Hopt1]]].
  destruct (a_pat_sound Hrun1 Hwf0 Hskl (a_wf_pskl__hole _ _)
              a_sk_mode_compat__tc Hexp2)
    as [Hle1 [Hwf1 _]].
  destruct Hle1 as [[κ1b [Hid1b Hinc1b]] _].
  destruct (Hopt1 κ1b Hid1b Hinc1b) as [ζ1 [Hζ1 [Heqv1 Hprec1]]].
  rewrite bskl_to_pskl_pskl_to_bskl_syn in Hprec1.
  (* ---- 2. the FUNCTION stage : IH1 at (fn M, P' → P0) ---- *)
  assert (HwfP' : Θ1' ⨟ empty ⊢ₚₛᵃ P')
    by (eapply a_pat_output_wf;
        [ exact Hrun1 | exact Hwf0 | exact Hskl
        | apply a_wf_pskl__hole | apply a_sk_mode_compat__tc | exact Hexp2 ]).
  assert (HwfP0m : Θ1' ⨟ empty ⊢ₚₛᵃ P0).
  { pose proof (a_wf_pskl_msubst_inc Hinc1b Hwf0 HwfP0
                  ltac:(intros α Hα; clear - Hα; fsetdec)) as Hw.
    rewrite (msubst_pskl_id P0 Hid1b) in Hw. exact Hw. }
  assert (Hskl1 : forall y Ps, binds y (abind_var_skl Ps) Θ1' ->
             Θ1' ⨟ empty ⊢ₚₛᵃ Ps).
  { intros y Ps Hb.
    assert (Hb0 : binds y (abind_var_skl Ps) Θ0)
      by (eapply a_pat_tm_ge; [ exact Hrun1 | exact I | exact Hb ]).
    pose proof (a_wf_pskl_msubst_inc Hinc1b Hwf0 (Hskl _ _ Hb0)
                  ltac:(intros α Hα; clear - Hα; fsetdec)) as Hw.
    rewrite (msubst_pskl_id Ps Hid1b) in Hw. exact Hw. }
  assert (Hrig1m : forall α, α `in` ftvar_in_exp e1 -> binds α abind_tvar Θ1')
    by (intros α Hα; eapply a_inc_binds_tvar;
        [ exact Hinc1b | apply Hrig1; exact Hα ]).
  (* the codomain refinement, transported to ζ1 (the Anno idiom) *)
  assert (Hσ1 : msubst_compose ζ1 κ1b ∷ Θ0 ⊑ Θ)
    by (eapply a_inc_compose;
        [ exact Hinc1b | exact Hwf0 | exact Hwf1 | exact Hζ1 ]).
  assert (HwfQ2 : Θ ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl (btyp_to_bskl B2))).
  { rewrite bskl_to_pskl_btyp.
    apply a_wf_ptyp_to_wf_pskl. exact HwfB2. }
  assert (Hpp1 : Θ ⨟ empty ⊢ₚᵣᵃ
                   (msubst_pskl (msubst_compose ζ1 κ1b) P0)
                   ⊑ (msubst_pskl κ P0)).
  { eapply a_inc_equiv_precise_msubst_flip with (Θ0 := Θ0) (Δ0 := empty);
      [ exact HwfP0 | exact Hwf0 | exact HwfΘ | exact Hinc | exact Hσ1
      | exact Heqv1 | clear; fsetdec ]. }
  assert (Hcod : Θ ⨟ empty ⊢ᵣᵃ
                   (pskl_to_bskl_inh (msubst_pskl (msubst_compose ζ1 κ1b) P0))
                   ⊳ (btyp_to_bskl B2)).
  { eapply ad_precise_preserves_refine;
      [ exact Hpp1 | exact Href | exact HwfΘ
      | intros α Hα; clear - Hα; fsetdec | exact HwfQ2 ]. }
  assert (Hms1 : msubst_pskl (msubst_compose ζ1 κ1b) P0 = msubst_pskl ζ1 P0).
  { eapply msubst_compose_id_pskl;
      [ exact Hwf0 | exact Hwf1 | exact Hid1b | exact Hinc1b | exact Hζ1
      | eapply a_wf_pskl_to_a_scope_pskl;
          [ exact HwfP0 | intros z b Hb; exact Hb
          | intros α Hα; clear - Hα; fsetdec ] ]. }
  rewrite Hms1 in Hcod.
  (* the domain refinement : precision preserves the rule's own (paper's
     lemma:precision-preserves-refinement, verbatim) *)
  assert (HwfB1e : Θ ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl (btyp_to_bskl B1))).
  { rewrite bskl_to_pskl_btyp.
    apply a_wf_ptyp_to_wf_pskl. exact HwfB1. }
  assert (Hdom : Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl ζ1 P'))
                   ⊳ (btyp_to_bskl B1)).
  { eapply ad_precise_preserves_refine;
      [ exact Hprec1 | exact HrefP | exact HwfΘ
      | intros α Hα; clear - Hα; fsetdec | exact HwfB1e ]. }
  destruct (IH1 (mode_fn M) Θ1' (pskl_arrow P' P0) ζ1 Θ (btyp_arrow B1 B2)
              Hwf1 HwfΘ
              ltac:(apply a_wf_pskl__arrow; [ exact HwfP' | exact HwfP0m ])
              ltac:(apply a_ty_mode_compat__fn; exact Hmod)
              Hζ1 Hrig1m Hskl1 HsklT Hlc1 Hd1
              ltac:(cbn [msubst_pskl pskl_to_bskl_inh btyp_to_bskl];
                    apply ad_refine_syn__arrow; [ exact Hdom | exact Hcod ]))
    as [C [Θ2' [Hrun2 Hopt2]]].
  (* the output is a SYNTACTIC arrow *)
  pose proof (a_typing_fn_arrow_shape Hrun2) as Hshape.
  inversion Hshape; subst.
  match goal with
  | Hs : fn_arrow_shape M ?BB |- _ => idtac
  end.
  match goal with
  | H : a_typing (mode_fn M) Θ1' _ e1 (ptyp_arrow ?AA ?BB) _ |- _ =>
      rename AA into Af; rename BB into Bf
  end.
  (* soundness of the function run *)
  assert (Hexp1 : a_wf_exp Θ1' e1)
    by (apply a_wf_exp_of_tvarish;
        [ exact Hlc1 | intros α Hα; left; apply Hrig1m; exact Hα ]).
  destruct (a_typing_sound Hrun2 Hwf1 Hskl1
              ltac:(apply a_wf_pskl__arrow; [ exact HwfP' | exact HwfP0m ])
              ltac:(apply a_ty_mode_compat__fn; exact Hmod)
              Hexp1)
    as [Hle2 [Hwf2 [HwfC _]]].
  destruct Hle2 as [[κ2b [Hid2b Hinc2b]] _].
  destruct (Hopt2 κ2b Hid2b Hinc2b) as [ζ2 [Hζ2 [Heqv2 Heq2]]].
  simpl in Heq2.
  (* invert the arrow equivalence *)
  inversion HwfC; subst.
  match goal with
  | H1 : a_wf_ptyp Θ2' Af, H2 : a_wf_ptyp Θ2' Bf |- _ =>
      rename H1 into HwfAf; rename H2 into HwfBf
  end.
  destruct (a_tyequiv_arrow_inv HwfΘ
              ltac:(eapply msubst_ptyp_lc;
                    [ exact Hζ2 | eapply a_wf_ptyp_lc; exact HwfAf ])
              ltac:(eapply msubst_ptyp_lc;
                    [ exact Hζ2 | eapply a_wf_ptyp_lc; exact HwfBf ])
              ltac:(eapply a_wf_ptyp_lc; exact HwfB1)
              ltac:(eapply a_wf_ptyp_lc; exact HwfB2)
              Heq2)
    as [HeqDom HeqCod].
  (* ---- 3. the ARGUMENT stage : IH2 at (TC, ⌈Af⌉) ---- *)
  assert (HwfA2 : a_wf_ptyp Θ A2)
    by (eapply (proj1 (a_tyequiv_wf_iff HeqA2 (fun x b h => h) HwfΘ));
        exact HwfB1).
  assert (Hrig2m : forall α, α `in` ftvar_in_exp e2 -> binds α abind_tvar Θ2')
    by (intros α Hα; eapply a_inc_binds_tvar;
        [ exact Hinc2b
        | eapply a_inc_binds_tvar;
            [ exact Hinc1b | apply Hrig2; exact Hα ] ]).
  assert (Hskl2 : forall y Ps, binds y (abind_var_skl Ps) Θ2' ->
             Θ2' ⨟ empty ⊢ₚₛᵃ Ps).
  { intros y Ps Hb.
    assert (Hb1 : binds y (abind_var_skl Ps) Θ1')
      by (exact (a_typing_tm_ge Hrun2 y (abind_var_skl Ps) I Hb)).
    pose proof (a_wf_pskl_msubst_inc Hinc2b Hwf1 (Hskl1 _ _ Hb1)
                  ltac:(intros α Hα; clear - Hα; fsetdec)) as Hw.
    rewrite (msubst_pskl_id Ps Hid2b) in Hw. exact Hw. }
  assert (Hexp2m : a_wf_exp Θ2' e2)
    by (apply a_wf_exp_of_tvarish;
        [ exact Hlc2 | intros α Hα; left; apply Hrig2m; exact Hα ]).
  assert (HeqChain : Θ ⊢ (msubst_ptyp ζ2 Af) ≡ᵗ A2)
    by (eapply a_tyequiv__trans; [ exact HeqDom | exact HeqA2 ]).
  assert (Heqs : Θ ⊢ (ptyp_to_pskl (msubst_ptyp ζ2 Af)) ≡ˢ (ptyp_to_pskl A2))
    by (apply a_tyequiv_embed_pskl; exact HeqChain).
  assert (Href3 : Θ ⨟ empty ⊢ᵣᵃ
                    (pskl_to_bskl_inh (msubst_pskl ζ2 (ptyp_to_pskl Af)))
                    ⊳ (btyp_to_bskl (ptyp_to_btyp_inh A2))).
  { rewrite msubst_pskl_embed_ptyp, <- (pskl_to_bskl_inh_ptyp A2).
    eapply ad_refine_syn_f_forget.
    eapply (proj2 (skl_tyequiv_refine_syn_f_transport Heqs HwfΘ
                     (fun x b h => h))).
    apply ad_refine_syn_f_of_plain.
    apply ad_refine_syn_refl_inh.
    apply a_wf_ptyp_to_wf_pskl. exact HwfA2. }
  destruct (IH2 mode_tc Θ2' (ptyp_to_pskl Af) ζ2 Θ (ptyp_to_btyp_inh A2)
              Hwf2 HwfΘ
              ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfAf)
              (a_ty_mode_compat__tc Af)
              Hζ2 Hrig2m Hskl2 HsklT Hlc2 Hd2 Href3)
    as [A3 [Θ3' [Hrun3 Hopt3]]].
  (* ---- 4. the run ---- *)
  exists Bf, Θ3'.
  split.
  { eapply a_typing__app; [ exact Hrun1 | exact Hrun2 | exact Hrun3 ]. }
  (* ---- 5. optimality : the TRIPLE glue ---- *)
  intros κ1 Hκid Hκinc.
  assert (Heqκ : κ1 = κ1b)
    by (eapply a_inc_id_msubst_unique;
        [ exact Hκinc | exact Hinc1b | exact Hκid | exact Hid1b ]).
  destruct (a_typing_sound Hrun3 Hwf2 Hskl2
              ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfAf)
              (a_ty_mode_compat__tc Af) Hexp2m)
    as [Hle3 [Hwf3 _]].
  destruct Hle3 as [[κ3b [Hid3b Hinc3b]] _].
  destruct (Hopt3 κ3b Hid3b Hinc3b) as [ζ3 [Hζ3 [Heqv3 _]]].
  exists ζ3.
  split; [ exact Hζ3 | ].
  split.
  { (* inner glue: stages 2+3 *)
    assert (Hglue23 : a_inc_equiv Θ1' ζ1 (msubst_compose ζ3 κ2b) Θ).
    { eapply a_inc_equiv_glue with
        (Θmid := Θ2') (Θfin := Θ3') (κ1b := κ3b) (ζ1 := ζ2);
        [ exact Hwf1 | exact Hwf2 | exact Hwf3 | exact HwfΘ
        | exact Hid2b | exact Hid3b
        | intros α Hα;
          pose proof (a_inc_dom_flex Hinc2b Hα) as Hfα;
          eapply a_inc_flex_dom;
            [ exact Hinc3b | exact Hwf2
            | eapply a_inc_id_flex_preserve;
                [ exact Hinc2b | exact Hid2b | exact Hwf1 | exact Hfα ] ]
        | exact Hinc2b | exact Hinc3b | exact Hζ2 | exact Hζ3
        | exact Heqv2 | exact Heqv3 ]. }
    (* outer glue: stage 1 + the combined tail; the composed identity
       collapses to the inner one VERBATIM ([msubst_compose_id_id]) *)
    assert (Hinc23 : msubst_compose κ3b κ2b ∷ Θ1' ⊑ Θ3')
      by (eapply a_inc_compose;
          [ exact Hinc2b | exact Hwf1 | exact Hwf2 | exact Hinc3b ]).
    rewrite (msubst_compose_id_id Hid2b Hid3b) in Hinc23.
    assert (Hglue : a_inc_equiv Θ0 κ (msubst_compose ζ3 κ1b) Θ).
    { eapply a_inc_equiv_glue with
        (Θmid := Θ1') (Θfin := Θ3') (κ1b := κ2b) (ζ1 := ζ1);
        [ exact Hwf0 | exact Hwf1 | exact Hwf3 | exact HwfΘ
        | exact Hid1b | exact Hid2b
        | intros α Hα;
          pose proof (a_inc_dom_flex Hinc1b Hα) as Hfα;
          eapply a_inc_flex_dom;
            [ exact Hinc23 | exact Hwf1
            | eapply a_inc_id_flex_preserve;
                [ exact Hinc1b | exact Hid1b | exact Hwf0 | exact Hfα ] ]
        | exact Hinc1b | exact Hinc23 | exact Hζ1 | exact Hζ3
        | exact Heqv1 | exact Hglue23 ]. }
    rewrite Heqκ. exact Hglue. }
  (* ---- 6. the ≡ᵗ conclusion : the codomain pushed ζ2 → ζ3 ---- *)
  assert (HmsBf : msubst_ptyp (msubst_compose ζ3 κ3b) Bf = msubst_ptyp ζ3 Bf)
    by (eapply msubst_compose_id_ptyp;
        [ exact Hwf2 | exact Hwf3 | exact Hid3b | exact Hinc3b | exact Hζ3
        | exact HwfBf ]).
  assert (HeqW : Θ ⊢ (msubst_ptyp ζ2 Bf) ≡ᵗ (msubst_ptyp ζ3 Bf)).
  { rewrite <- HmsBf.
    apply (@a_inc_equiv_msubst_ptyp Bf Θ2' ζ2 (msubst_compose ζ3 κ3b) Θ
             HwfBf Heqv3 Hwf2
             ltac:(eapply a_inc_msubst_lc; exact Hζ2)
             ltac:(apply msubst_lc_compose;
                   [ eapply a_inc_msubst_lc; exact Hζ3
                   | exact (is_id_msubst_values_lc Hid3b) ])). }
  eapply a_tyequiv__trans;
    [ apply a_tyequiv__sym; exact HeqW | exact HeqCod ].
Qed.

(* ===================================================================== *)
(*  §6.3 #3 — guess^TY EXISTENCE with an AVOID SET.  Completeness         *)
(*  CHOOSES the block, so this settles [AT-Abs]'s [uniq (αs ++ Θ1)]       *)
(*  premise; the "two independent generators" gap closes because the      *)
(*  arrow case feeds the first half's names into the second's avoid set.  *)
(* ===================================================================== *)

(** Two uniq lists with disjoint domains append to a uniq list. *)
Lemma uniq_app_of : forall (Ξ1 Ξ2 : aenv),
  uniq Ξ1 -> uniq Ξ2 ->
  (forall α, α `in` dom Ξ1 -> α `notin` dom Ξ2) ->
  uniq (Ξ1 ++ Ξ2).
Proof.
  intros Ξ1; induction Ξ1 as [ | [α b] Ξ1' IH ]; intros Ξ2 Hu1 Hu2 Hdj;
    [ exact Hu2 | ].
  inversion Hu1; subst.
  simpl_env. apply uniq_cons.
  - apply IH; [ assumption | exact Hu2 | ].
    intros β Hβ. apply Hdj. simpl. clear - Hβ; fsetdec.
  - rewrite dom_app.
    assert (Hα2 : α `notin` dom Ξ2)
      by (apply Hdj; simpl; clear; fsetdec).
    match goal with
    | Hn : α `notin` dom Ξ1' |- _ => clear - Hn Hα2; fsetdec
    end.
Qed.

(** ⭐ [guess^TY] EXISTENCE, with an AVOID SET: completeness CHOOSES the
    block, so an avoid-set-indexed generator settles [AT-Abs]'s
    [uniq (αs ++ Θ1)] premise (hand-off §6.3 #3; the "two independent
    generators" gap is closed by feeding the first half's names into the
    second half's avoid set at the arrow). *)
Lemma a_guess_mono_exists : forall P Θ L,
  lc_pskl P ->
  exists Ξ A,
    a_guess_mono Θ P Ξ A /\
    a_decls Ξ /\ uniq Ξ /\
    (forall α, α `in` dom Ξ -> α `notin` L).
Proof.
  intros P Θ L Hlc; revert Θ L; induction Hlc; intros Θ L.
  - (* unit *)
    exists nil, ptyp_unit. repeat split;
      [ apply a_guess_mono__unit | apply a_decls__nil | apply uniq_nil
      | intros β Hβ; simpl in Hβ; clear - Hβ; fsetdec ].
  - (* var_f *)
    exists nil, (ptyp_var_f α). repeat split;
      [ apply a_guess_mono__var | apply a_decls__nil | apply uniq_nil
      | intros β Hβ; simpl in Hβ; clear - Hβ; fsetdec ].
  - (* arrow *)
    destruct (IHHlc1 Θ L) as [Ξ1 [A [Hg1 [Hd1 [Hu1 Hav1]]]]].
    destruct (IHHlc2 Θ (L `union` dom Ξ1)) as [Ξ2 [B [Hg2 [Hd2 [Hu2 Hav2]]]]].
    exists (Ξ1 ++ Ξ2), (ptyp_arrow A B).
    repeat split.
    + apply a_guess_mono__arrow; [ exact Hg1 | exact Hg2 ].
    + clear - Hd1 Hd2. induction Hd1; simpl_env;
        [ exact Hd2 | apply a_decls__cons; assumption ].
    + apply uniq_app_of; [ exact Hu1 | exact Hu2 | ].
      intros α Hα Hα2.
      pose proof (Hav2 α Hα2) as Hn. clear - Hn Hα; fsetdec.
    + intros α Hα. rewrite dom_app in Hα.
      destruct (AtomSetImpl.union_1 Hα) as [H1 | H2];
        [ apply Hav1; exact H1 | apply Hav2 in H2; clear - H2; fsetdec ].
  - (* all *)
    destruct (atom_fresh (ftvar_in_aenv Θ `union` ftvar_in_pskl P1 `union` L))
      as [β Hβ].
    destruct (H0 β ((β ~ abind_tvar) ++ Θ) L) as [Ξ [A [Hg [Hd [Hu Hav]]]]].
    exists Ξ, (ptyp_all (close_ptyp_wrt_ptyp β A)).
    repeat split;
      [ apply a_guess_mono__forall;
          [ clear - Hβ; fsetdec | exact Hg ]
      | exact Hd | exact Hu | exact Hav ].
  - (* hole *)
    destruct (atom_fresh (ftvar_in_aenv Θ `union` L)) as [α Hα].
    exists ((α ~ abind_flex_mono) ++ nil), (ptyp_var_f α).
    repeat split;
      [ apply a_guess_mono__hole; clear - Hα; fsetdec
      | apply a_decls__cons; apply a_decls__nil
      | apply uniq_cons; [ apply uniq_nil | simpl; clear; fsetdec ]
      | intros β Hβ; simpl in Hβ;
        assert (β = α) by (clear - Hβ; fsetdec); subst;
        clear - Hα; fsetdec ].
  - (* tophole *)
    destruct (IHHlc Θ L) as [Ξ [A [Hg [Hd [Hu Hav]]]]].
    exists Ξ, A.
    repeat split;
      [ apply a_guess_mono__tophole; exact Hg
      | exact Hd | exact Hu | exact Hav ].
Qed.
