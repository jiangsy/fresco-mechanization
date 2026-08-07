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
