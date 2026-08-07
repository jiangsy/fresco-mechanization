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
  (* the counterpart's wf : scope from the join, ghost-freeness structurally *)
  assert (HwfQ : Θ ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl (btyp_to_bskl B))).
  { rewrite bskl_to_pskl_btyp.
    apply a_wf_ptyp_to_wf_pskl.
    eapply a_wf_ptyp_of_scope_pskl;
      [ | rewrite <- bskl_to_pskl_btyp; reflexivity ].
    eapply ad_pat_sub_target_wf. exact (ad_pat_sub_of_v (ex_intro _ njoin Hjoin)). }
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
  (* precision between two type paintings IS the equivalence *)
  rewrite msubst_bskl_syn_erase, msubst_pskl_embed_ptyp, bskl_to_pskl_btyp
    in Hprec.
  unfold ad_precise in Hprec.
  rewrite (pskl_to_bskl_inh_ptyp (btyp_to_ptyp B)) in Hprec.
  pose proof (ad_refine_syn_inh_tyequiv Hprec HwfΘ
                (msubst_ptyp ζ A1) (ptyp_to_btyp_inh (btyp_to_ptyp B))
                eq_refl eq_refl) as Heq.
  rewrite btyp_to_ptyp_ptyp_to_btyp_inh in Heq.
  exact Heq.
Qed.
