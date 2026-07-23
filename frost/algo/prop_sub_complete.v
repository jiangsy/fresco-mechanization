(** COMPLETENESS + OPTIMALITY OF ALGORITHMIC SUBTYPING.

    Paper: [thm:complete-subtyping] (algorithmic.tex:1446); proofs
    subtyping-proofs.tex:1526-3536.  Plan: docs/DESIGN-completeness-subtyping.md.

    This file builds bottom-up.  P5a (this commit): the fuel-indexed
    measure [ad_pat_sub_n] (def in def_decl_algo_sub.v) and its bridges to
    the plain [ad_pat_sub] — [of_n] / [to_n] / [n_mono] — plus the
    fuel-preserving tvar-rename [ad_pat_sub_n_rename_tvar] that [to_n]'s
    binder cases need for the ∀α∃n → ∃n∀α swap. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_skeleton.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo_sub.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_consis_sound.
Require Import src.frost.algo.prop_consis_complete.
Require Import src.frost.algo.prop_mono_bridge.
Require Import src.frost.algo.prop_precise.
Require Import src.frost.algo.prop_decorate.
Require Import src.frost.algo.prop_pat_sub.

Set Implicit Arguments.

(* ===================================================================== *)
(*  P5a — the fuel measure and its bridges to plain [ad_pat_sub].          *)
(* ===================================================================== *)

(** Erase the fuel: a fuel-indexed derivation IS a plain one. *)
Lemma ad_pat_sub_of_n : forall n NM M Ψ Θ R Q,
  ad_pat_sub_n n NM M Ψ Θ R Q ->
  Ψ ⨟ Θ ⊢ₛᵃ[ NM | M ] R ⩽ Q.
Proof.
  intros n NM M Ψ Θ R Q H. induction H.
  - eapply ad_pat_sub__infer; eauto.
  - eapply ad_pat_sub__check; eauto.
  - eapply ad_pat_sub__forall_r; eauto.
  - eapply ad_pat_sub__univ_ghost_r; eauto.
  - eapply ad_pat_sub__arrow; eauto.
  - eapply ad_pat_sub__forall_l_tagged; eauto.
  - eapply ad_pat_sub__forall_l_untagged; eauto.
  - eapply ad_pat_sub__ghost; eauto.
  - eapply ad_pat_sub__ghostg; eauto.
  - eapply ad_pat_sub__univ_ghost_l; eauto.
  - eapply ad_pat_sub__univ_ghost_lg; eauto.
  - eapply ad_pat_sub__flex_mono; eauto.
Qed.

(** One extra unit of fuel is harmless.  Each rule concludes at [S n] from
    a recursive premise at [n]; bumping the conclusion to [S (S n)] just
    applies the same constructor with its premise supplied by the IH (now
    at [S n]). *)
Lemma ad_pat_sub_n_succ : forall n NM M Ψ Θ R Q,
  ad_pat_sub_n n NM M Ψ Θ R Q ->
  ad_pat_sub_n (S n) NM M Ψ Θ R Q.
Proof.
  intros n NM M Ψ Θ R Q H. induction H.
  - eapply ad_pat_sub_n__infer; eauto.
  - eapply ad_pat_sub_n__check; eauto.
  - eapply ad_pat_sub_n__forall_r with (L := L); eauto.
  - eapply ad_pat_sub_n__univ_ghost_r; eauto.
  - eapply ad_pat_sub_n__arrow; eauto.
  - eapply ad_pat_sub_n__forall_l_tagged; eauto.
  - eapply ad_pat_sub_n__forall_l_untagged; eauto.
  - eapply ad_pat_sub_n__ghost; eauto.
  - eapply ad_pat_sub_n__ghostg; eauto.
  - eapply ad_pat_sub_n__univ_ghost_l; eauto.
  - eapply ad_pat_sub_n__univ_ghost_lg; eauto.
  - eapply ad_pat_sub_n__flex_mono; eauto.
Qed.

(** Fuel weakening: more fuel than needed is harmless. *)
Lemma ad_pat_sub_n_mono : forall n NM M Ψ Θ R Q,
  ad_pat_sub_n n NM M Ψ Θ R Q ->
  forall m, n <= m ->
  ad_pat_sub_n m NM M Ψ Θ R Q.
Proof.
  intros n NM M Ψ Θ R Q H m Hle.
  induction Hle; [ assumption | ].
  apply ad_pat_sub_n_succ; assumption.
Qed.

(** Renaming the opened rigid binder in [ad_pat_sub_n] — the fuel-preserving
    mirror of [ad_pat_sub_rename_tvar] (prop_pat_sub.v).  The fuel [n] rides
    along inertly; [to_n]'s binder cases use it to turn the cofinite family
    [∀α∉L, ∃n, …] into [∃n, ∀α∉L, …]. *)
Lemma ad_pat_sub_n_rename_tvar : forall n NM M Ψ Θ1 α Θ0 S Q Y,
  ad_pat_sub_n n NM M Ψ (Θ1 ++ (α ~ abind_tvar) ++ Θ0) S Q ->
  α `notin` dom (Θ1 ++ Θ0) ->
  (forall β τ, binds β (abind_flex_mono_def τ) (Θ1 ++ Θ0) ->
     α `notin` ftvar_in_ptyp τ) ->
  ad_pat_sub_n n NM M Ψ (Θ1 ++ (Y ~ abind_tvar) ++ Θ0)
      (subst_bskl_in_uskl (uskl_var_f Y) α S)
      (subst_bskl_in_bskl (bskl_var_f Y) α Q).
Proof.
  intros * H.
  remember (Θ1 ++ (α ~ abind_tvar) ++ Θ0) as Θfull eqn:HeqΘ.
  revert Θ1 HeqΘ.
  induction H; intros Θ1 ->; intros Hdom Hdefs; simpl.
  - apply ad_pat_sub_n__infer; auto.
    + apply ad_pat_consis_rename_tvar; auto.
    + change (bskl_var_f Y) with (ptyp_to_bskl_syn (ptyp_var_f Y)).
      apply is_sskl_subst_mono; auto using mono_ptyp.
  - rewrite subst_var_bskl_inh.
    apply ad_pat_sub_n__check.
    + change (uskl_var_f Y) with (ptyp_to_uskl_syn (ptyp_var_f Y)).
      apply guarded_uskl_subst_mono; auto using mono_ptyp.
    + apply guarded_pskl_subst; auto using guarded_pskl__var, lc_pskl_var_f.
    + rewrite <- subst_var_bskl_inh.
      apply ad_pat_consis_rename_tvar; auto.
  - apply ad_pat_sub_n__forall_r with (L := L `union` singleton α).
    intros X HX.
    assert (Hαx : α <> X) by fsetdec.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
    assert (HXL : X `notin` L) by fsetdec.
    apply (H0 X HXL ((X ~ abind_tvar) ++ Θ1));
      [ simpl_env; reflexivity
      | simpl; repeat rewrite dom_app in *; fsetdec
      | intros β τ Hb;
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
        [ discriminate | eauto ] ].
  - apply ad_pat_sub_n__univ_ghost_r; auto.
    + change (uskl_var_f Y) with (ptyp_to_uskl_syn (ptyp_var_f Y)).
      apply guarded_uskl_subst_mono; auto using mono_ptyp.
    + change (bskl_var_f Y) with (ptyp_to_bskl_syn (ptyp_var_f Y)).
      apply guarded_bskl_subst_mono; auto using mono_ptyp.
    + change (bskl_var_f Y) with (ptyp_to_bskl_syn (ptyp_var_f Y)).
      apply is_sskl_subst_mono; auto using mono_ptyp.
    + apply ad_pat_consis_rename_tvar; auto.
  - specialize (IHad_pat_sub_n Θ1 ltac:(reflexivity) Hdom Hdefs).
    eapply ad_pat_sub_n__arrow.
    + eapply ad_pat_consis_rename_tvar; eauto.
    + exact IHad_pat_sub_n.
    + eassumption.
  - specialize (IHad_pat_sub_n Θ1 ltac:(reflexivity) Hdom Hdefs).
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl in IHad_pat_sub_n;
      [ | apply lc_uskl_var_f ].
    eapply ad_pat_sub_n__forall_l_tagged.
    5: exact IHad_pat_sub_n.
    + assumption.
    + eassumption.
    + change (uskl_var_f Y) with (ptyp_to_uskl_syn (ptyp_var_f Y)).
      apply a_tags_sort_subst_mono;
        [ assumption | apply mono_ptyp__var ].
    + change (uskl_var_f Y) with (ptyp_to_uskl_syn (ptyp_var_f Y)).
      rewrite uskl_to_pskl_subst_mono. simpl.
      apply a_wf_pskl_rename_tvar;
        first [ assumption | clear; fsetdec ].
  - specialize (IHad_pat_sub_n Θ1 ltac:(reflexivity) Hdom Hdefs).
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl in IHad_pat_sub_n;
      [ | apply lc_uskl_var_f ].
    eapply ad_pat_sub_n__forall_l_untagged.
    5: exact IHad_pat_sub_n.
    + assumption.
    + eassumption.
    + change (uskl_var_f Y) with (ptyp_to_uskl_syn (ptyp_var_f Y)).
      apply a_tags_sort_subst_mono;
        [ assumption | apply mono_ptyp__var ].
    + change (uskl_var_f Y) with (ptyp_to_uskl_syn (ptyp_var_f Y)).
      rewrite uskl_to_pskl_subst_mono. simpl.
      apply a_wf_pskl_rename_tvar;
        first [ assumption | clear; fsetdec ].
  - rewrite subst_var_bskl_inh.
    apply ad_pat_sub_n__ghost; auto.
    + apply a_wf_pskl_rename_tvar; [ assumption | clear; fsetdec ].
    + rewrite <- subst_var_bskl_inh.
      change (bskl_var_f Y) with (ptyp_to_bskl_syn (ptyp_var_f Y)).
      apply mod_comp_sk_subst_mono; auto using mono_ptyp.
  - apply ad_pat_sub_n__ghostg; auto.
  - apply ad_pat_sub_n__univ_ghost_l; auto.
  - apply ad_pat_sub_n__univ_ghost_lg; auto.
  - match goal with
    | |- context [ if ?e then _ else _ ] => destruct e as [-> | Hne]
    end.
    + exfalso.
      match goal with
      | Hb : binds _ (abind_flex_mono_def _) _ |- _ =>
          unfold binds in Hb; apply in_app_or in Hb;
          destruct Hb as [Hb | Hb];
          [ apply binds_In in Hb; simpl_env in *; fsetdec | ];
          apply in_app_or in Hb; destruct Hb as [Hb | Hb];
          [ destruct Hb as [Heq | Habs]; [ inversion Heq | inversion Habs ]
          | apply binds_In in Hb; simpl_env in *; fsetdec ]
      end.
    + match goal with
      | Hb0 : binds ?a (abind_flex_mono_def _) (_ ++ _ ++ _) |- _ =>
          assert (Hb' : binds a (abind_flex_mono_def τ) (Θ1 ++ Θ0))
            by (eapply binds_strip_mid;
                [ exact Hb0 | intro He; inversion He ])
      end.
      eapply ad_pat_sub_n__flex_mono.
      { unfold binds in Hb' |- *. apply in_app_or in Hb'.
        apply in_or_app.
        destruct Hb' as [Hb' | Hb'];
          [ left; exact Hb' | right; simpl; right; exact Hb' ]. }
      specialize (IHad_pat_sub_n Θ1 ltac:(reflexivity) Hdom Hdefs).
      rewrite subst_bskl_in_uskl_fresh_eq in IHad_pat_sub_n;
        [ exact IHad_pat_sub_n | ].
      rewrite ftvar_in_uskl_ptyp_syn. eauto.
Qed.

(** Every plain derivation has some fuel.  Binder cases pick a fresh
    witness, read off its fuel, and transport that same fuel to every
    other opening via [ad_pat_sub_n_rename_tvar]. *)
Lemma ad_pat_sub_to_n : forall NM M Ψ Θ R Q,
  a_wf_aenv Θ ->
  Ψ ⨟ Θ ⊢ₛᵃ[ NM | M ] R ⩽ Q ->
  exists n, ad_pat_sub_n n NM M Ψ Θ R Q.
Proof.
  intros NM M Ψ Θ R Q Hwf H. revert Hwf. induction H; intros Hwf.
  - exists 1. eapply ad_pat_sub_n__infer; eauto.
  - exists 1. eapply ad_pat_sub_n__check; eauto.
  - (* forall_r — pick a fresh witness, read off its fuel, transport by rename *)
    pick fresh α0 for
      (L `union` dom Θ `union` ftvar_in_uskl T `union` ftvar_in_bskl B).
    assert (Hwf0 : a_wf_aenv ((α0 ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - Fr; fsetdec | exact Hwf ]).
    destruct (H0 α0 ltac:(fsetdec) Hwf0) as [n0 Hn0].
    exists (S n0).
    eapply ad_pat_sub_n__forall_r with
      (L := L `union` dom Θ `union` ftvar_in_uskl T
            `union` ftvar_in_bskl B `union` singleton α0).
    intros X HX.
    rewrite (subst_bskl_in_bskl_intro α0);
      [ | clear - Fr; fsetdec ].
    rewrite <- (subst_bskl_in_uskl_fresh_eq T (uskl_var_f X) α0);
      [ | clear - Fr; fsetdec ].
    replace ((X ~ abind_tvar) ++ Θ)
       with (nil ++ (X ~ abind_tvar) ++ Θ) by (simpl_env; reflexivity).
    apply ad_pat_sub_n_rename_tvar.
    + simpl_env. exact Hn0.
    + simpl_env. clear - Fr; fsetdec.
    + intros β τ Hb. simpl_env in Hb.
      assert (Hsc : ftvar_in_ptyp τ [<=] dom Θ)
        by (eapply a_wf_aenv_def_ftv_dom; [ exact Hwf | exact Hb ]).
      clear - Fr Hsc; fsetdec.
  - exists 1. eapply ad_pat_sub_n__univ_ghost_r; eauto.
  - destruct (IHad_pat_sub Hwf) as [n Hn].
    exists (S n). eapply ad_pat_sub_n__arrow; eauto.
  - destruct (IHad_pat_sub Hwf) as [n Hn].
    exists (S n). eapply ad_pat_sub_n__forall_l_tagged; eauto.
  - destruct (IHad_pat_sub Hwf) as [n Hn].
    exists (S n). eapply ad_pat_sub_n__forall_l_untagged; eauto.
  - exists 1. eapply ad_pat_sub_n__ghost; eauto.
  - exists 1. eapply ad_pat_sub_n__ghostg; eauto.
  - destruct (IHad_pat_sub Hwf) as [n Hn].
    exists (S n). eapply ad_pat_sub_n__univ_ghost_l; eauto.
  - destruct (IHad_pat_sub Hwf) as [n Hn].
    exists (S n). eapply ad_pat_sub_n__univ_ghost_lg; eauto.
  - destruct (IHad_pat_sub Hwf) as [n Hn].
    exists (S n). eapply ad_pat_sub_n__flex_mono; eauto.
Qed.

(* ===================================================================== *)
(*  P5b — partial-precision-complete + precision-substitution.            *)
(*  See docs/DESIGN-completeness-subtyping.md §5.1 for the case-plan.     *)
(* ===================================================================== *)

(** A pskl with no synthesised quantifier: [inh] and [syn] paintings then
    coincide (they differ only at [pskl_all_syn]). *)
Fixpoint pskl_no_forall (P : pskl) : Prop :=
  match P with
  | pskl_all_syn _ => False
  | pskl_arrow P1 P2 => pskl_no_forall P1 /\ pskl_no_forall P2
  | pskl_tophole P0 => pskl_no_forall P0
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

(** Empty tags ⇒ the erasure is quantifier-free ([all_etag] always carries a
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

(** Narrow the ghost-binder context [Δ] to any [Δ'] that still contains every
    [Δ]-variable [P] actually uses. *)
Lemma a_wf_pskl_delta_narrow : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  forall Δ', (forall X, X `in` ftvar_in_pskl P -> X `in` Δ -> X `in` Δ') ->
  Θ ⨟ Δ' ⊢ₚₛᵃ P.
Proof.
  intros Θ Δ P H. induction H; intros Δ' Hnar; simpl in *.
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var.
    destruct H as [HΔ | Htv]; [ left; apply Hnar; [ clear; fsetdec | exact HΔ ] | right; exact Htv ].
  - apply a_wf_pskl__arrow;
      [ apply IHa_wf_pskl1 | apply IHa_wf_pskl2 ];
      intros X HX HXΔ; apply Hnar; auto; clear - HX; fsetdec.
  - apply a_wf_pskl__all with (L := L). intros X HX.
    apply H0; [ exact HX | ].
    intros Y HY HYΔ.
    destruct (Y == X) as [-> | Hne]; [ clear; fsetdec | ].
    assert (HYΔ0 : Y `in` Δ) by (clear - HYΔ Hne; fsetdec).
    assert (HYP : Y `in` ftvar_in_pskl P).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f X)) as Hup.
      simpl in Hup. clear - HY Hup Hne. fsetdec. }
    assert (Y `in` Δ') by (apply Hnar; auto). clear - H1; fsetdec.
  - apply a_wf_pskl__hole.
  - apply a_wf_pskl__tophole; [ exact H | ].
    apply IHa_wf_pskl. clear; intros X HX HXe; exact HXe.
Qed.

Lemma a_wf_pskl_delta_strip : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  AtomSetImpl.inter Δ (ftvar_in_pskl P) [=] empty ->
  Θ ⨟ empty ⊢ₚₛᵃ P.
Proof.
  intros Θ Δ P H Hdis.
  eapply a_wf_pskl_delta_narrow; [ exact H | ].
  intros X HX HXΔ. exfalso. clear - Hdis HX HXΔ. fsetdec.
Qed.

(** Clean structural inversions of [d_tags_skl] (name-agnostic). *)
Lemma d_tags_skl_unit_inv : forall Ψ,
  d_tags_skl Ψ uskl_unit -> Ψ [=] empty.
Proof. intros Ψ H. inversion H; subst; auto. Qed.

Lemma d_tags_skl_var_inv : forall Ψ X,
  d_tags_skl Ψ (uskl_var_f X) -> Ψ [=] empty.
Proof. intros Ψ X H. inversion H; subst; auto. Qed.

Lemma d_tags_skl_arrow_inv : forall Ψ ψ1 ψ2,
  d_tags_skl Ψ (uskl_arrow ψ1 ψ2) ->
  exists Ψ1 Ψ2, d_tags_skl Ψ1 ψ1 /\ d_tags_skl Ψ2 ψ2
             /\ AtomSetImpl.inter Ψ1 Ψ2 [=] empty /\ Ψ [=] Ψ1 `union` Ψ2.
Proof. intros Ψ ψ1 ψ2 H. inversion H; subst. eauto 10. Qed.

Lemma d_tags_skl_all_etag_inv : forall Ψ ε ψ,
  d_tags_skl Ψ (uskl_all_etag ε ψ) ->
  exists L Ψ0,
    (forall X, X `notin` L ->
       d_tags_skl Ψ0 (open_uskl_wrt_uskl ψ (uskl_var_f X)))
    /\ ε `notin` Ψ0 /\ Ψ [=] add ε Ψ0.
Proof. intros Ψ ε ψ H. inversion H; subst. eauto 8. Qed.

Lemma d_tags_skl_topholeg_inv : forall Ψ ψ,
  d_tags_skl Ψ (uskl_topholeg ψ) -> d_tags_skl Ψ ψ.
Proof. intros Ψ ψ H. inversion H; subst; auto. Qed.

(** The solved tag context of partial precision is contained in [ψ]'s tags —
    the invariant that makes the [tophole_fill] case of partial-precision-
    complete vacuous. *)
Lemma ad_partial_precise_tags_sub : forall Θ Δ Ψ P ψ,
  a_wf_aenv Θ ->
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  forall Ψt, d_tags_skl Ψt ψ -> Ψ [<=] Ψt.
Proof.
  intros Θ Δ Ψ P ψ Hwf H. induction H; intros Ψt Hdt.
  - apply d_tags_skl_unit_inv in Hdt. fsetdec.
  - apply d_tags_skl_var_inv in Hdt. fsetdec.
  - apply d_tags_skl_arrow_inv in Hdt as [Ψt1 [Ψt2 [Hd1 [Hd2 [_ Heqt]]]]].
    specialize (IHad_partial_precise1 Hwf _ Hd1).
    specialize (IHad_partial_precise2 Hwf _ Hd2).
    fsetdec.
  - apply d_tags_skl_all_etag_inv in Hdt as [L0 [Ψt0 [Hd0 [Hεt Heqt]]]].
    pick fresh X for (L `union` L0).
    specialize (H0 X ltac:(fsetdec) Hwf _ (Hd0 X ltac:(fsetdec))).
    fsetdec.
  - fsetdec.
  - eapply IHad_partial_precise; eauto.
  - (* tophole_fill: the recursive premise keeps Ψ but drops the ε tag;
       here the sub-derivation extends Θ with the rigid X *)
    apply d_tags_skl_all_etag_inv in Hdt as [L0 [Ψt0 [Hd0 [Hεt Heqt]]]].
    pick fresh X for (L `union` L0 `union` dom Θ).
    assert (Hwf' : a_wf_aenv ((X ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - Fr; fsetdec | exact Hwf ]).
    specialize (H0 X ltac:(fsetdec) Hwf' _ (Hd0 X ltac:(fsetdec))).
    fsetdec.
  - apply d_tags_skl_topholeg_inv in Hdt. eapply IHad_partial_precise; eauto.
  - eapply IHad_partial_precise; eauto.
  - (* flex_r: ψ = var α ⇒ Ψt = ∅, and the def body is a tag-free monotype *)
    apply d_tags_skl_var_inv in Hdt.
    assert (Hmono : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    assert (Ψ [<=] empty).
    { eapply IHad_partial_precise; [ exact Hwf | ].
      apply mono_ptyp_to_uskl_syn_tags; [ exact Hmono | reflexivity ]. }
    fsetdec.
Qed.

(** Recover the tag reading / re-tag under set-equality. *)
Lemma a_tags_sort_d_tags : forall NM Ψ ψ,
  a_tags_sort NM Ψ ψ -> d_tags_skl Ψ ψ.
Proof. intros NM Ψ ψ H. inversion H; auto. Qed.

(** [d_tags_skl] respects set-equality (local copy of the lemma in
    prop_decorate_key.v — kept here so completeness does not depend on the
    soundness decoration file). *)
Lemma d_tags_skl_recong : forall Ψ Ψ' ψ,
  d_tags_skl Ψ ψ -> Ψ [=] Ψ' -> d_tags_skl Ψ' ψ.
Proof.
  intros Ψ Ψ' ψ H; revert Ψ'; induction H; intros Ψ' Heq.
  - apply d_tags_skl__unit; fsetdec.
  - apply d_tags_skl__var; fsetdec.
  - eapply d_tags_skl__arrow;
      [ exact H | exact H0 | exact H1 | clear - H2 Heq; fsetdec ].
  - eapply d_tags_skl__all_etag;
      [ exact H | exact H1 | clear - H2 Heq; fsetdec ].
  - apply d_tags_skl__holeg; fsetdec.
  - apply d_tags_skl__topholeg; apply IHd_tags_skl; exact Heq.
Qed.

Lemma a_tags_sort_psi_cong : forall NM Ψ Ψ' ψ,
  a_tags_sort NM Ψ ψ -> Ψ [=] Ψ' -> a_tags_sort NM Ψ' ψ.
Proof.
  intros NM Ψ Ψ' ψ H Heq. inversion H; subst;
    [ apply a_tags_sort__sk | apply a_tags_sort__ty ]; auto;
    eapply d_tags_skl_recong; eauto.
Qed.

(** Structural inversions of [a_tags_sort] (both modes at once), carrying the
    tag decomposition needed to pin the sub-derivations' tag sets. *)
Lemma a_tags_sort_arrow_inv : forall NM Ψ ψ1 ψ2,
  a_tags_sort NM Ψ (uskl_arrow ψ1 ψ2) ->
  exists Ψ1 Ψ2, a_tags_sort NM Ψ1 ψ1 /\ a_tags_sort NM Ψ2 ψ2
             /\ AtomSetImpl.inter Ψ1 Ψ2 [=] empty /\ Ψ [=] Ψ1 `union` Ψ2.
Proof.
  intros NM Ψ ψ1 ψ2 H. inversion H; subst;
    match goal with Ht : is_tskl _ |- _ => inversion Ht; subst end;
    match goal with Hd : d_tags_skl _ (uskl_arrow _ _) |- _ =>
      apply d_tags_skl_arrow_inv in Hd as [Ψa [Ψb [Hd1 [Hd2 [Hdisj Hun]]]]] end.
  - exists Ψa, Ψb. repeat apply conj; try assumption; apply a_tags_sort__sk; auto.
  - match goal with Hg : uskl_ghost_free (uskl_arrow _ _) |- _ =>
      inversion Hg; subst end.
    exists Ψa, Ψb. repeat apply conj; try assumption; apply a_tags_sort__ty; auto.
Qed.

Lemma a_tags_sort_all_etag_inv : forall NM Ψ ε ψ,
  a_tags_sort NM Ψ (uskl_all_etag ε ψ) ->
  exists L Ψ0,
    (forall X, X `notin` L ->
       a_tags_sort NM Ψ0 (open_uskl_wrt_uskl ψ (uskl_var_f X)))
    /\ ε `notin` Ψ0 /\ Ψ [=] add ε Ψ0.
Proof.
  intros NM Ψ ε ψ H. inversion H; subst.
  - (* sk *)
    match goal with Hit : is_tskl (uskl_all_etag _ _) |- _ =>
      inversion Hit; subst end.
    match goal with Hd : d_tags_skl _ (uskl_all_etag _ _) |- _ =>
      apply d_tags_skl_all_etag_inv in Hd as [Ld [Ψ0 [Hd0 [Hεt Hun]]]] end.
    match goal with Hit0 : forall X, X `notin` ?Li -> is_tskl _ |- _ =>
      exists (Li `union` Ld), Ψ0; repeat apply conj; try assumption;
      intros X HX; apply a_tags_sort__sk; [ apply Hit0 | apply Hd0 ]; fsetdec end.
  - (* ty *)
    match goal with Hit : is_tskl (uskl_all_etag _ _) |- _ =>
      inversion Hit; subst end.
    match goal with Hd : d_tags_skl _ (uskl_all_etag _ _) |- _ =>
      apply d_tags_skl_all_etag_inv in Hd as [Ld [Ψ0 [Hd0 [Hεt Hun]]]] end.
    match goal with Hgf : uskl_ghost_free (uskl_all_etag _ _) |- _ =>
      inversion Hgf; subst end.
    match goal with
    | Hit0 : forall X, X `notin` ?Li -> is_tskl _,
      Hgf0 : forall X, X `notin` ?Lg -> uskl_ghost_free _ |- _ =>
      exists (Li `union` Lg `union` Ld), Ψ0; repeat apply conj; try assumption;
      intros X HX;
      apply a_tags_sort__ty; [ apply Hit0 | apply Hd0 | apply Hgf0 ]; fsetdec
    end.
Qed.

(** Clean [a_wf_pskl] inversions (name-agnostic). *)
Lemma a_wf_pskl_all_inv : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ (pskl_all_syn P) ->
  exists L, forall X, X `notin` L ->
    Θ ⨟ (add X Δ) ⊢ₚₛᵃ (open_pskl_wrt_pskl P (pskl_var_f X)).
Proof. intros Θ Δ P H. inversion H; subst. eauto. Qed.

Lemma a_wf_pskl_tophole_inv : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ (pskl_tophole P) ->
  guarded_pskl P /\ Θ ⨟ empty ⊢ₚₛᵃ P.
Proof. intros Θ Δ P H. inversion H; subst. auto. Qed.

(** [lemma:partial-precision-complete] (subtyping-proofs.tex:1639).  Under
    wf of [ψ] and the tag-sort premise, partial precision at the FULL tag set
    [Ψ] upgrades to plain (coloured) precision against [⌊ψ⌋].  See §5.1. *)
Lemma ad_partial_precise_complete : forall NM Θ Δ Ψ P ψ,
  a_wf_aenv Θ ->
  a_tags_sort NM Ψ ψ ->
  Θ ⨟ Δ ⊢ₚₛᵃ ⌊ ψ ⌋ˢ ->
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  Θ ⨟ Δ ⊢ₚᵣᵃ P ⊑ ⌊ ψ ⌋ˢ.
Proof.
  intros NM Θ Δ Ψ P ψ Hwf Htags Hwfp H.
  revert Hwf Htags Hwfp. induction H; intros Hwf Htags Hwfp;
    unfold ad_precise in *; simpl in *.
  - (* unit *) apply ad_refine_syn__unit.
  - (* var *) apply ad_refine_syn__var. assumption.
  - (* arrow *)
    apply a_tags_sort_arrow_inv in Htags as [Ψa [Ψb [Hta [Htb [Hdisj Hun]]]]].
    inversion Hwfp; subst.
    assert (Hs1 : Ψ1 [<=] Ψa) by
      (eapply (ad_partial_precise_tags_sub Hwf H); exact (a_tags_sort_d_tags Hta)).
    assert (Hs2 : Ψ2 [<=] Ψb) by
      (eapply (ad_partial_precise_tags_sub Hwf H0); exact (a_tags_sort_d_tags Htb)).
    apply ad_refine_syn__arrow.
    + apply IHad_partial_precise1;
        [ exact Hwf
        | eapply a_tags_sort_psi_cong; [ exact Hta | clear - H1 Hun Hdisj Hs1 Hs2; fsetdec ]
        | assumption ].
    + apply IHad_partial_precise2;
        [ exact Hwf
        | eapply a_tags_sort_psi_cong; [ exact Htb | clear - H1 Hun Hdisj Hs1 Hs2; fsetdec ]
        | assumption ].
  - (* forall: ψ = all_etag ε ψ0, P = all_syn P0 *)
    apply a_tags_sort_all_etag_inv in Htags as [Lt [Ψt [Hta [Hεt Hun]]]].
    apply a_wf_pskl_all_inv in Hwfp as [Lw Hwbody].
    apply ad_refine_syn__all with (L := L `union` Lt `union` Lw `union` dom Θ
       `union` ftvar_in_pskl P `union` ftvar_in_uskl ψ).
    intros X HX.
    assert (Hs0 : Ψ0 [<=] Ψt) by
      (eapply (ad_partial_precise_tags_sub Hwf (H X ltac:(fsetdec)));
        exact (a_tags_sort_d_tags (Hta X ltac:(fsetdec)))).
    assert (Heq0 : Ψ0 [=] Ψt) by (clear - H1 Hun Hεt Hs0; fsetdec).
    rewrite <- pskl_to_bskl_inh_open.
    rewrite <- pskl_to_bskl_inh_open.
    rewrite <- (uskl_to_pskl_open ψ).
    apply H0; [ fsetdec | exact Hwf | | ].
    + eapply a_tags_sort_psi_cong; [ apply Hta; fsetdec | clear - Heq0; fsetdec ].
    + rewrite uskl_to_pskl_open. apply Hwbody. fsetdec.
  - (* hole: ψ ∀-free (empty tags) ⇒ inh = syn, wf-strip supplies the fill *)
    assert (Hnf : pskl_no_forall (uskl_to_pskl ψ)) by
      (eapply d_tags_empty_no_forall;
        [ exact (a_tags_sort_d_tags Htags) | assumption ]).
    rewrite (pskl_no_forall_inh_eq_syn _ Hnf).
    apply ad_refine_syn__hole.
    eapply a_wf_pskl_delta_strip; [ exact Hwfp | ].
    rewrite ftvar_in_pskl_uskl_to_pskl. assumption.
  - (* tophole_remove *)
    apply ad_refine_syn__tophole_remove.
    apply IHad_partial_precise; [ exact Hwf | exact Htags | exact Hwfp ].
  - (* tophole_fill: VACUOUS via tags_sub — ε is solved but the premise drops it *)
    exfalso.
    apply a_tags_sort_all_etag_inv in Htags as [Lt [Ψt [Hta [Hεt Hun]]]].
    pick fresh X for (L `union` Lt `union` dom Θ).
    assert (Hwf' : a_wf_aenv ((X ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - Fr; fsetdec | exact Hwf ]).
    assert (Hsub : Ψ [<=] Ψt) by
      (eapply (ad_partial_precise_tags_sub Hwf' (H X ltac:(fsetdec)));
        exact (a_tags_sort_d_tags (Hta X ltac:(fsetdec)))).
    clear - Hun Hεt Hsub. fsetdec.
  - (* tophole_keep: ψ = topholeg ψ0 (SK-only; TY gf excludes it) *)
    apply a_wf_pskl_tophole_inv in Hwfp as [Hg Hw0].
    apply ad_refine_syn__tophole_keep.
    + apply guarded_pskl_to_bskl_inh. exact Hg.
    + apply IHad_partial_precise; [ exact Hwf | | ].
      * inversion Htags; subst;
          match goal with Hit : is_tskl (uskl_topholeg _) |- _ =>
            inversion Hit; subst end.
        -- match goal with Hd : d_tags_skl _ (uskl_topholeg _) |- _ =>
             apply d_tags_skl_topholeg_inv in Hd end.
           apply a_tags_sort__sk; auto.
        -- match goal with Hg0 : uskl_ghost_free (uskl_topholeg _) |- _ =>
             inversion Hg0 end.
      * eapply a_wf_pskl_delta_mono; [ exact Hw0 | clear; fsetdec ].
  - (* flex_l: subject α unfolds to its mono def; ψ unchanged *)
    assert (Hmono : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf | exact H ]).
    eapply ad_refine_syn__flex_l; [ exact H | ].
    rewrite <- (ptyp_to_bskl_inh_syn_eq Hmono).
    apply IHad_partial_precise; [ exact Hwf | exact Htags | exact Hwfp ].
  - (* flex_r: target α unfolds to its mono def (tag-free, wf since flex-free) *)
    assert (Hmono : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf | exact H ]).
    assert (Hwfτ : a_wf_ptyp Θ τ)
      by (eapply a_wf_aenv_binds_def_wf; [ exact Hwf | exact H ]).
    assert (HΨ : Ψ [=] empty)
      by exact (d_tags_skl_var_inv (a_tags_sort_d_tags Htags)).
    eapply ad_refine_syn__flex_r; [ exact H | ].
    rewrite <- (ptyp_to_bskl_inh_syn_eq Hmono).
    replace (ptyp_to_pskl τ) with (uskl_to_pskl (ptyp_to_uskl_syn τ))
      by (apply uskl_to_pskl_ptyp_to_uskl_syn).
    apply IHad_partial_precise.
    + exact Hwf.
    + (* build at concrete [empty] FIRST (no evar), then re-tag to Ψ [=] empty
         — psi_cong with an evar source would make [fsetdec] hang. *)
      assert (Htagpaint : a_tags_sort NM empty (ptyp_to_uskl_syn τ)).
      { destruct NM.
        - apply a_tags_sort__ty.
          + exact (mono_ptyp_to_uskl_syn_is_tskl Hmono).
          + apply (mono_ptyp_to_uskl_syn_tags Hmono). reflexivity.
          + exact (mono_ptyp_to_uskl_syn_ghost_free Hmono).
        - apply a_tags_sort__sk.
          + exact (mono_ptyp_to_uskl_syn_is_tskl Hmono).
          + apply (mono_ptyp_to_uskl_syn_tags Hmono). reflexivity. }
      eapply a_tags_sort_psi_cong; [ exact Htagpaint | clear - HΨ; fsetdec ].
    + rewrite uskl_to_pskl_ptyp_to_uskl_syn.
      apply a_scope_pskl_of_ptyp_vis.
      * eapply a_wf_ptyp_lc; exact Hwfτ.
      * intros X HX. right.
        eapply a_wf_ptyp_ftv_tvarish; [ exact Hwfτ | exact HX ].
Qed.

(* ===================================================================== *)
(*  P5b-ii — precision-substitution, foundational crux.                    *)
(*  The paper's no-type-mismatch step is, on the consistency premises,       *)
(*  subject-precision preserving consistency.  Built in two steps           *)
(*  consistency.  Built in two steps (DESIGN §5.2): (1a) strip the          *)
(*  decorated subject to plain (tags drop to ∅); (1b) transport the erased  *)
(*  subject along the refinement — the SUBJECT-side mirror of the Qed       *)
(*  target-side [ad_pat_consis_refine_inh_gen] (prop_sub_sound.v).          *)
(* ===================================================================== *)

(** [strip ψ := pskl_to_uskl ⌊ψ⌋ˢ] commutes with opening. *)
Lemma strip_uskl_open : forall ψ X,
  pskl_to_uskl (uskl_to_pskl (open_uskl_wrt_uskl ψ (uskl_var_f X)))
  = open_uskl_wrt_uskl (pskl_to_uskl (uskl_to_pskl ψ)) (uskl_var_f X).
Proof.
  intros ψ X. rewrite uskl_to_pskl_open, pskl_to_uskl_open. reflexivity.
Qed.

(** (1a) Stripping the decorated subject to its plain skeleton preserves
    consistency; the subject is then tag-free so the tag context is [∅]. *)
Lemma ad_pat_consis_strip_tags : forall Ψt Θ ψa Q,
  Ψt ⨟ Θ ⊢ₛᵃ ψa ∼ Q ->
  empty ⨟ Θ ⊢ₛᵃ (pskl_to_uskl (uskl_to_pskl ψa)) ∼ Q.
Proof.
  intros Ψt Θ ψa Q H. induction H; simpl.
  - apply ad_pat_consis__unit. reflexivity.
  - apply ad_pat_consis__var; [ reflexivity | assumption ].
  - eapply ad_pat_consis__arrow;
      [ exact IHad_pat_consis1 | exact IHad_pat_consis2 | fsetdec ].
  - eapply ad_pat_consis__forall_inh_untagged with (L := L).
    intros X HX. rewrite <- strip_uskl_open. exact (H0 X HX).
  - eapply ad_pat_consis__forall_inh_untagged with (L := L).
    intros X HX. rewrite <- strip_uskl_open. exact (H0 X HX).
  - eapply ad_pat_consis__forall_syn with (L := L).
    intros X HX. rewrite <- strip_uskl_open. exact (H0 X HX).
  - eapply ad_pat_consis__forall_syn with (L := L).
    intros X HX. rewrite <- strip_uskl_open. exact (H0 X HX).
  - change bskl_hole with (pskl_to_bskl_inh pskl_hole).
    apply ad_pat_consis__hole; [ reflexivity | apply a_wf_pskl__hole ].
  - (* topholeg: stripping the dotted ghost yields a plain [tophole] *)
    apply ad_pat_consis__tophole. exact IHad_pat_consis.
  - apply ad_pat_consis__hole; [ reflexivity | exact H0 ].
  - apply ad_pat_consis__tophole. exact IHad_pat_consis.
  - eapply ad_pat_consis__tophole_inh with (L := L).
    intros X HX. specialize (H0 X HX). simpl in H0. exact H0.
  - apply ad_pat_consis__tophole_drop. exact IHad_pat_consis.
  - eapply ad_pat_consis__flex_l; [ exact H | ].
    rewrite uskl_to_pskl_ptyp_to_uskl_syn, pskl_to_uskl_ptyp in IHad_pat_consis.
    exact IHad_pat_consis.
  - eapply ad_pat_consis__flex_r; [ exact H | exact IHad_pat_consis ].
Qed.

(** (1b) helpers: SUBJECT-side transport (mirror of [consis_transport_arrow]
    / [consis_transport_all], which transport the target).  Both subjects are
    tag-free ([pskl_to_uskl _]), so the tag context is inert. *)
(** WF-carrying subject transporters.  The transport hypotheses thread a
    [Θ' ⊢ bskl_to_pskl Q'] premise: the reconstruction at a subject HOLE
    ([B = uskl_hole]) needs the erased target well-formed (via
    [consis_concrete_target_inh] + [__hole]).  The wf-less transporters
    ([consis_forall/tophole_subject_transport], prop_consis_complete.v) cannot
    carry it, so these are genuine wf-variants, not duplicates. *)
Lemma consis_subj_transport_arrow_wf : forall Ψ Θ' A1 A2 B1 B2 Q,
  Ψ ⨟ Θ' ⊢ₛᵃ (uskl_arrow A1 A2) ∼ Q ->
  a_wf_aenv Θ' ->
  Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q) ->
  (forall Ψ1 Q1, Ψ1 ⨟ Θ' ⊢ₛᵃ A1 ∼ Q1 -> Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q1) ->
     Ψ1 ⨟ Θ' ⊢ₛᵃ B1 ∼ Q1) ->
  (forall Ψ2 Q2, Ψ2 ⨟ Θ' ⊢ₛᵃ A2 ∼ Q2 -> Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q2) ->
     Ψ2 ⨟ Θ' ⊢ₛᵃ B2 ∼ Q2) ->
  Ψ ⨟ Θ' ⊢ₛᵃ (uskl_arrow B1 B2) ∼ Q.
Proof.
  intros Ψ Θ' A1 A2 B1 B2 Q Hc Hwfa Hwfq Ht1 Ht2.
  remember (uskl_arrow A1 A2) as Ssub eqn:HS.
  revert Hwfq; induction Hc; try discriminate HS; intros Hwfq.
  - (* arrow: Q = bskl_arrow Q1 Q2 *)
    inversion HS; subst.
    simpl in Hwfq.
    inversion Hwfq as [ | | Θz Δz Pw1 Pw2 Hwfq1 Hwfq2 | | | ]; subst.
    apply ad_pat_consis__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2).
    + apply Ht1; assumption.
    + apply Ht2; assumption.
    + assumption.
  - (* flex_r: Q = bskl_var α ≔ τ; recurse at target [syn τ] *)
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    apply IHHc; [ exact HS | exact Hwfa | exact Ht1 | exact Ht2 | ].
    replace (bskl_to_pskl (ptyp_to_bskl_syn τ)) with (ptyp_to_pskl τ)
      by (unfold ptyp_to_bskl_syn; rewrite bskl_to_pskl_pskl_to_bskl_syn;
          reflexivity).
    apply a_wf_pskl_mono_ptyp;
      [ eapply a_wf_aenv_binds_def_mono; eauto
      | eapply a_wf_aenv_binds_def_wf; eauto ].
Qed.

(** WF bridge for a ∀-target: the erased opened body is wf under the ∀-var as
    a TVAR in [Θ] (which the consistency transport needs), from the opened
    body wf with the ∀-var in [Δ] (as [a_wf_pskl__all] gives it) via
    [a_wf_pskl_reassoc] + [a_wf_pskl_delta_narrow]. *)
Lemma wf_open_of_all : forall Θ Δ Q0 X,
  Θ ⨟ (add X Δ) ⊢ₚₛᵃ open_pskl_wrt_pskl (bskl_to_pskl Q0) (pskl_var_f X) ->
  ((X ~ abind_tvar) ++ Θ) ⨟ Δ
    ⊢ₚₛᵃ bskl_to_pskl (open_bskl_wrt_bskl Q0 (bskl_var_f X)).
Proof.
  intros Θ Δ Q0 X Hb.
  rewrite bskl_to_pskl_open.
  eapply a_wf_pskl_delta_narrow with (Δ := remove X (add X Δ)).
  - apply (a_wf_pskl_reassoc Hb X).
  - intros W HW HWin. clear - HWin. fsetdec.
Qed.

Lemma consis_forall_subject_transport_wf : forall Ψ Θ' A0 B0 Q L0,
  Ψ ⨟ Θ' ⊢ₛᵃ (uskl_all_syn A0) ∼ Q ->
  a_wf_aenv Θ' ->
  Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q) ->
  (forall X, X `notin` L0 -> forall Ψ' Q',
     Ψ' ⨟ ((X ~ abind_tvar) ++ Θ') ⊢ₛᵃ
       (open_uskl_wrt_uskl A0 (uskl_var_f X)) ∼ Q' ->
     ((X ~ abind_tvar) ++ Θ') ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q') ->
     Ψ' ⨟ ((X ~ abind_tvar) ++ Θ') ⊢ₛᵃ
       (open_uskl_wrt_uskl B0 (uskl_var_f X)) ∼ Q') ->
  Ψ ⨟ Θ' ⊢ₛᵃ (uskl_all_syn B0) ∼ Q.
Proof.
  intros Ψ Θ' A0 B0 Q L0 Hc Hwfa Hwfq Htr.
  remember (uskl_all_syn A0) as Ssub eqn:HS.
  revert Hwfq; induction Hc; try discriminate HS; intros Hwfq.
  - (* forall_inh_untagged: Q = bskl_all_inh Q0 *)
    inversion HS; subst.
    simpl in Hwfq. destruct (a_wf_pskl_all_inv Hwfq) as [Lw Hbody].
    apply ad_pat_consis__forall_inh_untagged with (L := L `union` L0 `union` Lw).
    intros X HX.
    apply Htr; [ clear - HX; fsetdec | apply H; clear - HX; fsetdec | ].
    apply wf_open_of_all. apply Hbody. clear - HX; fsetdec.
  - (* forall_syn: Q = bskl_all_syn Q0 *)
    inversion HS; subst.
    simpl in Hwfq. destruct (a_wf_pskl_all_inv Hwfq) as [Lw Hbody].
    apply ad_pat_consis__forall_syn with (L := L `union` L0 `union` Lw).
    intros X HX.
    apply Htr; [ clear - HX; fsetdec | apply H; clear - HX; fsetdec | ].
    apply wf_open_of_all. apply Hbody. clear - HX; fsetdec.
  - (* flex_r: Q = bskl_var α ≔ τ *)
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    apply IHHc; [ exact HS | exact Hwfa | exact Htr | ].
    replace (bskl_to_pskl (ptyp_to_bskl_syn τ)) with (ptyp_to_pskl τ)
      by (unfold ptyp_to_bskl_syn; rewrite bskl_to_pskl_pskl_to_bskl_syn;
          reflexivity).
    apply a_wf_pskl_mono_ptyp;
      [ eapply a_wf_aenv_binds_def_mono; eauto
      | eapply a_wf_aenv_binds_def_wf; eauto ].
Qed.

Lemma consis_tophole_subject_transport_wf : forall Ψ Θ' S Q,
  Ψ ⨟ Θ' ⊢ₛᵃ S ∼ Q ->
  a_wf_aenv Θ' ->
  Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q) ->
  forall S0 T0, S = uskl_tophole S0 ->
  (forall Θ'' Ψ' Q',
     a_wf_aenv Θ'' ->
     (forall x b, binds x b Θ' -> binds x b Θ'') ->
     Ψ' ⨟ Θ'' ⊢ₛᵃ S0 ∼ Q' ->
     Θ'' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q') ->
     Ψ' ⨟ Θ'' ⊢ₛᵃ T0 ∼ Q') ->
  Ψ ⨟ Θ' ⊢ₛᵃ (uskl_tophole T0) ∼ Q.
Proof.
  intros Ψ Θ' S Q Hc; induction Hc;
    intros HwfΘ Hwfq S0 T0 HeqS Htr; try discriminate HeqS.
  - (* tophole: Q = bskl_tophole Q0 *)
    inversion HeqS; subst.
    simpl in Hwfq. destruct (a_wf_pskl_tophole_inv Hwfq) as [Hg Hwfb].
    apply ad_pat_consis__tophole.
    apply (Htr Θ); [ exact HwfΘ | intros x b Hb; exact Hb | exact Hc | exact Hwfb ].
  - (* tophole_inh: Q = bskl_all_inh Q0, extended context *)
    inversion HeqS; subst.
    simpl in Hwfq. destruct (a_wf_pskl_all_inv Hwfq) as [Lw Hbody].
    apply ad_pat_consis__tophole_inh with (L := L `union` dom Θ `union` Lw).
    intros X HX.
    assert (HwfX : a_wf_aenv ((X ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - HX; fsetdec | exact HwfΘ ]).
    eapply (H0 X ltac:(clear - HX; fsetdec) HwfX).
    + apply wf_open_of_all. apply Hbody. clear - HX; fsetdec.
    + reflexivity.
    + intros Θ'' Ψ' Q' Hwf' Hincl' Hc' Hwfq'.
      apply (Htr Θ'' Ψ' Q' Hwf'); [ | exact Hc' | exact Hwfq' ].
      intros x b Hb. apply Hincl'. apply binds_cons_3. exact Hb.
  - (* tophole_drop: Q arbitrary *)
    inversion HeqS; subst.
    apply ad_pat_consis__tophole_drop.
    apply (Htr Θ); [ exact HwfΘ | intros x b Hb; exact Hb | exact Hc | exact Hwfq ].
  - (* flex_r: Q = bskl_var α ≔ τ *)
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    eapply IHHc; [ exact HwfΘ | | exact HeqS | exact Htr ].
    replace (bskl_to_pskl (ptyp_to_bskl_syn τ)) with (ptyp_to_pskl τ)
      by (unfold ptyp_to_bskl_syn; rewrite bskl_to_pskl_pskl_to_bskl_syn;
          reflexivity).
    apply a_wf_pskl_mono_ptyp;
      [ eapply a_wf_aenv_binds_def_mono; eauto
      | eapply a_wf_aenv_binds_def_wf; eauto ].
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

(** (1b) hole-case leaf (EQUATION ONLY): a CONCRETE, ∀-free subject
    [pskl_to_uskl P] consistent with [Q] forces [Q] to be an inh-painting of
    its own erasure — [inh (bskl_to_pskl Q) = Q] — with empty tags.  That is
    ALL the main lemma's hole case needs: combined with a THREADED
    [Θ ⊢ bskl_to_pskl Q] (well-formedness is an INPUT, not a conclusion — cf.
    [ad_pat_consis_refine_inh_gen]'s [Bsrc] premise), [uskl_hole ∼ Q] follows
    by [__hole] with [B := bskl_to_pskl Q].  Proving only the EQUATION avoids
    reconstructing the wf of a ∀-witness under the [Θ↔Δ] tension (which is not
    a general fact — a [⊤◇] body cannot reference a Δ-var). *)
Lemma consis_concrete_target_inh : forall Ψ Θ S Q,
  Ψ ⨟ Θ ⊢ₛᵃ S ∼ Q ->
  a_wf_aenv Θ ->
  forall P, S = pskl_to_uskl P ->
  pskl_no_forall P ->
  Ψ [=] empty /\ pskl_to_bskl_inh (bskl_to_pskl Q) = Q.
Proof.
  intros Ψ Θ S Q Hc; induction Hc; intros Hwfa P0 HS Hnf.
  - (* unit *)  split; [ exact H | reflexivity ].
  - (* var *)   split; [ exact H | reflexivity ].
  - (* arrow *)
    destruct P0 as [ | n | Xv | Pl Pr | Pq | | Pt ];
      simpl in HS; try discriminate HS. inversion HS; subst.
    simpl in Hnf; destruct Hnf as [Hnf1 Hnf2].
    destruct (IHHc1 Hwfa _ eq_refl Hnf1) as [HΨ1 Heq1].
    destruct (IHHc2 Hwfa _ eq_refl Hnf2) as [HΨ2 Heq2].
    split; [ fsetdec | simpl; rewrite Heq1, Heq2; reflexivity ].
  - (* forall_inh_tagged: subject all_etag — impossible *)
    destruct P0 as [ | n | Xv | Pl Pr | Pq | | Pt ]; simpl in HS; discriminate HS.
  - (* forall_inh_untagged: subject all_syn ⇒ ¬nf *)
    destruct P0 as [ | n | Xv | Pl Pr | Pq | | Pt ];
      simpl in HS; try discriminate HS. simpl in Hnf; contradiction.
  - (* forall_syn_tagged *)
    destruct P0 as [ | n | Xv | Pl Pr | Pq | | Pt ]; simpl in HS; discriminate HS.
  - (* forall_syn ⇒ ¬nf *)
    destruct P0 as [ | n | Xv | Pl Pr | Pq | | Pt ];
      simpl in HS; try discriminate HS. simpl in Hnf; contradiction.
  - (* ghostg *)
    destruct P0 as [ | n | Xv | Pl Pr | Pq | | Pt ]; simpl in HS; discriminate HS.
  - (* topholeg *)
    destruct P0 as [ | n | Xv | Pl Pr | Pq | | Pt ]; simpl in HS; discriminate HS.
  - (* hole *)
    split; [ exact H
           | simpl; rewrite bskl_to_pskl_pskl_to_bskl_inh; reflexivity ].
  - (* tophole: bskl_tophole Q0 *)
    destruct P0 as [ | n | Xv | Pl Pr | Pq | | Pt ];
      simpl in HS; try discriminate HS. inversion HS; subst.
    simpl in Hnf.
    destruct (IHHc Hwfa _ eq_refl Hnf) as [HΨ0 Heq0].
    split; [ exact HΨ0 | simpl; rewrite Heq0; reflexivity ].
  - (* tophole_inh: bskl_all_inh Q0 — close the opened equation via open-inj *)
    destruct P0 as [ | n | Xv | Pl Pr | Pq | | Pt ];
      simpl in HS; try discriminate HS. inversion HS; subst.
    simpl in Hnf.
    pick fresh X for (L `union` dom Θ `union` ftvar_in_bskl Q).
    assert (HwfX : a_wf_aenv ((X ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ fsetdec | exact Hwfa ]).
    destruct (H0 X ltac:(fsetdec) HwfX (pskl_tophole Pt) eq_refl Hnf)
      as [HΨX HeqX].
    split; [ exact HΨX | ].
    simpl. f_equal.
    eapply open_bskl_wrt_bskl_inj with (Xbs1 := X).
    + rewrite ftvar_in_bskl_inh, ftvar_in_pskl_bskl_to_pskl. fsetdec.
    + fsetdec.
    + rewrite <- pskl_to_bskl_inh_open, <- bskl_to_pskl_open. exact HeqX.
  - (* tophole_drop: Q arbitrary *)
    destruct P0 as [ | n | Xv | Pl Pr | Pq | | Pt ];
      simpl in HS; try discriminate HS. inversion HS; subst.
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
    destruct (IHHc Hwfa P0 HS Hnf) as [HΨ _].
    split; [ exact HΨ | reflexivity ].
Qed.


(** Monotonicity of [a_binds_tvar] under context extension. *)
Lemma a_binds_tvar_mono : forall X Θ Θ',
  a_binds_tvar X Θ ->
  (forall x b, binds x b Θ -> binds x b Θ') ->
  a_binds_tvar X Θ'.
Proof.
  intros X Θ Θ' H Hmon. unfold a_binds_tvar in *.
  destruct H as [Hb | [Hb | [τ Hb]]];
    [ left | right; left | right; right; exists τ ]; apply Hmon; exact Hb.
Qed.

(** (1b) — SUBJECT-REFINEMENT preserves consistency.  If [Ptgt] refines to
    [Psrc] ([Psrc] ghostier), then any [Q] consistent with the FILLED subject
    [Ptgt] is consistent with the GHOSTIER subject [Psrc].  Well-formedness of
    the (erased) target is THREADED as an input (the hole reconstruction needs
    it; see [consis_concrete_target_inh]).  Subject-side mirror of the target
    template [ad_pat_consis_refine_inh_gen] (prop_sub_sound.v). *)
Lemma ad_pat_consis_subject_refine : forall Θ Δ Src Tgt,
  ad_refine_syn Θ Δ Src Tgt ->
  forall Psrc Ptgt, Src = pskl_to_bskl_inh Psrc -> Tgt = pskl_to_bskl_inh Ptgt ->
  forall Θ',
  (forall x b, binds x b Θ -> binds x b Θ') ->
  (forall X, X `in` Δ -> a_binds_tvar X Θ') ->
  a_wf_aenv Θ' ->
  forall Ψ Q,
    Ψ ⨟ Θ' ⊢ₛᵃ (pskl_to_uskl Ptgt) ∼ Q ->
    Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q) ->
    Ψ ⨟ Θ' ⊢ₛᵃ (pskl_to_uskl Psrc) ∼ Q.
Proof.
  intros Θ Δ Src Tgt Hr.
  induction Hr; intros Psrc Ptgt HSrc HTgt Θ' Hmon Hrig Hwf' Ψ Qc Hc Hwfq.
  - (* unit *)
    destruct Psrc; simpl in HSrc; try discriminate HSrc.
    destruct Ptgt; simpl in HTgt; try discriminate HTgt. exact Hc.
  - (* var *)
    destruct Psrc; simpl in HSrc; try discriminate HSrc.
    destruct Ptgt; simpl in HTgt; try discriminate HTgt.
    inversion HSrc; inversion HTgt; subst. exact Hc.
  - (* arrow *)
    destruct Psrc as [ | | | Ps1 Ps2 | | | ]; simpl in HSrc; try discriminate HSrc.
    destruct Ptgt as [ | | | Pt1 Pt2 | | | ]; simpl in HTgt; try discriminate HTgt.
    inversion HSrc; inversion HTgt; subst.
    simpl in Hwfq.
    eapply consis_subj_transport_arrow_wf;
      [ exact Hc | exact Hwf' | exact Hwfq | | ].
    + intros Ψ1 Q1 Hc1 Hwfq1.
      eapply IHHr1;
        [ reflexivity | reflexivity | exact Hmon | exact Hrig | exact Hwf'
        | exact Hc1 | exact Hwfq1 ].
    + intros Ψ2 Q2 Hc2 Hwfq2.
      eapply IHHr2;
        [ reflexivity | reflexivity | exact Hmon | exact Hrig | exact Hwf'
        | exact Hc2 | exact Hwfq2 ].
  - (* all: Src = all_inh S0, Tgt = all_inh T0 (Δ grows under the binder) *)
    destruct Psrc as [ | | | | Ps0 | | ]; simpl in HSrc; try discriminate HSrc.
    destruct Ptgt as [ | | | | Pt0 | | ]; simpl in HTgt; try discriminate HTgt.
    inversion HSrc; inversion HTgt; subst.
    simpl. simpl in Hc.
    eapply consis_forall_subject_transport_wf
      with (A0 := pskl_to_uskl Pt0) (B0 := pskl_to_uskl Ps0)
           (L0 := L `union` dom Θ' `union` Δ);
      [ exact Hc | exact Hwf' | exact Hwfq | ].
    intros X HX Ψ' Q' Hc' Hwfq'.
    rewrite <- pskl_to_uskl_open_var.
    rewrite <- pskl_to_uskl_open_var in Hc'.
    eapply (H0 X ltac:(clear - HX; fsetdec)
              (open_pskl_wrt_pskl Ps0 (pskl_var_f X))
              (open_pskl_wrt_pskl Pt0 (pskl_var_f X)));
      [ symmetry; apply pskl_to_bskl_inh_open
      | symmetry; apply pskl_to_bskl_inh_open
      | intros x b Hb; unfold binds; simpl; right; apply Hmon; exact Hb
      | intros Y HYΔ; destruct (Y == X) as [ -> | Hne ];
          [ left; unfold binds; simpl; left; reflexivity
          | apply a_binds_tvar_weaken_cons; apply Hrig;
            clear - HYΔ Hne; fsetdec ]
      | apply a_wf_aenv__tvar; [ clear - HX; fsetdec | exact Hwf' ]
      | exact Hc'
      | exact Hwfq' ].
  - (* hole: Src = bskl_hole, Tgt = syn P (∀-free) *)
    destruct Psrc; simpl in HSrc; try discriminate HSrc.
    assert (Hnf : pskl_no_forall Ptgt)
      by (eapply inh_eq_syn_no_forall; symmetry; exact HTgt).
    destruct (consis_concrete_target_inh Hc Hwf' Ptgt eq_refl Hnf) as [HΨ Heqinh].
    simpl. rewrite <- Heqinh.
    apply ad_pat_consis__hole; [ exact HΨ | exact Hwfq ].
  - (* tophole_remove: Src = ⊤◇ S0, Tgt = P (same); drop the ⊤◇ *)
    destruct Psrc as [ | | | | | | Ps0 ]; simpl in HSrc; try discriminate HSrc.
    inversion HSrc; subst.
    simpl. apply ad_pat_consis__tophole_drop.
    eapply IHHr;
      [ reflexivity | reflexivity | exact Hmon | exact Hrig | exact Hwf'
      | exact Hc | exact Hwfq ].
  - (* tophole_fill: Tgt = all_syn P — impossible for an inh painting *)
    destruct Ptgt; simpl in HTgt; try discriminate HTgt.
  - (* tophole_keep: Src = ⊤◇ S0, Tgt = ⊤◇ T0 *)
    destruct Psrc as [ | | | | | | Ps0 ]; simpl in HSrc; try discriminate HSrc.
    destruct Ptgt as [ | | | | | | Pt0 ]; simpl in HTgt; try discriminate HTgt.
    inversion HSrc; inversion HTgt; subst.
    simpl. simpl in Hc.
    eapply consis_tophole_subject_transport_wf
      with (S0 := pskl_to_uskl Pt0) (T0 := pskl_to_uskl Ps0);
      [ exact Hc | exact Hwf' | exact Hwfq | reflexivity | ].
    intros Θ'' Ψ' Q' Hwf'' Hincl'' Hc'' Hwfq''.
    eapply IHHr with (Ptgt := Pt0);
      [ reflexivity | reflexivity
      | intros x b Hb; apply Hincl''; apply Hmon; exact Hb
      | intros Y HYΔ; eapply a_binds_tvar_mono;
          [ apply Hrig; exact HYΔ | exact Hincl'' ]
      | exact Hwf'' | exact Hc'' | exact Hwfq'' ].
  - (* flex_l: Src = bskl_var α (α ≔ τ), premise syn τ ⊳ Tgt *)
    destruct Psrc as [ | | X | | | | ]; simpl in HSrc; try discriminate HSrc.
    inversion HSrc; subst.
    assert (Hmτ : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf' | apply Hmon; exact H ]).
    simpl. eapply ad_pat_consis__flex_l; [ apply Hmon; exact H | ].
    replace (ptyp_to_uskl_syn τ) with (pskl_to_uskl (ptyp_to_pskl τ))
      by (apply pskl_to_uskl_ptyp).
    eapply IHHr with (Ptgt := Ptgt);
      [ symmetry; apply (mono_inh_eq_syn Hmτ) | reflexivity
      | exact Hmon | exact Hrig | exact Hwf' | exact Hc | exact Hwfq ].
  - (* flex_r: Tgt = bskl_var α (α ≔ τ), premise Src ⊳ syn τ *)
    destruct Ptgt as [ | | X | | | | ]; simpl in HTgt; try discriminate HTgt.
    inversion HTgt; subst.
    assert (Hmτ : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf' | apply Hmon; exact H ]).
    simpl in Hc.
    assert (Hc' : Ψ ⨟ Θ' ⊢ₛᵃ (ptyp_to_uskl_syn τ) ∼ Qc)
      by (eapply consis_unfold_def_subject;
            [ exact Hc | exact Hwf' | reflexivity | apply Hmon; exact H ]).
    replace (ptyp_to_uskl_syn τ) with (pskl_to_uskl (ptyp_to_pskl τ)) in Hc'
      by (apply pskl_to_uskl_ptyp).
    eapply IHHr with (Ptgt := ptyp_to_pskl τ);
      [ reflexivity | symmetry; apply (mono_inh_eq_syn Hmτ)
      | exact Hmon | exact Hrig | exact Hwf' | exact Hc' | exact Hwfq ].
Qed.

(** Crux (1): a plain [ψa]-consistency, composed with a precision
    [Pa ⊑ ⌊ψa⌋], yields a [Pa]-consistency.  This is [(1a) ; (1b)]:
    [ad_pat_consis_strip_tags] erases the decorated subject to
    [⌊ψa⌋] (tags → ∅), then [ad_pat_consis_subject_refine] transports it
    down the precision to [Pa].  The (erased) target's wf is THREADED. *)
Lemma ad_pat_consis_subject_precise : forall Ψt Θ Δ ψa Pa Q,
  Ψt ⨟ Θ ⊢ₛᵃ ψa ∼ Q ->
  Θ ⨟ Δ ⊢ₚᵣᵃ Pa ⊑ (uskl_to_pskl ψa) ->
  a_wf_aenv Θ ->
  (forall X, X `in` Δ -> a_binds_tvar X Θ) ->
  Θ ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q) ->
  empty ⨟ Θ ⊢ₛᵃ (pskl_to_uskl Pa) ∼ Q.
Proof.
  intros Ψt Θ Δ ψa Pa Q Hc Hpre Hwfa Hrig Hwfq.
  unfold ad_precise in Hpre.
  eapply ad_pat_consis_subject_refine with (Δ := Δ);
    [ exact Hpre
    | reflexivity
    | reflexivity
    | intros x b Hb; exact Hb
    | exact Hrig
    | exact Hwfa
    | eapply ad_pat_consis_strip_tags; exact Hc
    | exact Hwfq ].
Qed.
