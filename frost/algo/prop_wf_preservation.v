(** OUTPUT WELL-FORMEDNESS of the consistency and subtyping runs — the
    algorithmic half of the paper's implicit "all types and skeletons in
    judgements are well-formed" convention (WF-SIDE-CONDITIONS.md).

    ⭐ WHY THIS FILE EXISTS (2026-08-07, hand-off §5).  lemma:context-precision
    transports a [P-Var] leaf along an entry's precision via
    lemma:precision-sub, whose external side condition is the DISCIPLINED wf
    of the leaf's subtyping counterpart ([ad_precise_extends_pat_sub],
    prop_completeness_sub_precise.v).  That wf can come only from the RULE
    ([ad_pat]'s base rows), and soundness must then SUPPLY it from the run —
    i.e. the algorithm's own outputs must be well-formed.  Neither the
    declarative join nor refinement gives this (refinement does NOT preserve
    wf — cex/cex_refine_not_transitive.v's capture configuration is
    derivable declaratively); it is a property of the ALGORITHM, proved here.

    ⭐⭐ THE CONSISTENCY INDUCTION'S MOTIVE ([a_consis_output_wf]).  The run's
    Δ1/Δ2 rigid-trackers exist precisely to guard ghost fills (the Ghost /
    GhostR side conditions), and the output-wf induction leans on them:
    besides wf itself the motive carries (i) the output's SHIELDED variables
    (those under a tophole, [pskl_shielded_ftv] — the P6 kit's gadget) avoid
    Δ1 ∪ Δ2, which is what lets the three close-rows re-bind their opened
    rigid ([a_wf_pskl_tvar_to_delta] + [a_wf_pskl_all_of_one]); (ii) an ftv
    PROVENANCE bound (a Δ-variable in the output comes from an input), which
    is what survives a [⊤ ∼ ⊤] merge whose result must be wf at the EMPTY Δ;
    and (iii) head-guardedness propagation for the ⊤-rebuild.  The wf
    hypotheses stay at Δ = ∅ throughout — the Δ-vars are rigids of the run's
    own context, so only the shielded positions ever need the tracking.

    [a_sub_output_wf] then follows by the mutual walk induction, cribbing
    the context surgeries of [a_subtag_sound_bundle] row for row; its arrow
    row consumes [a_consis_output_wf] at Δ1 = Δ2 = ∅. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_extra.
Require Import src.frost.ltac_utils.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.prop_swap.
Require Import src.frost.algo.def_meta.
Require Import src.frost.deco_algo.def_decorated.
Require Import src.frost.algo_decl.def_consis_refine.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.consis.prop_consis_rename.
Require Import src.frost.algo.consis.prop_soundness_consis.
Require Import src.frost.algo.sub.look.prop_rho_relation.
Require Import src.frost.algo.sub.look.prop_solve_ext.
Require Import src.frost.algo.sub.look.prop_sub_var.
Require Import src.frost.algo.consis.prop_completeness_consis.
Require Import src.frost.algo.prop_pat_sub.
Require Import src.frost.algo.prop_metasubst.
Require Import src.frost.algo.sub.prop_looksub.
Require Import src.frost.algo.sub.prop_soundness_sub.
Require Import src.frost.algo.prop_mono_bridge.
Require Import src.frost.algo.prop_precise.

Set Implicit Arguments.

(* ===================================================================== *)
(*  §1  Gadgets                                                          *)
(* ===================================================================== *)

(** A variable-for-variable substitution moves no skeleton in or out of a
    tophole, so when the replaced variable is not shielded the shielded set
    is unchanged. *)
Lemma pskl_shielded_ftv_subst_var_notin : forall P α β,
  β `notin` pskl_shielded_ftv P ->
  pskl_shielded_ftv (subst_pskl_in_pskl (pskl_var_f α) β P)
    [=] pskl_shielded_ftv P.
Proof.
  induction P; intros α0 β Hβ; simpl in *; try fsetdec.
  - (* var_f *) destruct_if; simpl; fsetdec.
  - (* arrow *)
    rewrite IHP1, IHP2; [ fsetdec | fsetdec | fsetdec ].
  - (* all_syn *) apply IHP; fsetdec.
  - (* tophole *)
    rewrite ftvar_in_pskl_subst_pskl_in_pskl_fresh; [ fsetdec | ].
    simpl. fsetdec.
Qed.

(** ⭐ A well-formed ∀-body keeps its binder OUT of every tophole (the
    tophole rule re-checks its body at the empty Δ), so opening with a
    fresh variable adds nothing to the shielded set. *)
Lemma a_wf_pskl_all_shielded_open : forall Θ Δ P α,
  {{ Θ ⨟ Δ ⊢ₚₛ (pskl_all_syn P) }}a ->
  α `notin` dom Θ `union` ftvar_in_pskl P ->
  pskl_shielded_ftv (open_pskl_wrt_pskl P (pskl_var_f α)) [<=] dom Θ.
Proof.
  intros Θ Δ P α Hwf Hα.
  inversion Hwf as [ | | | L Θz Δz Pz Hbody Heq | | ]; subst.
  destruct (atom_fresh (L `union` dom Θ `union` ftvar_in_pskl P
                          `union` singleton α)) as [β Hβ].
  pose proof (a_wf_pskl_shielded_dom (Hbody β ltac:(solve_notin_auto))) as Hdom.
  rewrite (subst_pskl_in_pskl_intro β P (pskl_var_f α) ltac:(solve_notin_auto)).
  rewrite pskl_shielded_ftv_subst_var_notin; [ exact Hdom | ].
  clear - Hdom Hβ. fsetdec.
Qed.

(* ===================================================================== *)
(*  §2  The consistency run's output is well-formed                      *)
(* ===================================================================== *)

Lemma a_consis_output_wf : forall Δ1 Δ2 Θ0 P0 P Q Θ1,
  {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}a ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
  (forall α, α `in` (Δ1 `union` Δ2) -> binds α abind_tvar Θ0) ->
  no_flex_dep (Δ1 `union` Δ2) Θ0 ->
  flex_above_free (Δ1 `union` Δ2) Θ0 ->
  (Δ1 `union` Δ2) ∩ pskl_shielded_ftv P0 [=] empty ->
  (Δ1 `union` Δ2) ∩ pskl_shielded_ftv P [=] empty ->
  ({{ Θ1 ⨟ empty ⊢ₚₛ Q }}a)
  /\ ((Δ1 `union` Δ2) ∩ pskl_shielded_ftv Q [=] empty)
  /\ (forall α, α `in` (Δ1 `union` Δ2) -> α `in` ftvar_in_pskl Q ->
        α `in` (ftvar_in_pskl P0 `union` ftvar_in_pskl P))
  /\ (guarded_pskl P0 -> guarded_pskl P -> guarded_pskl Q).
Proof.
  intros Δ1 Δ2 Θ0 P0 P Q Θ1 Hc.
  induction Hc; intros Hwf HwfP0 HwfP Hcov Hnfd Hfaf Hsh0 Hsh.
  - (* C-Ghost : ◇ ∼ P0, output P0 *)
    split; [ exact HwfP0 | ].
    split; [ exact Hsh0 | ].
    split; [ intros α Hα Hft; clear - Hft; fsetdec | ].
    intros _ Hg; inversion Hg.
  - (* C-Unit *)
    split; [ apply a_wf_pskl__unit | ].
    split; [ simpl; clear; fsetdec | ].
    split; [ intros α Hα Hft; simpl in Hft; clear - Hft; fsetdec | ].
    intros _ _; apply guarded_pskl__unit.
  - (* C-Rigid *)
    split; [ apply a_wf_pskl__var; right; left; exact H | ].
    split; [ simpl; clear; fsetdec | ].
    split; [ intros α0 Hα0 Hft; simpl in *; clear - Hft; fsetdec | ].
    intros _ _; apply guarded_pskl__var.
  - (* C-Arrow *)
    inversion HwfP0 as [ | | Θz Δz P0az P0bz HwfP0a HwfP0b | | | ]; subst.
    inversion HwfP as [ | | Θz Δz P1z P2z HwfP1 HwfP2 | | | ]; subst.
    simpl in Hsh0, Hsh.
    assert (Hsh0a : (Δ1 `union` Δ2) ∩ pskl_shielded_ftv P0a [=] empty)
      by (clear - Hsh0; fsetdec).
    assert (Hsh0b : (Δ1 `union` Δ2) ∩ pskl_shielded_ftv P0b [=] empty)
      by (clear - Hsh0; fsetdec).
    assert (Hsh1 : (Δ1 `union` Δ2) ∩ pskl_shielded_ftv P1 [=] empty)
      by (clear - Hsh; fsetdec).
    assert (Hsh2 : (Δ1 `union` Δ2) ∩ pskl_shielded_ftv P2 [=] empty)
      by (clear - Hsh; fsetdec).
    destruct (IHHc1 Hwf HwfP0a HwfP1 Hcov Hnfd Hfaf Hsh0a Hsh1)
      as [HwfQ1 [HshQ1 [HprovQ1 HgQ1]]].
    destruct (a_consis_sound_aux Hc1 Hwf HwfP0a HwfP1 Hcov Hnfd Hfaf)
      as [Hle1 [Hwf1 [Hnfd1 [Hfaf1 _]]]].
    assert (Hcov1 : forall α, α `in` (Δ1 `union` Δ2) ->
                    binds α abind_tvar Θ1).
    { intros α Hα. destruct Hle1 as [[κ [Hid Hinc]] _].
      eapply a_inc_binds_tvar; [ exact Hinc | apply Hcov; exact Hα ]. }
    assert (HwfP0b1 : {{ Θ1 ⨟ empty ⊢ₚₛ P0b }}a)
      by (eapply a_wf_pskl_isub; [ exact HwfP0b | exact Hle1 ]).
    assert (HwfP21 : {{ Θ1 ⨟ empty ⊢ₚₛ P2 }}a)
      by (eapply a_wf_pskl_isub; [ exact HwfP2 | exact Hle1 ]).
    destruct (IHHc2 Hwf1 HwfP0b1 HwfP21 Hcov1 Hnfd1 Hfaf1 Hsh0b Hsh2)
      as [HwfQ2 [HshQ2 [HprovQ2 HgQ2]]].
    destruct (a_consis_sound_aux Hc2 Hwf1 HwfP0b1 HwfP21 Hcov1 Hnfd1 Hfaf1)
      as [Hle2 [Hwf2 _]].
    split.
    { apply a_wf_pskl__arrow;
        [ eapply a_wf_pskl_isub; [ exact HwfQ1 | exact Hle2 ] | exact HwfQ2 ]. }
    split; [ simpl; clear - HshQ1 HshQ2; fsetdec | ].
    split.
    { intros α Hα Hft. simpl in Hft.
      apply union_1 in Hft. destruct Hft as [Hft | Hft];
        [ pose proof (HprovQ1 α Hα Hft) as Hp
        | pose proof (HprovQ2 α Hα Hft) as Hp ];
        simpl; clear - Hp; fsetdec. }
    intros _ _. apply guarded_pskl__arrow;
      [ eapply a_wf_pskl_lc; exact HwfQ1 | eapply a_wf_pskl_lc; exact HwfQ2 ].
  - (* C-ForallInh : both sides opened, α to both Δs *)
    simpl in Hsh0, Hsh.
    assert (HαP0 : α `notin` ftvar_in_pskl P0) by (clear - H; fsetdec).
    assert (HαP : α `notin` ftvar_in_pskl P) by (clear - H; fsetdec).
    assert (HαΔ : α `notin` (Δ1 `union` Δ2)) by (clear - H; fsetdec).
    assert (HαΘ0 : α `notin` dom Θ0)
      by (pose proof (dom_subset_ftvar_in_aenv Θ0); clear - H H0; fsetdec).
    assert (Hwfx : {{ ⊢ ((α ~ abind_tvar) ++ Θ0) }}a)
      by (apply a_wf_aenv__tvar; [ exact HαΘ0 | exact Hwf ]).
    assert (HwfP0o : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ
                       (open_pskl_wrt_pskl P0 (pskl_var_f α)) }}a)
      by (apply a_wf_pskl_all_syn_open_tvar;
            [ exact HwfP0 | clear - HαΘ0 HαP0; fsetdec ]).
    assert (HwfPo : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ
                      (open_pskl_wrt_pskl P (pskl_var_f α)) }}a)
      by (apply a_wf_pskl_all_syn_open_tvar;
            [ exact HwfP | clear - HαΘ0 HαP; fsetdec ]).
    assert (Hcovx : forall α0, α0 `in` (add α Δ1 `union` add α Δ2) ->
                    binds α0 abind_tvar ((α ~ abind_tvar) ++ Θ0)).
    { intros α0 Hα0. destruct (α0 == α) as [->|Hne];
        [ unfold binds; left; reflexivity
        | unfold binds; right; apply Hcov; clear - Hα0 Hne; fsetdec ]. }
    assert (Hnfdx : no_flex_dep (add α Δ1 `union` add α Δ2)
                      ((α ~ abind_tvar) ++ Θ0))
      by (apply no_flex_dep_cong with (Δ := add α (Δ1 `union` Δ2));
            [ clear; fsetdec | apply no_flex_dep_open_tvar; auto ]).
    assert (Hfafx : flex_above_free (add α Δ1 `union` add α Δ2)
                      ((α ~ abind_tvar) ++ Θ0))
      by (apply faf_cong with (Δ := add α (Δ1 `union` Δ2));
            [ clear; fsetdec
            | apply faf_open_tvar; auto; clear - HαΔ; fsetdec ]).
    assert (Hsh0x : (add α Δ1 `union` add α Δ2) ∩
                    pskl_shielded_ftv (open_pskl_wrt_pskl P0 (pskl_var_f α))
                    [=] empty).
    { pose proof (pskl_shielded_ftv_open_upper P0 (pskl_var_f α)) as Hup.
      simpl in Hup.
      pose proof (a_wf_pskl_all_shielded_open (α := α) HwfP0
                    ltac:(clear - HαΘ0 HαP0; solve_notin_auto)) as Hdo.
      clear - Hup Hdo Hsh0 HαΘ0 HαΔ. fsetdec. }
    assert (Hshx : (add α Δ1 `union` add α Δ2) ∩
                   pskl_shielded_ftv (open_pskl_wrt_pskl P (pskl_var_f α))
                   [=] empty).
    { pose proof (pskl_shielded_ftv_open_upper P (pskl_var_f α)) as Hup.
      simpl in Hup.
      pose proof (a_wf_pskl_all_shielded_open (α := α) HwfP
                    ltac:(clear - HαΘ0 HαP; solve_notin_auto)) as Hdo.
      clear - Hup Hdo Hsh HαΘ0 HαΔ. fsetdec. }
    destruct (IHHc Hwfx HwfP0o HwfPo Hcovx Hnfdx Hfafx Hsh0x Hshx)
      as [HwfQ [HshQ [HprovQ _]]].
    assert (HαshQ : α `notin` pskl_shielded_ftv Q)
      by (clear - HshQ; fsetdec).
    assert (Hwfstr : {{ Θ1 ⨟ (add α empty) ⊢ₚₛ Q }}a).
    { apply (@a_wf_pskl_tvar_to_delta nil α Θ1 empty Q);
        [ exact HwfQ | exact HαshQ ]. }
    assert (Hα1 : α `notin` dom Θ1).
    { pose proof (a_assign_unify_consis_uniq) as [_ [_ Hu]].
      pose proof (Hu _ _ _ _ _ _ _ Hc
                    ltac:(apply a_wf_aenv_uniq; exact Hwfx)) as Hux.
      inversion Hux; subst; auto. }
    split.
    { apply a_wf_pskl_all_of_one with (β := α);
        [ rewrite open_pskl_wrt_pskl_close_pskl_wrt_pskl; exact Hwfstr
        | exact Hα1
        | rewrite ftvar_in_pskl_close_pskl_wrt_pskl; clear; fsetdec ]. }
    split.
    { simpl.
      pose proof (pskl_shielded_ftv_close_upper Q α) as Hcu.
      clear - HshQ Hcu. fsetdec. }
    split.
    { intros α0 Hα0 Hft. simpl in Hft.
      rewrite ftvar_in_pskl_close_pskl_wrt_pskl in Hft.
      assert (Hα0α : α0 <> α) by (clear - Hft; fsetdec).
      assert (Hα0Q : α0 `in` ftvar_in_pskl Q) by (clear - Hft; fsetdec).
      pose proof (HprovQ α0 ltac:(clear - Hα0; solve_notin_auto) Hα0Q) as Hp.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                    P0 (pskl_var_f α)) as Hu0.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                    P (pskl_var_f α)) as Hu1.
      simpl in Hu0, Hu1. simpl.
      clear - Hp Hu0 Hu1 Hα0α. fsetdec. }
    intros Hg _; inversion Hg.
  - (* C-ForallSyn : subject opened (α to Δ2), tophole input kept *)
    simpl in Hsh0, Hsh.
    assert (HαP0 : α `notin` ftvar_in_pskl P0) by (clear - H; fsetdec).
    assert (HαP : α `notin` ftvar_in_pskl P) by (clear - H; fsetdec).
    assert (HαΔ : α `notin` (Δ1 `union` Δ2)) by (clear - H; fsetdec).
    assert (HαΘ0 : α `notin` dom Θ0)
      by (pose proof (dom_subset_ftvar_in_aenv Θ0); clear - H H0; fsetdec).
    assert (Hwfx : {{ ⊢ ((α ~ abind_tvar) ++ Θ0) }}a)
      by (apply a_wf_aenv__tvar; [ exact HαΘ0 | exact Hwf ]).
    assert (HwfP0x : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ (pskl_tophole P0) }}a).
    { eapply a_wf_pskl_delta_mono;
        [ apply (a_wf_pskl_reassoc HwfP0 α) | clear; fsetdec ]. }
    assert (HwfPo : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ
                      (open_pskl_wrt_pskl P (pskl_var_f α)) }}a)
      by (apply a_wf_pskl_all_syn_open_tvar;
            [ exact HwfP | clear - HαΘ0 HαP; fsetdec ]).
    assert (Hcovx : forall α0, α0 `in` (Δ1 `union` add α Δ2) ->
                    binds α0 abind_tvar ((α ~ abind_tvar) ++ Θ0)).
    { intros α0 Hα0. destruct (α0 == α) as [->|Hne];
        [ unfold binds; left; reflexivity
        | unfold binds; right; apply Hcov; clear - Hα0 Hne; fsetdec ]. }
    assert (Hnfdx : no_flex_dep (Δ1 `union` add α Δ2)
                      ((α ~ abind_tvar) ++ Θ0))
      by (apply no_flex_dep_cong with (Δ := add α (Δ1 `union` Δ2));
            [ clear; fsetdec | apply no_flex_dep_open_tvar; auto ]).
    assert (Hfafx : flex_above_free (Δ1 `union` add α Δ2)
                      ((α ~ abind_tvar) ++ Θ0))
      by (apply faf_cong with (Δ := add α (Δ1 `union` Δ2));
            [ clear; fsetdec
            | apply faf_open_tvar; auto; clear - HαΔ; fsetdec ]).
    assert (Hsh0x : (Δ1 `union` add α Δ2) ∩
                    pskl_shielded_ftv (pskl_tophole P0) [=] empty)
      by (simpl; clear - Hsh0 HαP0; fsetdec).
    assert (Hshx : (Δ1 `union` add α Δ2) ∩
                   pskl_shielded_ftv (open_pskl_wrt_pskl P (pskl_var_f α))
                   [=] empty).
    { pose proof (pskl_shielded_ftv_open_upper P (pskl_var_f α)) as Hup.
      simpl in Hup.
      pose proof (a_wf_pskl_all_shielded_open (α := α) HwfP
                    ltac:(clear - HαΘ0 HαP; solve_notin_auto)) as Hdo.
      clear - Hup Hdo Hsh HαΘ0 HαΔ. fsetdec. }
    destruct (IHHc Hwfx HwfP0x HwfPo Hcovx Hnfdx Hfafx Hsh0x Hshx)
      as [HwfQ [HshQ [HprovQ _]]].
    assert (HαshQ : α `notin` pskl_shielded_ftv Q)
      by (clear - HshQ; fsetdec).
    assert (Hwfstr : {{ Θ1 ⨟ (add α empty) ⊢ₚₛ Q }}a).
    { apply (@a_wf_pskl_tvar_to_delta nil α Θ1 empty Q);
        [ exact HwfQ | exact HαshQ ]. }
    assert (Hα1 : α `notin` dom Θ1).
    { pose proof (a_assign_unify_consis_uniq) as [_ [_ Hu]].
      pose proof (Hu _ _ _ _ _ _ _ Hc
                    ltac:(apply a_wf_aenv_uniq; exact Hwfx)) as Hux.
      inversion Hux; subst; auto. }
    split.
    { apply a_wf_pskl_all_of_one with (β := α);
        [ rewrite open_pskl_wrt_pskl_close_pskl_wrt_pskl; exact Hwfstr
        | exact Hα1
        | rewrite ftvar_in_pskl_close_pskl_wrt_pskl; clear; fsetdec ]. }
    split.
    { simpl.
      pose proof (pskl_shielded_ftv_close_upper Q α) as Hcu.
      clear - HshQ Hcu. fsetdec. }
    split.
    { intros α0 Hα0 Hft. simpl in Hft.
      rewrite ftvar_in_pskl_close_pskl_wrt_pskl in Hft.
      assert (Hα0α : α0 <> α) by (clear - Hft; fsetdec).
      assert (Hα0Q : α0 `in` ftvar_in_pskl Q) by (clear - Hft; fsetdec).
      pose proof (HprovQ α0 ltac:(clear - Hα0; solve_notin_auto) Hα0Q) as Hp.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                    P (pskl_var_f α)) as Hu1.
      simpl in Hu1. simpl.
      clear - Hp Hu1 Hα0α. fsetdec. }
    intros _ Hg; inversion Hg.
  - (* C-UnivGhost : ⊤P ∼ ⊤P0 → ⊤Q *)
    inversion HwfP0 as [ | | | | | Θz Δz P0z Hg0 Hwb0 ]; subst.
    inversion HwfP as [ | | | | | Θz Δz Pz Hgs Hwbs ]; subst.
    simpl in Hsh0, Hsh.
    assert (Hsh0b : (Δ1 `union` Δ2) ∩ pskl_shielded_ftv P0 [=] empty)
      by (pose proof (pskl_shielded_ftv_sub_ftv P0) as Hsf;
          clear - Hsh0 Hsf; fsetdec).
    assert (Hshb : (Δ1 `union` Δ2) ∩ pskl_shielded_ftv P [=] empty)
      by (pose proof (pskl_shielded_ftv_sub_ftv P) as Hsf;
          clear - Hsh Hsf; fsetdec).
    destruct (IHHc Hwf Hwb0 Hwbs Hcov Hnfd Hfaf Hsh0b Hshb)
      as [HwfQ [HshQ [HprovQ HgQ]]].
    split.
    { apply a_wf_pskl__tophole; [ apply HgQ; assumption | exact HwfQ ]. }
    split.
    { simpl. intros β. split; [ | clear; fsetdec ].
      intros Hβ.
      assert (Hβ1 : β `in` (Δ1 `union` Δ2)) by (clear - Hβ; fsetdec).
      assert (Hβ2 : β `in` ftvar_in_pskl Q) by (clear - Hβ; fsetdec).
      pose proof (HprovQ β Hβ1 Hβ2) as Hp.
      clear - Hp Hsh0 Hsh Hβ1. fsetdec. }
    split.
    { intros α Hα Hft. simpl in Hft. simpl.
      exact (HprovQ α Hα Hft). }
    intros Hg _; inversion Hg.
  - (* C-UnivGhost1 : ⊤P kept, ∀-input opened (α to Δ1) *)
    simpl in Hsh0, Hsh.
    assert (HαP0 : α `notin` ftvar_in_pskl P0) by (clear - H; fsetdec).
    assert (HαP : α `notin` ftvar_in_pskl P) by (clear - H; fsetdec).
    assert (HαΔ : α `notin` (Δ1 `union` Δ2)) by (clear - H; fsetdec).
    assert (HαΘ0 : α `notin` dom Θ0)
      by (pose proof (dom_subset_ftvar_in_aenv Θ0); clear - H H0; fsetdec).
    assert (Hwfx : {{ ⊢ ((α ~ abind_tvar) ++ Θ0) }}a)
      by (apply a_wf_aenv__tvar; [ exact HαΘ0 | exact Hwf ]).
    assert (HwfP0o : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ
                       (open_pskl_wrt_pskl P0 (pskl_var_f α)) }}a)
      by (apply a_wf_pskl_all_syn_open_tvar;
            [ exact HwfP0 | clear - HαΘ0 HαP0; fsetdec ]).
    assert (HwfPx : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ (pskl_tophole P) }}a).
    { eapply a_wf_pskl_delta_mono;
        [ apply (a_wf_pskl_reassoc HwfP α) | clear; fsetdec ]. }
    assert (Hcovx : forall α0, α0 `in` (add α Δ1 `union` Δ2) ->
                    binds α0 abind_tvar ((α ~ abind_tvar) ++ Θ0)).
    { intros α0 Hα0. destruct (α0 == α) as [->|Hne];
        [ unfold binds; left; reflexivity
        | unfold binds; right; apply Hcov; clear - Hα0 Hne; fsetdec ]. }
    assert (Hnfdx : no_flex_dep (add α Δ1 `union` Δ2)
                      ((α ~ abind_tvar) ++ Θ0))
      by (apply no_flex_dep_cong with (Δ := add α (Δ1 `union` Δ2));
            [ clear; fsetdec | apply no_flex_dep_open_tvar; auto ]).
    assert (Hfafx : flex_above_free (add α Δ1 `union` Δ2)
                      ((α ~ abind_tvar) ++ Θ0))
      by (apply faf_cong with (Δ := add α (Δ1 `union` Δ2));
            [ clear; fsetdec
            | apply faf_open_tvar; auto; clear - HαΔ; fsetdec ]).
    assert (Hsh0x : (add α Δ1 `union` Δ2) ∩
                    pskl_shielded_ftv (open_pskl_wrt_pskl P0 (pskl_var_f α))
                    [=] empty).
    { pose proof (pskl_shielded_ftv_open_upper P0 (pskl_var_f α)) as Hup.
      simpl in Hup.
      pose proof (a_wf_pskl_all_shielded_open (α := α) HwfP0
                    ltac:(clear - HαΘ0 HαP0; solve_notin_auto)) as Hdo.
      clear - Hup Hdo Hsh0 HαΘ0 HαΔ. fsetdec. }
    assert (Hshx : (add α Δ1 `union` Δ2) ∩
                   pskl_shielded_ftv (pskl_tophole P) [=] empty)
      by (simpl; clear - Hsh HαP; fsetdec).
    destruct (IHHc Hwfx HwfP0o HwfPx Hcovx Hnfdx Hfafx Hsh0x Hshx)
      as [HwfQ [HshQ [HprovQ _]]].
    assert (HαshQ : α `notin` pskl_shielded_ftv Q)
      by (clear - HshQ; fsetdec).
    assert (Hwfstr : {{ Θ1 ⨟ (add α empty) ⊢ₚₛ Q }}a).
    { apply (@a_wf_pskl_tvar_to_delta nil α Θ1 empty Q);
        [ exact HwfQ | exact HαshQ ]. }
    assert (Hα1 : α `notin` dom Θ1).
    { pose proof (a_assign_unify_consis_uniq) as [_ [_ Hu]].
      pose proof (Hu _ _ _ _ _ _ _ Hc
                    ltac:(apply a_wf_aenv_uniq; exact Hwfx)) as Hux.
      inversion Hux; subst; auto. }
    split.
    { apply a_wf_pskl_all_of_one with (β := α);
        [ rewrite open_pskl_wrt_pskl_close_pskl_wrt_pskl; exact Hwfstr
        | exact Hα1
        | rewrite ftvar_in_pskl_close_pskl_wrt_pskl; clear; fsetdec ]. }
    split.
    { simpl.
      pose proof (pskl_shielded_ftv_close_upper Q α) as Hcu.
      clear - HshQ Hcu. fsetdec. }
    split.
    { intros α0 Hα0 Hft. simpl in Hft.
      rewrite ftvar_in_pskl_close_pskl_wrt_pskl in Hft.
      assert (Hα0α : α0 <> α) by (clear - Hft; fsetdec).
      assert (Hα0Q : α0 `in` ftvar_in_pskl Q) by (clear - Hft; fsetdec).
      pose proof (HprovQ α0 ltac:(clear - Hα0; solve_notin_auto) Hα0Q) as Hp.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                    P0 (pskl_var_f α)) as Hu0.
      simpl in Hu0. simpl.
      clear - Hp Hu0 Hα0α. fsetdec. }
    intros Hg _; inversion Hg.
  - (* C-UnivGhost2 : subject's ⊤ stripped against a guarded P0 *)
    inversion HwfP as [ | | | | | Θz Δz Pz Hgs Hwbs ]; subst.
    simpl in Hsh.
    assert (Hshb : (Δ1 `union` Δ2) ∩ pskl_shielded_ftv P [=] empty)
      by (pose proof (pskl_shielded_ftv_sub_ftv P) as Hsf;
          clear - Hsh Hsf; fsetdec).
    destruct (IHHc Hwf HwfP0 Hwbs Hcov Hnfd Hfaf Hsh0 Hshb)
      as [HwfQ [HshQ [HprovQ HgQ]]].
    split; [ exact HwfQ | ].
    split; [ exact HshQ | ].
    split.
    { intros α Hα Hft. simpl.
      exact (HprovQ α Hα Hft). }
    intros _ Hg; inversion Hg.
  - (* C-Flex : unify, output the subject variable *)
    assert (Hbα : a_binds_tvar α Θ0).
    { inversion HwfP as [ | Θz Δz αz Hd | | | | ]; subst.
      destruct Hd as [Hd | Hd]; [ clear - Hd; fsetdec | exact Hd ]. }
    pose proof a_assign_unify_consis_sound as [_ [Hus _]].
    destruct (Hus _ _ _ _ H Hwf) as [Hle [Hwf1 _]].
    split.
    { apply a_wf_pskl__var. right.
      eapply a_isub_binds_tvarish; [ exact Hle | exact Hbα ]. }
    split; [ simpl; clear; fsetdec | ].
    split; [ intros α0 Hα0 Hft; simpl in Hft; simpl; clear - Hft; fsetdec | ].
    intros _ _; apply guarded_pskl__var.
  - (* C-FlexL : assign, output the subject variable *)
    assert (Hbα : a_binds_tvar α Θ0).
    { inversion HwfP as [ | Θz Δz αz Hd | | | | ]; subst.
      destruct Hd as [Hd | Hd]; [ clear - Hd; fsetdec | exact Hd ]. }
    pose proof a_assign_unify_consis_sound as [Has _].
    destruct (Has _ _ _ _ _ H0 (a_decls__nil) Hwf HwfP0)
      as [Hle [Hwf1 _]].
    split.
    { apply a_wf_pskl__var. right.
      eapply a_isub_binds_tvarish; [ exact Hle | exact Hbα ]. }
    split; [ simpl; clear; fsetdec | ].
    split; [ intros α0 Hα0 Hft; simpl in Hft; simpl; clear - Hft; fsetdec | ].
    intros _ _; apply guarded_pskl__var.
  - (* C-FlexR : assign the counterpart's variable *)
    assert (Hbα : a_binds_tvar α Θ0).
    { inversion HwfP0 as [ | Θz Δz αz Hd | | | | ]; subst.
      destruct Hd as [Hd | Hd]; [ clear - Hd; fsetdec | exact Hd ]. }
    pose proof a_assign_unify_consis_sound as [Has _].
    destruct (Has _ _ _ _ _ H0 (a_decls__nil) Hwf HwfP)
      as [Hle [Hwf1 _]].
    split.
    { apply a_wf_pskl__var. right.
      eapply a_isub_binds_tvarish; [ exact Hle | exact Hbα ]. }
    split; [ simpl; clear; fsetdec | ].
    split; [ intros α0 Hα0 Hft; simpl in Hft; simpl; clear - Hft; fsetdec | ].
    intros _ _; apply guarded_pskl__var.
  - (* C-GhostR : ◇ input, output the subject *)
    split; [ exact HwfP | ].
    split; [ exact Hsh | ].
    split; [ intros α Hα Hft; clear - Hft; fsetdec | ].
    intros Hg _; inversion Hg.
  - (* C-UnivGhostR : counterpart's ⊤ stripped against a guarded subject *)
    inversion HwfP0 as [ | | | | | Θz Δz P0z Hg0 Hwb0 ]; subst.
    simpl in Hsh0.
    assert (Hsh0b : (Δ1 `union` Δ2) ∩ pskl_shielded_ftv P0 [=] empty)
      by (pose proof (pskl_shielded_ftv_sub_ftv P0) as Hsf;
          clear - Hsh0 Hsf; fsetdec).
    destruct (IHHc Hwf Hwb0 HwfP Hcov Hnfd Hfaf Hsh0b Hsh)
      as [HwfQ [HshQ [HprovQ HgQ]]].
    split; [ exact HwfQ | ].
    split; [ exact HshQ | ].
    split.
    { intros α Hα Hft. simpl.
      exact (HprovQ α Hα Hft). }
    intros Hg _; inversion Hg.
Qed.

(* ===================================================================== *)
(*  §3  The subtyping run's output is well-formed                        *)
(* ===================================================================== *)

(** The ∅|∅ instance of [a_consis_output_wf] — what [a_sub__arrow]'s domain
    premise and [a_sub__check]'s leaf need. *)
Corollary a_consis_output_wf_nil : forall Θ0 P0 P Q Θ1,
  {{ Θ0 ⊢[ P0 ] P ∼ Q ⊣ Θ1 }}a ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
  {{ Θ1 ⨟ empty ⊢ₚₛ Q }}a.
Proof.
  intros * Hc Hwf HwfP0 HwfP.
  destruct (a_consis_output_wf Hc Hwf HwfP0 HwfP
              ltac:(intros α Hα; exfalso; clear - Hα; solve_notin_auto)
              ltac:(intros β τ Hb; clear; solve_notin_auto)
              ltac:(intros Θa β b Θb Heq Hne; clear; solve_notin_auto)
              ltac:(clear; solve_notin_auto)
              ltac:(clear; solve_notin_auto))
    as [HwfQ _].
  exact HwfQ.
Qed.

(** The ∅|∅ ⊴/wf facts off the packaged soundness corollary. *)
Corollary a_consis_isub_wf_nil : forall Θ0 P0 P Q Θ1,
  {{ Θ0 ⊢[ P0 ] P ∼ Q ⊣ Θ1 }}a ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
  Θ0 ⊴ Θ1 /\ {{ ⊢ Θ1 }}a.
Proof.
  intros * Hc Hwf HwfP0 HwfP.
  destruct (a_consis_sound_aux Hc Hwf HwfP0 HwfP
              ltac:(intros α Hα; exfalso; clear - Hα; solve_notin_auto)
              ltac:(intros β τ Hb; clear; solve_notin_auto)
              ltac:(intros Θa β b Θb Heq Hne; clear; solve_notin_auto))
    as [Hle [Hwf1 _]].
  exact (conj Hle Hwf1).
Qed.

Definition sub_owf_concl (NM : a_sub_mode) (M : mode) (P0 : pskl)
    (Θ0 : aenv) (P P' : pskl) (Θ1 : aenv) : Prop :=
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
  Θ0 ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\ {{ Θ1 ⨟ empty ⊢ₚₛ P' }}a.

Definition sub_flex_owf_concl (NM : a_sub_mode) (M : mode) (P0 : pskl)
    (Θ0 Ξ : aenv) (α : atom) (Q : pskl) (Θ1 : aenv) : Prop :=
  {{ ⊢ (Ξ ++ Θ0) }}a ->
  a_decls Ξ ->
  {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a ->
  a_binds_tvar α (Ξ ++ Θ0) ->
  (Ξ ++ Θ0) ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\ {{ Θ1 ⨟ empty ⊢ₚₛ Q }}a.

Lemma a_sub_output_wf_bundle :
  (forall NM M P0 Θ0 P P' Θ1,
     a_sub NM M P0 Θ0 P P' Θ1 ->
     sub_owf_concl NM M P0 Θ0 P P' Θ1) /\
  (forall NM M P0 Θ0 Ξ α Q Θ1,
     a_sub_flex NM M P0 Θ0 Ξ α Q Θ1 ->
     sub_flex_owf_concl NM M P0 Θ0 Ξ α Q Θ1).
Proof.
  apply (a_sub_sub_flex_tm_mutind
           (fun NM M P0 Θ0 P P' Θ1 _ => sub_owf_concl NM M P0 Θ0 P P' Θ1)
           (fun NM M P0 Θ0 Ξ α Q Θ1 _ =>
              sub_flex_owf_concl NM M P0 Θ0 Ξ α Q Θ1));
    unfold sub_owf_concl, sub_flex_owf_concl.
  - (* Infer : output = subject, context unchanged *)
    intros NM P Θ0 Hwf HwfP0 HwfP.
    split; [ apply a_isub_refl; exact Hwf | ].
    split; [ exact Hwf | exact HwfP ].
  - (* Check (TY) : output = the check-against B *)
    intros Θ0 Θ1 A B Hgfa Hgfb Hga Hgb Hc Hwf HwfP0 HwfP.
    destruct Hc as [Qc Hc].
    destruct (a_consis_isub_wf_nil Hc Hwf HwfP0 HwfP) as [Hle Hwf1].
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    eapply a_wf_pskl_isub; [ exact HwfP0 | exact Hle ].
  - (* ForallR (TY) : open the binder, run the body, strip suffix+rigid *)
    intros α Θ0 Θ1 Ξ A B Hgf Hsuf Huq Hfr Hprem IH Hwf HwfP0 HwfP.
    rewrite dom_app in Hfr.
    assert (HαΘ0 : α `notin` dom Θ0) by (clear - Hfr; fsetdec).
    destruct (IH ltac:(apply a_wf_aenv__tvar;
                         [ exact HαΘ0 | exact Hwf ])
                ltac:(eapply a_wf_pskl_all_syn_open_tvar;
                        [ exact HwfP0 | clear - Hfr HαΘ0; simpl in Hfr; solve_notin_auto ])
                ltac:(eapply a_wf_pskl_delta_mono;
                        [ apply (a_wf_pskl_reassoc HwfP α) | clear; solve_notin_auto ]))
      as [Hle [Hwf1 HwfOut]].
    assert (HuqT : uniq (Ξ ++ (α ~ abind_tvar) ++ Θ1))
      by (apply a_wf_aenv_uniq; exact Hwf1).
    assert (Hwf1' : {{ ⊢ Θ1 }}a)
      by (eapply a_wf_aenv_strip_prefix_suffix_local; exact Hwf1).
    assert (Hle0 : Θ0 ⊴ Θ1)
      by (eapply a_isub_strip_tvar_mid with (Ξ := Ξ);
            [ exact HuqT | exact Huq | exact HαΘ0 | exact Hle ]).
    split; [ exact Hle0 | ]. split; [ exact Hwf1' | ].
    eapply a_wf_pskl_isub; [ exact HwfP0 | exact Hle0 ].
  - (* UnivGhostR (SK) : output ⊤subject, context unchanged *)
    intros Θ0 P Hg Hwf HwfP0 HwfP.
    split; [ apply a_isub_refl; exact Hwf | ].
    split; [ exact Hwf | ].
    apply a_wf_pskl__tophole; [ exact Hg | exact HwfP ].
  - (* FlexMono : hand to the walk at the empty pending suffix *)
    intros NM M P0 Θ0 Θ1 α Q Hf IHf Hwf HwfP0 HwfP.
    assert (Hbα : a_binds_tvar α Θ0).
    { inversion HwfP as [ | Θz Δz αz Hd | | | | ]; subst.
      destruct Hd as [Hd | Hd]; [ exfalso; clear - Hd; fsetdec | exact Hd ]. }
    destruct (IHf ltac:(simpl_env; exact Hwf) a_decls__nil
                ltac:(simpl_env; exact HwfP0)
                ltac:(simpl_env; exact Hbα))
      as [Hle [Hwf1 HwfQ]].
    simpl_env in Hle.
    split; [ exact Hle | ]. split; [ exact Hwf1 | exact HwfQ ].
  - (* Arrow : consis on the domain, recurse on the codomain *)
    intros NM M Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc Hs IHs Hwf HwfP0 HwfP.
    inversion HwfP0 as [ | | Θz Δz P0az P0bz HwfP0a HwfP0b | | | ]; subst.
    inversion HwfP as [ | | Θz Δz P1z P2z HwfP1 HwfP2 | | | ]; subst.
    destruct (a_consis_isub_wf_nil Hc Hwf HwfP0a HwfP1) as [Hle1 Hwf1].
    pose proof (a_consis_output_wf_nil Hc Hwf HwfP0a HwfP1) as HwfQ1.
    destruct (IHs Hwf1
                ltac:(eapply a_wf_pskl_isub; [ exact HwfP0b | exact Hle1 ])
                ltac:(eapply a_wf_pskl_isub; [ exact HwfP2 | exact Hle1 ]))
      as [Hle2 [Hwf2 HwfQ2]].
    split; [ eapply a_isub_trans; [ exact Hle1 | exact Hle2 ] | ].
    split; [ exact Hwf2 | ].
    apply a_wf_pskl__arrow;
      [ eapply a_wf_pskl_isub; [ exact HwfQ1 | exact Hle2 ] | exact HwfQ2 ].
  - (* ForallL : instantiate; the disciplined wf of P1 is ON the rule *)
    intros α NM M P0 Θ0 Θ1 P Q Ξ P1
      Hne Hgor Hfr Hex Huq HwfP1 Hs IHs Hwf HwfP0 HwfP.
    assert (Hdecls : a_decls Ξ) by (eapply a_extract_decls; eauto).
    assert (HwfΞΘ : {{ ⊢ (Ξ ++ Θ0) }}a).
    { apply a_wf_aenv_prepend_decls; auto.
      - clear - Huq. solve_uniq.
      - intros γ Hγ. clear - Huq Hγ. destruct_uniq.
        unfold disjoint in *. fsetdec. }
    assert (Hmono : forall x (b : abind),
               binds x b Θ0 -> binds x b (Ξ ++ Θ0))
      by (intros x b Hb; unfold binds in *; apply in_or_app; auto).
    assert (HwfP0' : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a)
      by (eapply a_wf_pskl_weaken; [ exact Hmono | exact HwfP0 ]).
    assert (HwfSo : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ (open_pskl_wrt_pskl P P1) }}a).
    { inversion HwfP as [ | | | Lb Θb Δb Pb Hbody | | ]; subst.
      apply a_wf_pskl_open with (L := Lb);
        [ intros α0 Hα0;
          eapply a_wf_pskl_weaken; [ exact Hmono | apply Hbody; auto ]
        | exact HwfP1 ]. }
    destruct (IHs HwfΞΘ HwfP0' HwfSo) as [Hle [Hwf1 HwfQ]].
    split; [ eapply a_isub_strengthen_decls_src; eauto | ].
    split; [ exact Hwf1 | exact HwfQ ].
  - (* Ghost (SK) : output = the check-against, context unchanged *)
    intros M Θ0 P0 Hwf HwfP0 HwfP.
    split; [ apply a_isub_refl; exact Hwf | ].
    split; [ exact Hwf | exact HwfP0 ].
  - (* UnivGhostL (SK) : strip the subject's ⊤ *)
    intros M Θ0 Θ1 P0 P Q Hne Hs IHs Hwf HwfP0 HwfP.
    inversion HwfP as [ | | | | | Θz Δz Pz Hgs Hwbs ]; subst.
    exact (IHs Hwf HwfP0 Hwbs).
  - (* Flex-Solve : deposit α̂0 ≔ α̂→β̂ and recurse on the arrow *)
    intros NM M P0 Θ0 Θ1 Ξ α0 α β Q Hne Hαf Hβf Hprem IH Hwf Hdecl HwfP0 Hαb.
    set (τab := ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)).
    set (Θmid := (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0).
    set (Θ' := Ξ ++ (α0 ~ abind_flex_mono_def τab) ++ Θmid).
    assert (Huq : uniq (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Hwf0 : {{ ⊢ Θ0 }}a).
    { eapply a_wf_aenv_app_r with (Θp := Ξ ++ (α0 ~ abind_flex_mono)).
      simpl_env. exact Hwf. }
    assert (Hbα : binds α abind_flex_mono Θmid)
      by (unfold Θmid; unfold binds; simpl; right; left; reflexivity).
    assert (Hbβ : binds β abind_flex_mono Θmid)
      by (unfold Θmid; unfold binds; simpl; left; reflexivity).
    assert (Hwfmid : {{ ⊢ Θmid }}a).
    { unfold Θmid. apply a_wf_aenv__flex.
      { simpl. clear - Hβf Hne. simpl_env in *. fsetdec. }
      apply a_wf_aenv__flex;
        [ clear - Hαf; simpl_env in *; fsetdec | exact Hwf0 ]. }
    assert (Hwfdef : {{ ⊢ ((α0 ~ abind_flex_mono_def τab) ++ Θmid) }}a).
    { apply a_wf_aenv__flex_def.
      - unfold Θmid. simpl. clear - Hαf Hβf Huq. simpl_env in *. solve_uniq.
      - apply a_wf_ptyp__arrow; apply a_wf_ptyp__var;
          [ right; left; exact Hbα | right; left; exact Hbβ ].
      - repeat constructor.
      - exact Hwfmid. }
    assert (HwfΘ' : {{ ⊢ Θ' }}a).
    { unfold Θ'. apply a_wf_aenv_prepend_decls; auto.
      - clear - Huq. solve_uniq.
      - intros γ Hγ. unfold Θmid. simpl_env.
        clear - Huq Hαf Hβf Hγ. destruct_uniq.
        unfold disjoint in *. simpl_env in *. fsetdec. }
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
    destruct (IH HwfΘ'
                ltac:(eapply a_wf_pskl_isub; [ exact HwfP0 | exact Hlift ])
                ltac:(apply a_wf_pskl__arrow; apply a_wf_pskl__var;
                        right; right; left;
                        (unfold Θ'; unfold binds; apply in_or_app; right;
                         simpl; right; auto)))
      as [Hle [Hwf1 HwfQ]].
    split;
      [ eapply a_isub_trans; [ exact Hlift | exact Hle ] | ].
    split; [ exact Hwf1 | exact HwfQ ].
  - (* Flex-Assign : merge and re-enter with the substituted subject *)
    intros NM M P0 Θ0 Θ1 Ξ α β τ Q Hβ1 Hprem IH Hwf Hdecl HwfP0 Hαb.
    assert (Hwfcons : {{ ⊢ ((β ~ abind_flex_mono_def τ) ++ Θ0) }}a)
      by (eapply a_wf_aenv_strip_prefix; eauto).
    inversion Hwfcons as [ | | βz τz Θz HβΘ0 Hwfτ Hm Hwf0 | | | ]; subst.
    assert (HβΞΘ0 : β `notin` dom (Ξ ++ Θ0)).
    { pose proof (a_wf_aenv_uniq Hwf) as Huq.
      clear - Huq. simpl_env in Huq. destruct_uniq.
      unfold disjoint in *. simpl_env in *. fsetdec. }
    assert (HwfΞΘ0 : {{ ⊢ (Ξ ++ Θ0) }}a)
      by (eapply a_wf_aenv_strip_mid; eauto).
    assert (Hwfpaint : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ ptyp_to_pskl τ }}a).
    { apply a_scope_pskl_of_ptyp_vis;
        [ apply mono_ptyp_lc; exact Hm | ].
      intros α1 Hα1. right.
      pose proof (a_wf_ptyp_ftv_tvarish Hwfτ Hα1) as Ht.
      destruct Ht as [Hb | [Hb | [τ1 Hb]]];
        [ left | right; left | right; right; exists τ1 ];
        unfold binds in *; apply in_or_app; auto. }
    assert (HwfP0' : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ
              subst_pskl_in_pskl (ptyp_to_pskl τ) β P0 }}a).
    { eapply a_wf_pskl_subst_ctx with (b := abind_flex_mono_def τ);
        [ exact HwfP0 | reflexivity | exact HβΞΘ0 | clear; fsetdec
        | apply mono_ptyp_to_pskl_guarded; exact Hm | exact Hwfpaint ]. }
    assert (Hwfvarsub : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ
              subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α) }}a).
    { eapply a_wf_pskl_subst_ctx with (b := abind_flex_mono_def τ);
        [ apply a_wf_pskl__var; right; exact Hαb
        | reflexivity | exact HβΞΘ0 | clear; fsetdec
        | apply mono_ptyp_to_pskl_guarded; exact Hm | exact Hwfpaint ]. }
    destruct (IH HwfΞΘ0 HwfP0' Hwfvarsub) as [Hle [Hwf1 HwfQ]].
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
    eapply a_wf_pskl_weaken;
      [ intros y b0 Hb; unfold binds; right; exact Hb | exact HwfQ ].
  - (* Flex-Depend : β̂ joins the pending suffix *)
    intros NM M P0 Θ0 Θ1 Ξ α β Q Hne Hin Hprem IH Hwf Hdecl HwfP0 Hαb.
    assert (Hdecl' : a_decls (Ξ ++ (β ~ abind_flex_mono)))
      by (apply a_decls_app;
          [ exact Hdecl | apply (a_decls__cons β); apply a_decls__nil ]).
    destruct (IH ltac:(simpl_env; simpl_env in Hwf; exact Hwf) Hdecl'
                ltac:(simpl_env; simpl_env in HwfP0; exact HwfP0)
                ltac:(simpl_env; simpl_env in Hαb; exact Hαb))
      as [Hle [Hwf1 HwfQ]].
    split; [ simpl_env in Hle; simpl_env; exact Hle | ].
    split; [ exact Hwf1 | exact HwfQ ].
  - (* Flex-Skip : strip the flexible head, re-cons on the way out *)
    intros NM M P0 Θ0 Θ1 Ξ α β Q Hne Hni Hβ1 Hprem IH Hwf Hdecl HwfP0 Hαb.
    assert (Hwf' : {{ ⊢ (Ξ ++ Θ0) }}a)
      by (eapply a_wf_aenv_strip_mid; eauto).
    assert (HwfP0' : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a)
      by (eapply a_wf_pskl_strip_mid; eauto).
    destruct (IH Hwf' Hdecl HwfP0'
                ltac:(eapply a_binds_tvar_strip_mid;
                        [ exact Hαb
                        | intro He; inversion He; subst;
                          exact (Hne eq_refl)
                        | intro He; inversion He; subst;
                          exact (Hne eq_refl)
                        | intros τ1 He; inversion He; subst;
                          exact (Hne eq_refl) ]))
      as [Hle [Hwf1 HwfQ]].
    split.
    { apply a_isub_prepend_decls_src; auto.
      { intros γ Hb.
        apply a_binds_tvar_weaken_cons.
        eapply a_isub_binds_flex; [ exact Hle | ].
        unfold binds; apply in_or_app; left; exact Hb. }
      apply a_isub_cons_flex.
      eapply a_isub_strengthen_decls_src; eauto. }
    split; [ apply a_wf_aenv__flex; auto | ].
    eapply a_wf_pskl_weaken;
      [ intros y b0 Hb; unfold binds; right; exact Hb | exact HwfQ ].
  - (* Flex-SkipRigid *)
    intros NM M P0 Θ0 Θ1 Ξ α β Q Hne Hni Hβ1 Hprem IH Hwf Hdecl HwfP0 Hαb.
    assert (Hwf' : {{ ⊢ (Ξ ++ Θ0) }}a)
      by (eapply a_wf_aenv_strip_mid; eauto).
    assert (HwfP0' : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a)
      by (eapply a_wf_pskl_strip_mid; eauto).
    destruct (IH Hwf' Hdecl HwfP0'
                ltac:(eapply a_binds_tvar_strip_mid;
                        [ exact Hαb
                        | intro He; inversion He; subst;
                          exact (Hne eq_refl)
                        | intro He; inversion He; subst;
                          exact (Hne eq_refl)
                        | intros τ1 He; inversion He; subst;
                          exact (Hne eq_refl) ]))
      as [Hle [Hwf1 HwfQ]].
    split.
    { apply a_isub_prepend_decls_src; auto.
      { intros γ Hb.
        apply a_binds_tvar_weaken_cons.
        eapply a_isub_binds_flex; [ exact Hle | ].
        unfold binds; apply in_or_app; left; exact Hb. }
      apply a_isub_cons_tvar.
      eapply a_isub_strengthen_decls_src; eauto. }
    split; [ apply a_wf_aenv__tvar; auto | ].
    eapply a_wf_pskl_weaken;
      [ intros y b0 Hb; unfold binds; right; exact Hb | exact HwfQ ].
  - (* Flex-SkipTmVar (type entry) *)
    intros NM M P0 Θ0 Θ1 Ξ α x Apay Q Hxout Hprem IH Hwf Hdecl HwfP0 Hαb.
    assert (Huq : uniq (Ξ ++ (x ~ abind_var_typ Apay) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Hbx : binds x (abind_var_typ Apay)
                    (Ξ ++ (x ~ abind_var_typ Apay) ++ Θ0))
      by (apply binds_app_3; apply binds_app_2;
          unfold binds; simpl; left; reflexivity).
    assert (Hxfr : x `notin` ftvar_in_pskl P0).
    { intro Hin.
      destruct (a_wf_pskl_ftv_tvarish HwfP0 Hin) as [Hemp | Hbt];
        [ clear - Hemp; fsetdec | ].
      destruct Hbt as [Hb | [Hb | [τ0 Hb]]];
        pose proof (binds_unique _ _ _ _ _ Hbx Hb Huq) as Hcx;
        discriminate Hcx. }
    assert (Hwf' : {{ ⊢ (Ξ ++ Θ0) }}a)
      by (eapply a_wf_aenv_strip_mid; eauto).
    assert (HwfT : {{ ⊢ ((x ~ abind_var_typ Apay) ++ Θ0) }}a)
      by (eapply a_wf_aenv_app_r; exact Hwf).
    apply a_wf_aenv_var_typ_inv in HwfT.
    destruct HwfT as [_ [HwfQ0 _]].
    assert (HwfQ' : a_wf_ptyp (Ξ ++ Θ0) Apay)
      by (eapply a_wf_ptyp_weaken;
          [ intros y b0 Hb; apply binds_app_3; exact Hb | exact HwfQ0 ]).
    destruct (IH Hwf' Hdecl
                ltac:(eapply a_wf_pskl_strip_mid; [ exact HwfP0 | exact Hxfr ])
                ltac:(eapply a_binds_tvar_strip_mid;
                        [ exact Hαb
                        | intro He; discriminate He
                        | intro He; discriminate He
                        | intros τ1 He; discriminate He ]))
      as [Hle [Hwf1 HwfQ]].
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
    eapply a_wf_pskl_weaken;
      [ intros y b0 Hb; unfold binds; right; exact Hb | exact HwfQ ].
  - (* Flex-SkipTmVar (skeleton entry) *)
    intros NM M P0 Θ0 Θ1 Ξ α x Qpay Q Hxout Hprem IH Hwf Hdecl HwfP0 Hαb.
    assert (Huq : uniq (Ξ ++ (x ~ abind_var_skl Qpay) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Hbx : binds x (abind_var_skl Qpay)
                    (Ξ ++ (x ~ abind_var_skl Qpay) ++ Θ0))
      by (apply binds_app_3; apply binds_app_2;
          unfold binds; simpl; left; reflexivity).
    assert (Hxfr : x `notin` ftvar_in_pskl P0).
    { intro Hin.
      destruct (a_wf_pskl_ftv_tvarish HwfP0 Hin) as [Hemp | Hbt];
        [ clear - Hemp; fsetdec | ].
      destruct Hbt as [Hb | [Hb | [τ0 Hb]]];
        pose proof (binds_unique _ _ _ _ _ Hbx Hb Huq) as Hcx;
        discriminate Hcx. }
    assert (Hwf' : {{ ⊢ (Ξ ++ Θ0) }}a)
      by (eapply a_wf_aenv_strip_mid; eauto).
    assert (HwfT : {{ ⊢ ((x ~ abind_var_skl Qpay) ++ Θ0) }}a)
      by (eapply a_wf_aenv_app_r; exact Hwf).
    apply a_wf_aenv_var_skl_inv in HwfT.
    destruct HwfT as [_ [HscQ0 _]].
    assert (HscQ' : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ Qpay }}a)
      by (eapply a_wf_pskl_weaken;
          [ intros y b0 Hb; apply binds_app_3; exact Hb | exact HscQ0 ]).
    destruct (IH Hwf' Hdecl
                ltac:(eapply a_wf_pskl_strip_mid; [ exact HwfP0 | exact Hxfr ])
                ltac:(eapply a_binds_tvar_strip_mid;
                        [ exact Hαb
                        | intro He; discriminate He
                        | intro He; discriminate He
                        | intros τ1 He; discriminate He ]))
      as [Hle [Hwf1 HwfQ]].
    split.
    { apply a_isub_prepend_decls_src; auto.
      { intros γ Hb.
        apply a_binds_tvar_weaken_cons.
        eapply a_isub_binds_flex; [ exact Hle | ].
        unfold binds; apply in_or_app; left; exact Hb. }
      apply a_isub_cons_var_skl;
        [ eapply a_isub_strengthen_decls_src; eauto
        | eapply a_scope_pskl_lc; eauto ]. }
    split.
    { apply a_wf_aenv__var; [ exact Hxout | | exact Hwf1 ].
      eapply a_wf_pskl_isub; [ exact HscQ' | exact Hle ]. }
    eapply a_wf_pskl_weaken;
      [ intros y b0 Hb; unfold binds; right; exact Hb | exact HwfQ ].
Qed.

(** The paper-facing corollary: an [a_sub] run from well-formed inputs has a
    WELL-FORMED output, in the output context. *)
Corollary a_sub_output_wf : forall NM M P0 Θ0 P P' Θ1,
  a_sub NM M P0 Θ0 P P' Θ1 ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
  {{ Θ1 ⨟ empty ⊢ₚₛ P' }}a.
Proof.
  intros * Hrun Hwf HwfP0 HwfP.
  destruct ((proj1 a_sub_output_wf_bundle) _ _ _ _ _ _ _ Hrun Hwf HwfP0 HwfP)
    as [_ [_ HwfOut]].
  exact HwfOut.
Qed.
