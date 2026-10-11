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
    declarative join nor refinement gives this (the refinement rules alone
    do NOT preserve wf — [ad_refine_syn_output_not_wf],
    cex/cex_refine_not_transitive.v; the paper presupposes it instead); it
    is a property of the ALGORITHM, proved here.

    ⭐⭐ THE CONSISTENCY INDUCTION'S MOTIVE ([a_consis_output_wf]).  The run's
    Δ1/Δ2 rigid-trackers exist precisely to guard ghost fills (the Ghost /
    GhostR side conditions), and the output-wf induction leans on them:
    besides wf itself the motive carries (i) the output's SHIELDED variables
    (those under a univ_ghost, [pskl_shielded_ftv] — the P6 kit's gadget) avoid
    Δ1 ∪ Δ2, which is what lets the three close-rows re-bind their opened
    rigid ([a_wf_pskl_tvar_to_delta] + [a_wf_pskl_all_of_one_at]); (ii) an ftv
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

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo_decl.prop_stability.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo_decl.prop_refinement.
Require Import src.fresco.algo.consistency.prop_consis_rename.
Require Import src.fresco.algo.consistency.prop_soundness_consis.
Require Import src.fresco.algo.subtyping.prop_rigid_substitution.
Require Import src.fresco.algo.subtyping.prop_solve_extension.
Require Import src.fresco.algo.subtyping.prop_completeness_solve_sub_var.
Require Import src.fresco.algo.consistency.prop_completeness_consis.
Require Import src.fresco.algo_decl.prop_subtyping.
Require Import src.fresco.algo.basic.prop_metasubst.
Require Import src.fresco.algo.subtyping.prop_looksub.
Require Import src.fresco.algo.subtyping.prop_soundness_subtag.
Require Import src.fresco.algo.consistency.prop_consis_monotype_equiv.
Require Import src.fresco.algo_decl.prop_precision.

Set Implicit Arguments.

(* ===================================================================== *)
(*  §1  Gadgets                                                          *)
(* ===================================================================== *)

(** A variable-for-variable substitution moves no skeleton in or out of a
    univ_ghost, so when the replaced variable is not shielded the shielded set
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
  - (* univ_ghost *)
    rewrite ftvar_in_pskl_subst_pskl_in_pskl_fresh; [ fsetdec | ].
    simpl. fsetdec.
Qed.

(** ⭐ A well-formed ∀-body keeps its binder OUT of every univ_ghost (the
    binder enters Δ, and the univ_ghost rule re-checks its body at Θ∖Δ), so
    opening with a fresh variable adds nothing to the shielded set. *)
Lemma a_wf_pskl_all_shielded_open : forall Θ Δ P α,
  {{ Θ ⨟ Δ ⊢ₚₛ (pskl_all_syn P) }}a ->
  α `notin` dom Θ `union` ftvar_in_pskl P ->
  pskl_shielded_ftv (open_pskl_wrt_pskl P (pskl_var_f α)) [<=] dom Θ.
Proof.
  intros Θ Δ P α Hwf Hα.
  inversion Hwf as [ | | | L Θz Δz Pz Hbody Heq | | ]; subst.
  destruct (atom_fresh (L `union` dom Θ `union` ftvar_in_pskl P
                          `union` singleton α)) as [β Hβ].
  pose proof (Hbody β ltac:(solve_notin_auto)) as Hb.
  pose proof (a_wf_pskl_shielded_dom Hb) as Hdom.
  pose proof (@a_wf_pskl_shielded_delta _ _ _ Hb β ltac:(clear; fsetdec)) as Hsh.
  simpl in Hdom.
  rewrite (subst_pskl_in_pskl_intro β P (pskl_var_f α) ltac:(solve_notin_auto)).
  rewrite pskl_shielded_ftv_subst_var_notin; [ clear - Hdom Hsh; fsetdec | ].
  exact Hsh.
Qed.

(** Opening a well-formed ∀ with a fresh [α] keeps every variable set that
    avoided the body's shielded variables — up to [α] itself — clear of the
    opened body's.  ⚠️ PERF: as ONE [fsetdec] this cost 24-30 s per use.
    Elementwise, every call below sees at most three set variables. *)
Lemma pskl_shielded_open_disjoint : forall Θ Δ P α D D',
  {{ Θ ⨟ Δ ⊢ₚₛ (pskl_all_syn P) }}a ->
  α `notin` dom Θ -> α `notin` ftvar_in_pskl P ->
  D ∩ pskl_shielded_ftv P [=] empty ->
  D' [<=] add α D ->
  D' ∩ pskl_shielded_ftv (open_pskl_wrt_pskl P (pskl_var_f α)) [=] empty.
Proof.
  intros * HwfP HαΘ HαP Hsh HD'.
  pose proof (pskl_shielded_ftv_open_upper P (pskl_var_f α)) as Hup.
  simpl in Hup.
  assert (HαΘP : α `notin` dom Θ `union` ftvar_in_pskl P)
    by (clear - HαΘ HαP; solve_notin_auto).
  pose proof (a_wf_pskl_all_shielded_open HwfP HαΘP) as Hdo.
  assert (HαS : α `notin`
            pskl_shielded_ftv (open_pskl_wrt_pskl P (pskl_var_f α)))
    by (clear - Hdo HαΘ; fsetdec).
  intros z; split; intros Hz; [ exfalso | clear - Hz; fsetdec ].
  assert (HzS : z `in` pskl_shielded_ftv
                  (open_pskl_wrt_pskl P (pskl_var_f α)))
    by (clear - Hz; fsetdec).
  assert (Hzα : z <> α) by (intros ->; clear - HzS HαS; fsetdec).
  assert (HzD : z `in` D) by (clear - Hz Hzα HD'; fsetdec).
  apply Hup in HzS.
  assert (HzP : z `in` pskl_shielded_ftv P)
    by (clear - HzS Hzα; fsetdec).
  clear - HzD HzP Hsh. fsetdec.
Qed.

(** The output of a consistency row that opened a binder [α] and closes it
    again: well-formedness, the shielded-set side condition and provenance
    all transfer through [∀ (close α Q)]. *)
Lemma consis_close_output_wf : forall Θ1 α Q D D' S X0 X,
  {{ ((α ~ abind_tvar) ++ Θ1) ⨟ empty ⊢ₚₛ Q }}a ->
  D ∩ pskl_shielded_ftv Q [=] empty ->
  (forall β, β `in` D -> β `in` ftvar_in_pskl Q -> β `in` S) ->
  add α D' [<=] D ->
  S [<=] add α (ftvar_in_pskl X0 `union` ftvar_in_pskl X) ->
  (guarded_pskl X0 -> guarded_pskl X ->
     guarded_pskl (pskl_all_syn (close_pskl_wrt_pskl α Q))) ->
  {{ Θ1 ⨟ empty ⊢ₚₛ (pskl_all_syn (close_pskl_wrt_pskl α Q)) }}a
  /\ (D' ∩ pskl_shielded_ftv (pskl_all_syn (close_pskl_wrt_pskl α Q)) [=] empty)
  /\ (forall β, β `in` D' ->
        β `in` ftvar_in_pskl (pskl_all_syn (close_pskl_wrt_pskl α Q)) ->
        β `in` (ftvar_in_pskl X0 `union` ftvar_in_pskl X))
  /\ (guarded_pskl X0 -> guarded_pskl X ->
        guarded_pskl (pskl_all_syn (close_pskl_wrt_pskl α Q))).
Proof.
  intros * HwfQ HshQ Hprov HD' HS Hg.
  assert (HαshQ : α `notin` pskl_shielded_ftv Q)
    by (clear - HshQ HD'; fsetdec).
  split.
  { apply a_wf_pskl_all_of_one_at with (β := α).
    - rewrite open_pskl_wrt_pskl_close_pskl_wrt_pskl.
      apply a_wf_pskl_tvar_to_delta_gen; assumption.
    - rewrite ftvar_in_pskl_close_pskl_wrt_pskl. clear; fsetdec. }
  split.
  { simpl. pose proof (pskl_shielded_ftv_close_upper Q α) as Hcu.
    clear - HshQ Hcu HD'. fsetdec. }
  split; [ | exact Hg ].
  intros β Hβ Hft. simpl in Hft.
  rewrite ftvar_in_pskl_close_pskl_wrt_pskl in Hft.
  assert (Hβα : β <> α) by (clear - Hft; fsetdec).
  assert (HβQ : β `in` ftvar_in_pskl Q) by (clear - Hft; fsetdec).
  assert (HβD : β `in` D) by (clear - Hβ HD'; fsetdec).
  pose proof (Hprov β HβD HβQ) as Hp.
  clear - Hp HS Hβα. fsetdec.
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
    split; [ apply a_wf_pskl__var; left; exact H | ].
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
    destruct (@delta_inv_open_tvar (Δ1 `union` Δ2) (add α Δ1 `union` add α Δ2) α Θ0
                ltac:(auto) ltac:(auto) ltac:(clear; fsetdec) Hcov
                ltac:(auto) ltac:(auto))
      as (Hcovx & Hnfdx & Hfafx).
    assert (Hsh0x : (add α Δ1 `union` add α Δ2) ∩
                    pskl_shielded_ftv (open_pskl_wrt_pskl P0 (pskl_var_f α)) [=] empty)
      by (apply (pskl_shielded_open_disjoint HwfP0 HαΘ0 HαP0 Hsh0); clear; fsetdec).
    assert (Hshx : (add α Δ1 `union` add α Δ2) ∩
                    pskl_shielded_ftv (open_pskl_wrt_pskl P (pskl_var_f α)) [=] empty)
      by (apply (pskl_shielded_open_disjoint HwfP HαΘ0 HαP Hsh); clear; fsetdec).
    destruct (IHHc Hwfx HwfP0o HwfPo Hcovx Hnfdx Hfafx Hsh0x Hshx)
      as [HwfQ [HshQ [HprovQ _]]].
    apply (consis_close_output_wf HwfQ HshQ HprovQ).
    + clear; fsetdec.
    + pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0 (pskl_var_f α)) as Hu0.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f α)) as Hu1.
      simpl in Hu0, Hu1 |- *. clear - Hu0 Hu1. fsetdec.
    + intros Hg _; inversion Hg.
  - (* C-ForallSyn : subject opened (α to Δ2), univ_ghost input kept *)
    simpl in Hsh0, Hsh.
    assert (HαP0 : α `notin` ftvar_in_pskl P0) by (clear - H; fsetdec).
    assert (HαP : α `notin` ftvar_in_pskl P) by (clear - H; fsetdec).
    assert (HαΘ0 : α `notin` dom Θ0)
      by (pose proof (dom_subset_ftvar_in_aenv Θ0); clear - H H0; fsetdec).
    assert (Hwfx : {{ ⊢ ((α ~ abind_tvar) ++ Θ0) }}a)
      by (apply a_wf_aenv__tvar; [ exact HαΘ0 | exact Hwf ]).
    assert (HwfP0x : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ (pskl_univ_ghost P0) }}a).
    { eapply a_wf_pskl_delta_mono;
        [ apply (a_wf_pskl_reassoc HwfP0 α) | clear; fsetdec ]. }
    assert (HwfPo : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ
                      (open_pskl_wrt_pskl P (pskl_var_f α)) }}a)
      by (apply a_wf_pskl_all_syn_open_tvar;
            [ exact HwfP | clear - HαΘ0 HαP; fsetdec ]).
    destruct (@delta_inv_open_tvar (Δ1 `union` Δ2) (Δ1 `union` add α Δ2) α Θ0
                ltac:(auto) ltac:(auto) ltac:(clear; fsetdec) Hcov
                ltac:(auto) ltac:(auto))
      as (Hcovx & Hnfdx & Hfafx).
    assert (Hsh0x : (Δ1 `union` add α Δ2) ∩
                    pskl_shielded_ftv (pskl_univ_ghost P0) [=] empty)
      by (simpl; clear - Hsh0 HαP0; fsetdec).
    assert (Hshx : (Δ1 `union` add α Δ2) ∩
                    pskl_shielded_ftv (open_pskl_wrt_pskl P (pskl_var_f α)) [=] empty)
      by (apply (pskl_shielded_open_disjoint HwfP HαΘ0 HαP Hsh); clear; fsetdec).
    destruct (IHHc Hwfx HwfP0x HwfPo Hcovx Hnfdx Hfafx Hsh0x Hshx)
      as [HwfQ [HshQ [HprovQ _]]].
    apply (consis_close_output_wf HwfQ HshQ HprovQ).
    + clear; fsetdec.
    + pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f α)) as Hu1.
      simpl in Hu1 |- *. clear - Hu1. fsetdec.
    + intros _ Hg; inversion Hg.
  - (* C-UnivGhost : ⊤P ∼ ⊤P0 → ⊤Q *)
    inversion HwfP0 as [ | | | | | Θz Δz P0z Hg0 Hwb0 ]; subst.
    inversion HwfP as [ | | | | | Θz Δz Pz Hgs Hwbs ]; subst.
    rewrite aenv_minus_empty in Hwb0, Hwbs.
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
    { apply a_wf_pskl__univ_ghost;
        [ apply HgQ; assumption | rewrite aenv_minus_empty; exact HwfQ ]. }
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
    assert (HαΘ0 : α `notin` dom Θ0)
      by (pose proof (dom_subset_ftvar_in_aenv Θ0); clear - H H0; fsetdec).
    assert (Hwfx : {{ ⊢ ((α ~ abind_tvar) ++ Θ0) }}a)
      by (apply a_wf_aenv__tvar; [ exact HαΘ0 | exact Hwf ]).
    assert (HwfP0o : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ
                       (open_pskl_wrt_pskl P0 (pskl_var_f α)) }}a)
      by (apply a_wf_pskl_all_syn_open_tvar;
            [ exact HwfP0 | clear - HαΘ0 HαP0; fsetdec ]).
    assert (HwfPx : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ (pskl_univ_ghost P) }}a).
    { eapply a_wf_pskl_delta_mono;
        [ apply (a_wf_pskl_reassoc HwfP α) | clear; fsetdec ]. }
    destruct (@delta_inv_open_tvar (Δ1 `union` Δ2) (add α Δ1 `union` Δ2) α Θ0
                ltac:(auto) ltac:(auto) ltac:(clear; fsetdec) Hcov
                ltac:(auto) ltac:(auto))
      as (Hcovx & Hnfdx & Hfafx).
    assert (Hsh0x : (add α Δ1 `union` Δ2) ∩
                    pskl_shielded_ftv (open_pskl_wrt_pskl P0 (pskl_var_f α)) [=] empty)
      by (apply (pskl_shielded_open_disjoint HwfP0 HαΘ0 HαP0 Hsh0); clear; fsetdec).
    assert (Hshx : (add α Δ1 `union` Δ2) ∩
                   pskl_shielded_ftv (pskl_univ_ghost P) [=] empty)
      by (simpl; clear - Hsh HαP; fsetdec).
    destruct (IHHc Hwfx HwfP0o HwfPx Hcovx Hnfdx Hfafx Hsh0x Hshx)
      as [HwfQ [HshQ [HprovQ _]]].
    apply (consis_close_output_wf HwfQ HshQ HprovQ).
    + clear; fsetdec.
    + pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0 (pskl_var_f α)) as Hu0.
      simpl in Hu0 |- *. clear - Hu0. fsetdec.
    + intros Hg _; inversion Hg.
  - (* C-UnivGhost2 : subject's ⊤ stripped against a guarded P0 *)
    inversion HwfP as [ | | | | | Θz Δz Pz Hgs Hwbs ]; subst.
    rewrite aenv_minus_empty in Hwbs.
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
    { inversion HwfP as [ | Θz Δz αz Hd | | | | ]; subst; exact Hd. }
    pose proof a_assign_unify_consis_sound as [_ [Hus _]].
    destruct (Hus _ _ _ _ H Hwf) as [Hle [Hwf1 _]].
    split.
    { apply a_wf_pskl__var.
      eapply a_isub_binds_tvarish; [ exact Hle | exact Hbα ]. }
    split; [ simpl; clear; fsetdec | ].
    split; [ intros α0 Hα0 Hft; simpl in Hft; simpl; clear - Hft; fsetdec | ].
    intros _ _; apply guarded_pskl__var.
  - (* C-FlexL : assign, output the subject variable *)
    assert (Hbα : a_binds_tvar α Θ0).
    { inversion HwfP as [ | Θz Δz αz Hd | | | | ]; subst; exact Hd. }
    pose proof a_assign_unify_consis_sound as [Has _].
    match goal with
    | Ha : {{ _ ⊲[ _ ] _ ≔ _ ⊣ _ }}a |- _ =>
        destruct (Has _ _ _ _ _ Ha (a_decls__nil) Hwf HwfP0)
          as [Hle [Hwf1 _]]
    end.
    split.
    { apply a_wf_pskl__var.
      eapply a_isub_binds_tvarish; [ exact Hle | exact Hbα ]. }
    split; [ simpl; clear; fsetdec | ].
    split; [ intros α0 Hα0 Hft; simpl in Hft; simpl; clear - Hft; fsetdec | ].
    intros _ _; apply guarded_pskl__var.
  - (* C-FlexR : assign the counterpart's variable *)
    assert (Hbα : a_binds_tvar α Θ0).
    { inversion HwfP0 as [ | Θz Δz αz Hd | | | | ]; subst; exact Hd. }
    pose proof a_assign_unify_consis_sound as [Has _].
    match goal with
    | Ha : {{ _ ⊲[ _ ] _ ≔ _ ⊣ _ }}a |- _ =>
        destruct (Has _ _ _ _ _ Ha (a_decls__nil) Hwf HwfP)
          as [Hle [Hwf1 _]]
    end.
    split.
    { apply a_wf_pskl__var.
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
    rewrite aenv_minus_empty in Hwb0.
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

(** The output of a flexible walk that SKIPS a mid entry [c ~ b] carries
    over to [(c ~ b) ++ Θ1], given the entry kind's cons lemma ([Hcons]) and
    well-formedness rule ([Hwfc]). *)
Lemma flex_owf_concl_cons : forall Θ0 Θ1 Ξ c (b : abind) Q,
  a_decls Ξ ->
  (Θ0 ⊴ Θ1 -> ((c ~ b) ++ Θ0) ⊴ ((c ~ b) ++ Θ1)) ->
  (Θ0 ⊴ Θ1 -> {{ ⊢ Θ1 }}a -> {{ ⊢ ((c ~ b) ++ Θ1) }}a) ->
  (Ξ ++ Θ0) ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\ {{ Θ1 ⨟ empty ⊢ₚₛ Q }}a ->
  (Ξ ++ (c ~ b) ++ Θ0) ⊴ ((c ~ b) ++ Θ1) /\ {{ ⊢ ((c ~ b) ++ Θ1) }}a /\
  {{ ((c ~ b) ++ Θ1) ⨟ empty ⊢ₚₛ Q }}a.
Proof.
  intros * Hdecl Hcons Hwfc [Hle [Hwf1 HwfQ]].
  assert (Hle0 : Θ0 ⊴ Θ1) by (eapply a_isub_strengthen_decls_src; eauto).
  split; [ apply a_isub_prepend_decls_src_cons; assumption | ].
  split; [ apply Hwfc; assumption | ].
  eapply a_wf_pskl_weaken; [ | exact HwfQ ].
  intros y b0 Hb; unfold binds; right; exact Hb.
Qed.

Lemma a_sub_output_wf_bundle :
  (forall NM M P0 Θ0 P P' Θ1,
     a_sub NM M P0 Θ0 P P' Θ1 ->
     sub_owf_concl NM M P0 Θ0 P P' Θ1) /\
  (forall NM M P0 Θ0 Ξ α Q Θ1,
     a_sub_flex NM M P0 Θ0 Ξ α Q Θ1 ->
     sub_flex_owf_concl NM M P0 Θ0 Ξ α Q Θ1).
Proof.
  apply a_sub_sub_flex_tm_mutind;
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
    apply a_wf_pskl__univ_ghost;
      [ exact Hg | rewrite aenv_minus_empty; exact HwfP ].
  - (* FlexMono : hand to the walk at the empty pending suffix *)
    intros NM M P0 Θ0 Θ1 α Q Hf IHf Hwf HwfP0 HwfP.
    assert (Hbα : a_binds_tvar α Θ0).
    { inversion HwfP as [ | Θz Δz αz Hd | | | | ]; subst; exact Hd. }
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
    { assert (HwfP' : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ (pskl_all_syn P) }}a)
        by (eapply a_wf_pskl_weaken; [ exact Hmono | exact HwfP ]).
      inversion HwfP' as [ | | | Lb Θb Δb Pb Hbody | | ]; subst.
      apply a_wf_pskl_open with (L := Lb); [ exact Hbody | exact HwfP1 ]. }
    destruct (IHs HwfΞΘ HwfP0' HwfSo) as [Hle [Hwf1 HwfQ]].
    split; [ eapply a_isub_strengthen_decls_src; eauto | ].
    split; [ exact Hwf1 | exact HwfQ ].
  - (* Ghost (SK) : output = the check-against, context unchanged *)
    intros M Θ0 P0 Hmghost Hwf HwfP0 HwfP.
    split; [ apply a_isub_refl; exact Hwf | ].
    split; [ exact Hwf | exact HwfP0 ].
  - (* UnivGhostL (SK) : strip the subject's ⊤ *)
    intros M Θ0 Θ1 P0 P Q Hne Hs IHs Hwf HwfP0 HwfP.
    inversion HwfP as [ | | | | | Θz Δz Pz Hgs Hwbs ]; subst.
    rewrite aenv_minus_empty in Hwbs.
    exact (IHs Hwf HwfP0 Hwbs).
  - (* Flex-Solve : deposit α̂0 ≔ α̂→β̂ and recurse on the arrow *)
    intros NM M P0 Θ0 Θ1 Ξ α0 α β Q Hne Hαf Hβf Hprem IH Hwf Hdecl HwfP0 Hαb.
    set (τab := ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)).
    set (Θmid := (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0).
    set (Θ' := Ξ ++ (α0 ~ abind_flex_mono_def τab) ++ Θmid).
    destruct (@a_flex_arrow_context Ξ Θ0 α0 α β
                Hwf Hdecl Hne Hαf Hβf) as [HwfΘ' Hlift].
    destruct (IH HwfΘ'
                ltac:(eapply a_wf_pskl_isub; [ exact HwfP0 | exact Hlift ])
                ltac:(apply a_wf_pskl__arrow; apply a_wf_pskl__var;
                        right; left;
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
    assert (HwfΞΘ0 : {{ ⊢ (Ξ ++ Θ0) }}a)
      by (eapply a_wf_aenv_strip_mid; eauto).

    assert (HwfP0' : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ
              subst_pskl_in_pskl (ptyp_to_pskl τ) β P0 }}a).
    { eapply a_wf_pskl_subst_mid_def; [ exact Hwf | exact HwfP0 ]. }
    assert (Hwfvarsub : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ
              subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α) }}a).
    { eapply a_wf_pskl_subst_mid_def; [ exact Hwf | apply a_wf_pskl__var; exact Hαb ]. }
    destruct (IH HwfΞΘ0 HwfP0' Hwfvarsub) as [Hle [Hwf1 HwfQ]].
    assert (Hle0 : Θ0 ⊴ Θ1)
      by (eapply a_isub_strengthen_decls_src; eauto).
    split.
    { apply (a_isub_prepend_decls_src_cons Hdecl Hle). intros _.
      apply a_isub_cons_flex_def; [ exact Hle0 | apply mono_ptyp_lc; exact Hm ]. }
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
    apply flex_owf_concl_cons.
    + exact Hdecl.
    + apply a_isub_cons_flex.
    + intros _ Hwf1. apply a_wf_aenv__flex; assumption.
    + apply IH.
      * eapply a_wf_aenv_strip_mid; eauto.
      * exact Hdecl.
      * eapply a_wf_pskl_strip_mid; eauto.
      * exact (a_binds_tvar_strip_mid_neq Hne Hαb).
  - (* Flex-SkipRigid *)
    intros NM M P0 Θ0 Θ1 Ξ α β Q Hne Hni Hβ1 Hprem IH Hwf Hdecl HwfP0 Hαb.
    apply flex_owf_concl_cons.
    + exact Hdecl.
    + apply a_isub_cons_tvar.
    + intros _ Hwf1. apply a_wf_aenv__tvar; assumption.
    + apply IH.
      * eapply a_wf_aenv_strip_mid; eauto.
      * exact Hdecl.
      * eapply a_wf_pskl_strip_mid; eauto.
      * exact (a_binds_tvar_strip_mid_neq Hne Hαb).
  - (* Flex-SkipTmVar (type entry) *)
    intros NM M P0 Θ0 Θ1 Ξ α x Apay Q Hxout Hprem IH Hwf Hdecl HwfP0 Hαb.
    assert (HwfT : {{ ⊢ ((x ~ abind_var_typ Apay) ++ Θ0) }}a)
      by (eapply a_wf_aenv_strip_prefix; exact Hwf).
    apply a_wf_aenv_var_typ_inv in HwfT.
    destruct HwfT as [_ [HwfQ0 _]].
    apply flex_owf_concl_cons.
    + exact Hdecl.
    + intros Hle0. apply a_isub_cons_var_typ.
      * exact Hle0.
      * eapply a_wf_ptyp_lc; exact HwfQ0.
    + intros Hle0 Hwf1. apply a_wf_aenv__var_typ.
      * exact Hxout.
      * eapply a_wf_ptyp_isub; [ exact HwfQ0 | exact Hle0 ].
      * exact Hwf1.
    + apply IH.
      * eapply a_wf_aenv_strip_mid; eauto.
      * exact Hdecl.
      * eapply a_wf_pskl_strip_mid; [ exact HwfP0 | ].
        eapply a_wf_pskl_tm_entry_fresh; [ exact Hwf | exact I | exact HwfP0 ].
      * exact (a_binds_tvar_strip_mid_tm Hαb I).
  - (* Flex-SkipTmVar (skeleton entry) *)
    intros NM M P0 Θ0 Θ1 Ξ α x Qpay Q Hxout Hprem IH Hwf Hdecl HwfP0 Hαb.
    assert (HwfT : {{ ⊢ ((x ~ abind_var_skl Qpay) ++ Θ0) }}a)
      by (eapply a_wf_aenv_strip_prefix; exact Hwf).
    apply a_wf_aenv_var_skl_inv in HwfT.
    destruct HwfT as [_ [HscQ0 _]].
    apply flex_owf_concl_cons.
    + exact Hdecl.
    + intros Hle0. apply a_isub_cons_var_skl.
      * exact Hle0.
      * eapply a_wf_pskl_lc; eauto.
    + intros Hle0 Hwf1. apply a_wf_aenv__var.
      * exact Hxout.
      * eapply a_wf_pskl_isub; [ exact HscQ0 | exact Hle0 ].
      * exact Hwf1.
    + apply IH.
      * eapply a_wf_aenv_strip_mid; eauto.
      * exact Hdecl.
      * eapply a_wf_pskl_strip_mid; [ exact HwfP0 | ].
        eapply a_wf_pskl_tm_entry_fresh; [ exact Hwf | exact I | exact HwfP0 ].
      * exact (a_binds_tvar_strip_mid_tm Hαb I).
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

(** …and the flexible walk's output, in ITS output context. *)
Corollary a_sub_flex_output_wf : forall NM M P0 Θ0 Ξ α Q Θ1,
  a_sub_flex NM M P0 Θ0 Ξ α Q Θ1 ->
  a_decls Ξ ->
  {{ ⊢ (Ξ ++ Θ0) }}a ->
  {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a ->
  a_binds_tvar α (Ξ ++ Θ0) ->
  {{ Θ1 ⨟ empty ⊢ₚₛ Q }}a.
Proof.
  intros * Hrun Hdecls Hwf HwfP0 Hαb.
  destruct ((proj2 a_sub_output_wf_bundle) _ _ _ _ _ _ _ _ Hrun
              Hwf Hdecls HwfP0 Hαb)
    as [_ [_ HwfOut]].
  exact HwfOut.
Qed.

(* ===================================================================== *)
(*  SPLITTING                                                             *)
(* ===================================================================== *)

Lemma a_split_wf : forall Θ0 P0 P Q Θ1,
  {{ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}a ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  Θ0 ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\
  {{ Θ1 ⨟ empty ⊢ₚₛ P }}a /\ {{ Θ1 ⨟ empty ⊢ₚₛ Q }}a.
Proof.
  intros Θ0 P0 P Q Θ1 Hs Hwf HwfP0; inversion Hs; subst.
  - (* arrow *)
    inversion HwfP0; subst.
    split; [ apply a_isub_refl; exact Hwf | ].
    split; [ exact Hwf | ]. split; assumption.
  - (* ghost *)
    split; [ apply a_isub_refl; exact Hwf | ].
    split; [ exact Hwf | ]. split; apply a_wf_pskl__ghost.
  - (* flex : the row's premise is a full consistency run *)
    match goal with
    | Hf1 : β `notin` ftvar_in_aenv Θ0,
      Hf2 : α1 `notin` add β (ftvar_in_aenv Θ0) |- _ =>
        pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds;
        assert (Hfrβ : β `notin` dom Θ0) by (clear - Hf1 Hds; fsetdec);
        assert (Hfrα1 : α1 `notin` add β (dom Θ0))
          by (clear - Hf2 Hds; fsetdec)
    end.
    assert (HwfX : {{ ⊢ ((α1 ~ abind_flex_mono)
                               ++ (β ~ abind_flex_mono) ++ Θ0) }}a).
    { apply a_wf_aenv__flex;
        [ simpl_env; repeat rewrite dom_app; simpl;
          clear - Hfrα1; fsetdec | ].
      apply a_wf_aenv__flex; [ clear - Hfrβ; fsetdec | exact Hwf ]. }
    assert (HwfArr : {{ ((α1 ~ abind_flex_mono) ++ (β ~ abind_flex_mono) ++ Θ0)
                       ⨟ empty ⊢ₚₛ (pskl_arrow (pskl_var_f β)
                                                (pskl_var_f α1)) }}a).
    { apply a_wf_pskl__arrow; apply a_wf_pskl__var; right; left;
        [ unfold binds; simpl; right; left; reflexivity
        | unfold binds; simpl; left; reflexivity ]. }
    match goal with
    | Hc : a_consis _ _ _ _ _ _ _ |- _ => inversion Hc; subst
    end.
    match goal with
    | Ha : {{ _ ⊲[ nil ] _ ≔ _ ⊣ _ }}a |- _ =>
        pose proof (a_assign_sound Ha a_decls__nil
                      ltac:(simpl_env; exact HwfX)
                      ltac:(simpl_env; exact HwfArr)) as [HleX _];
        pose proof (a_assign_preserves_wf Ha a_decls__nil
                      ltac:(simpl_env; exact HwfX)
                      ltac:(simpl_env; exact HwfArr)) as Hwf1
    end.
    simpl_env in HleX.
    assert (HleX0 : Θ0 ⊴ ((α1 ~ abind_flex_mono)
                           ++ (β ~ abind_flex_mono) ++ Θ0)).
    { apply a_isub_target_weaken;
        [ apply a_isub_target_weaken;
            [ apply a_isub_refl; exact Hwf
            | apply a_suffix__cons;
                [ apply a_suffix__nil | apply a_suffix_binding__flex_mono ] ]
        | apply a_suffix__cons;
            [ apply a_suffix__nil | apply a_suffix_binding__flex_mono ] ]. }
    split; [ eapply a_isub_trans; [ exact HleX0 | exact HleX ] | ].
    split; [ exact Hwf1 | ]. split;
      [ apply a_wf_pskl__var; eapply a_isub_binds_flex;
          [ exact HleX | unfold binds; simpl; right; left; reflexivity ]
      | apply a_wf_pskl__var; eapply a_isub_binds_flex;
          [ exact HleX | unfold binds; simpl; left; reflexivity ] ].
Qed.

(* ===================================================================== *)
(*  §5  ⭐⭐ A RUN NEVER MAKES AN ATOM IT ALREADY HAD FLEXIBLE              *)
(* ===================================================================== *)

(** ⭐ The subtyping twin of [a_assign_unify_consis_dom_mono] — premise-free.
    ⚙ [ForallR] is the one row that is not immediate: its premise's output
    carries the junk suffix and the opener, and what strips them is the
    rule's own [uniq (Ξ ++ Θ0)] together with the opener's freshness. *)
Lemma a_sub_sub_flex_dom_mono :
  (forall NM M P0 Θ0 P Q Θ1, a_sub NM M P0 Θ0 P Q Θ1 ->
     dom Θ0 [<=] dom Θ1) /\
  (forall NM M P0 Θ0 Ξ α Q Θ1, a_sub_flex NM M P0 Θ0 Ξ α Q Θ1 ->
     dom (Ξ ++ Θ0) [<=] dom Θ1).
Proof.
  apply a_sub_sub_flex_tm_mutind.
  - (* Infer *) intros; clear; fsetdec.
  - (* Check *) intros Θ0 Θ1 A B Hgfa Hgfb Hga Hgb [Qc Hc].
    exact (auc_dom_mono_consis Hc).
  - (* ForallR *)
    intros α Θ0 Θ1 Ξ A B Hgf Hsuf Huq Hfr Hprem IHprem.
    assert (Hdisj : disjoint Ξ Θ0) by solve_uniq.
    unfold disjoint in Hdisj.
    rewrite dom_app in Hfr.
    simpl_env in IHprem; simpl_env.
    clear - IHprem Hdisj Hfr. fsetdec.
  - (* UnivGhostR *) intros; clear; fsetdec.
  - (* FlexMono *) intros NM M P0 Θ0 Θ1 α Q Hf IHf.
    simpl_env in IHf. exact IHf.
  - (* Arrow *) intros NM M Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc Hs IHs.
    pose proof (auc_dom_mono_consis Hc) as Hd. clear - Hd IHs. fsetdec.
  - (* ForallL *) intros α NM M P0 Θ0 Θ1 P Q Ξ P1 Hne Hgd Hfr Hex Huq Hwfp Hprem IHs.
    simpl_env in IHs. clear - IHs. fsetdec.
  - (* Ghost *) intros; clear; fsetdec.
  - (* UnivGhostL *) intros; assumption.
  (* ---------- a_sub_flex ---------- *)
  - (* Flex-Solve *) intros NM M P0 Θ0 Θ1 Ξ α0 α β Q Hne Hαf Hβf Hprem IHs.
    simpl_env in IHs; simpl_env. clear - IHs. fsetdec.
  - (* Flex-Assign *) intros NM M P0 Θ0 Θ1 Ξ α β τ Q Hβ1 Hprem IHs.
    simpl_env in IHs; simpl_env. clear - IHs. fsetdec.
  - (* Flex-Depend *) intros NM M P0 Θ0 Θ1 Ξ α β Q Hne Hin Hprem IHs.
    simpl_env in IHs; simpl_env. clear - IHs. fsetdec.
  - (* Flex-Skip *) intros NM M P0 Θ0 Θ1 Ξ α β Q Hne Hni Hβ1 Hprem IHs.
    simpl_env in IHs; simpl_env. clear - IHs. fsetdec.
  - (* Flex-SkipRigid *) intros NM M P0 Θ0 Θ1 Ξ α β Q Hne Hni Hβ1 Hprem IHs.
    simpl_env in IHs; simpl_env. clear - IHs. fsetdec.
  - (* Flex-SkipTmVar *) intros NM M P0 Θ0 Θ1 Ξ α x Apay Q Hxout Hprem IHs.
    simpl_env in IHs; simpl_env. clear - IHs. fsetdec.
  - (* Flex-SkipTmSkl *) intros NM M P0 Θ0 Θ1 Ξ α x Qpay Q Hxout Hprem IHs.
    simpl_env in IHs; simpl_env. clear - IHs. fsetdec.
Qed.
