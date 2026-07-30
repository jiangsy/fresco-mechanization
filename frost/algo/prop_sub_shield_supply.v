(** P7 TASK 0 — THE FLEX-MONO WALL'S LEAF, i.e. what supplies P6-L's
    [sub_shield] premise at P7b's Sub-ForallL
    (docs/DESIGN-completeness-subtyping.md §9.0).

    P6-L ([a_extract_complete]) carries the P6-Sv/P6-Ss repair premise
    [sub_shield Θ0 Ψa ∅ P0 ψa], which cannot be dropped — the paper's P6-Sv
    WITHOUT it is machine-checked FALSE (cex/cex_p6sv_forall_flex.v) — so P7
    must SUPPLY it.  Unfolding [sub_shield] at Δρ = ∅, the hard leaf is a RAW
    Θ0-FLEXIBLE position of [P0], where the only applicable [flex_shield] rule
    is [fsh_clean], whose [ftag ψa ∩ Ψa = ∅] together with [d_tags_skl]'s
    [Ψa ⊆ ftag ψa] forces **Ψa = ∅**: the ForallL guess must be TAG-FREE.

    THE TAG ACCOUNTING IS WHAT DELIVERS THAT, and it is short.  A tag reaches
    the CONCLUSION's Ψ only by being SOLVED — i.e. by a rule that MATCHES a
    tagged quantifier of the subject against a quantifier of the counterpart.
    Every other row either forces [Ψ = ∅] outright or passes Ψ down.  In
    particular [ad_pat_sub_g__forall_l_tagged], the ForallL row, DROPS its own
    ε (conclusion [Ψ], premise [Ψ ∪ Ψ']) — instantiating a quantifier never
    solves its tag.  So against a counterpart with NO quantifier at all — a
    [bskl_monoish] one — nothing can be solved and the tag set collapses.

    And the counterpart IS mono-ish exactly where [P0] is flexible: a
    metasubstitution's images are MONOTYPES, so [κP0] is a mono PAINT there,
    and refining from a mono paint lands mono-ish
    ([ad_refine_mono_paint_rhs_monoish], Qed, prop_look_complete.v:3033).

    ⚠️ NOTE ON THE ROUTE THAT DOES NOT WORK.  DESIGN §9.0 originally planned
    to lift the whole of [ad_pat_consis_monoish_counterpart] — "against a
    mono-ish counterpart a tag-sorted subject IS A MONO PAINT and solves no
    tags" — to [ad_pat_sub_g].  Its MONO-PAINT half is FALSE
    (cex/cex_p7_sub_monoish.v): consistency's ∀ rules demand a quantifier
    counterpart, which is why they force the subject mono, whereas subtyping's
    ForallL INSTANTIATES, so [∀^ε α. α] can face the mono-ish [β] directly.
    The TAG half below is unaffected — and it is the half the shield needs. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_extra.
Require Import src.frost.def_tags.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.ltac_utils.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo_sub.
Require Import src.frost.algo.def_decl_algo_sub_hyg.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_mono_bridge.
Require Import src.frost.algo.prop_pat_sub.
Require Import src.frost.algo.prop_look_complete.

Set Implicit Arguments.

(* ===================================================================== *)
(*  §1  [is_tskl] IS CLOSED UNDER INSTANTIATION BY A DECORATED SKELETON   *)
(*                                                                        *)
(*  [is_tskl_subst_mono] (prop_pat_sub.v:944) covers a MONOTYPE            *)
(*  replacement; the ForallL row instantiates with an arbitrary decorated  *)
(*  guess, so the induction needs the general form.  Same proof.           *)
(* ===================================================================== *)

Lemma is_tskl_subst_tskl : forall ψ ψg β,
  is_tskl ψ -> is_tskl ψg ->
  is_tskl (subst_bskl_in_uskl ψg β ψ).
Proof.
  intros ψ ψg β H Hg; induction H; cbn.
  - apply is_tskl__unit.
  - destruct_if; [ exact Hg | apply is_tskl__var ].
  - apply is_tskl__arrow; assumption.
  - apply is_tskl__all_etag with (L := L `union` singleton β).
    intros α Hα.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      [ apply H0; clear - Hα; fsetdec
      | clear - Hα; fsetdec
      | apply is_tskl_lc; exact Hg ].
  - apply is_tskl__holeg.
  - apply is_tskl__topholeg; assumption.
Qed.

Lemma is_tskl_open_tskl : forall ε ψ ψg,
  is_tskl (uskl_all_etag ε ψ) -> is_tskl ψg ->
  is_tskl (open_uskl_wrt_uskl ψ ψg).
Proof.
  intros ε ψ ψg H Hg.
  destruct (is_tskl_all_etag_inv H) as [L HL].
  pick fresh α for (L `union` ftvar_in_uskl ψ).
  rewrite (subst_bskl_in_uskl_intro α ψ ψg) by (clear - Fr; fsetdec).
  apply is_tskl_subst_tskl; [ apply HL; clear - Fr; fsetdec | exact Hg ].
Qed.

(* ===================================================================== *)
(*  §2  THE LEAF: AGAINST A MONO-ISH COUNTERPART, NO TAG IS SOLVED         *)
(*                                                                        *)
(*  Read the rows.  [__infer] / [__univ_ghost_r] / [__ghost] / [__ghostg]  *)
(*  carry [Ψ = ∅] on the rule.  [__check] and [__arrow]'s domain hand the   *)
(*  work to consistency, where [ad_pat_consis_monoish_counterpart] already  *)
(*  says it.  [__forall_r] is the ONLY row that solves a tag, and its       *)
(*  counterpart is an [all_inh] — never mono-ish.  [__forall_l_tagged]      *)
(*  DROPS its own ε and hands the IH [Ψ ∪ Ψ'], so a collapse below          *)
(*  collapses Ψ too.  Everything else is [is_tskl]-impossible: plain ◇ /    *)
(*  ∀◇ and the tag-elided [all_syn] are not decorated skeletons.           *)
(* ===================================================================== *)

Lemma ad_pat_sub_g_monoish_tag_free : forall n NM M Ψ Θ ψ Q,
  ad_pat_sub_g n NM M Ψ Θ ψ Q ->
  a_wf_aenv Θ ->
  is_tskl ψ ->
  bskl_monoish Q ->
  Ψ [=] empty.
Proof.
  intros n NM M Ψ Θ ψ Q H; induction H; intros HwfΘ Htsk Hmi.
  - (* __infer : [Ψ = ∅] on the rule *) assumption.
  - (* __check : consistency against a mono-ish counterpart solves no tag *)
    destruct (ad_pat_consis_monoish_counterpart H1 HwfΘ Htsk Hmi)
      as [HΨ _]; exact HΨ.
  - (* __forall_r : the counterpart is an inherited ∀ — not mono-ish *)
    inversion Hmi.
  - (* __univ_ghost_r : [Ψ = ∅] on the rule *) assumption.
  - (* __arrow : the domain is consistency, the codomain the IH *)
    inversion Hmi; subst.
    assert (Ht1 : is_tskl R1) by (inversion Htsk; assumption).
    assert (Ht2 : is_tskl R2) by (inversion Htsk; assumption).
    destruct (ad_pat_consis_monoish_counterpart H HwfΘ Ht1 ltac:(assumption))
      as [HΨ1 _].
    assert (HΨ2 : Ψ2 [=] empty)
      by (apply IHad_pat_sub_g; [ exact HwfΘ | exact Ht2 | assumption ]).
    clear - H1 HΨ1 HΨ2; fsetdec.
  - (* __forall_l_tagged : ForallL DROPS ε and hands the IH [Ψ ∪ Ψ'] *)
    assert (Htg : is_tskl ψ)
      by (inversion H2; assumption).
    assert (HΨ : (Ψ `union` Ψ') [=] empty).
    { apply IHad_pat_sub_g;
        [ exact HwfΘ | eapply is_tskl_open_tskl; eassumption | exact Hmi ]. }
    clear - HΨ; fsetdec.
  - (* __forall_l_untagged : the tag-elided [all_syn] is not [is_tskl] *)
    inversion Htsk.
  - (* __ghost : plain ◇ is not [is_tskl] (and [Ψ = ∅] anyway) *)
    inversion Htsk.
  - (* __ghostg : [Ψ = ∅] on the rule *) assumption.
  - (* __univ_ghost_l : plain ∀◇ is not [is_tskl] *)
    inversion Htsk.
  - (* __univ_ghost_lg : ∀◈ passes Ψ down *)
    apply IHad_pat_sub_g;
      [ exact HwfΘ | inversion Htsk; assumption | exact Hmi ].
  - (* __flex_mono : unfold the definition; a mono paint is [is_tskl] *)
    assert (Hm : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eassumption).
    apply IHad_pat_sub_g;
      [ exact HwfΘ | apply mono_ptyp_to_uskl_syn_is_tskl; exact Hm | exact Hmi ].
Qed.

Print Assumptions ad_pat_sub_g_monoish_tag_free.
