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
Require Import src.frost.algo.prop_look_complete_cstr.   (* ftag_in_uskl_ptyp_to_uskl_syn *)
Require Import src.frost.algo.prop_consis_precise.   (* d_tags_skl_ftag *)
Require Import src.frost.algo.prop_look_complete_sub_var.
Require Import src.frost.algo.prop_look_complete_sub_cstr. (* sub_shield *)

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

(* ===================================================================== *)
(*  §3  A TAG-FREE GUESS SHIELDS EVERYTHING                               *)
(*                                                                        *)
(*  With [Ψa = ∅] in hand, the shield is immediate — and, notably,         *)
(*  UNIFORMLY in P0: [fsh_clean] does not look at the payload at all, so   *)
(*  no positional decomposition is needed on this branch.  What has to be  *)
(*  checked is the OTHER conjunct, [flex_apart_walk], because that one     *)
(*  quantifies over the ρ-walk and the ρ-walk can move Δρ.                 *)
(*                                                                        *)
(*  It cannot here.  [fastep_all_r] — the ONLY step that grows Δρ — needs  *)
(*  a TAGGED quantifier [∀^ε] in the guess, and tag-freeness is preserved  *)
(*  by every other step: they take subterms, or (at [fastep_flexdef_r])    *)
(*  install a mono PAINTING, which has no tags either.  So Δρ stays put    *)
(*  and every walked guess is Δρ-clean, which is [fa_clean].               *)
(* ===================================================================== *)

Lemma fa_walk_tag_free : forall A Δρ P0 ψa Δρ' P0' ψa',
  fa_walk A Δρ P0 ψa Δρ' P0' ψa' ->
  ftag_in_uskl ψa [=] empty ->
  (ftvar_in_uskl ψa) ∩ Δρ [=] empty ->
  Δρ' [=] Δρ /\ ftag_in_uskl ψa' [=] empty /\
  (ftvar_in_uskl ψa') ∩ Δρ' [=] empty.
Proof.
  intros A Δρ P0 ψa Δρ' P0' ψa' H; induction H; intros Htf Hcl.
  - (* fw_refl *)
    split; [ reflexivity | split; [ exact Htf | exact Hcl ] ].
  - (* fw_step : one step preserves the invariant, then the IH *)
    assert (Hstep : Δρ1 [=] Δρ /\ ftag_in_uskl ψ1 [=] empty /\
                    (ftvar_in_uskl ψ1) ∩ Δρ1 [=] empty).
    { destruct H; cbn in Htf, Hcl.
      - (* arrow_l *)
        split; [ reflexivity
               | split; [ clear - Htf; fsetdec | clear - Hcl; fsetdec ] ].
      - (* arrow_r *)
        split; [ reflexivity
               | split; [ clear - Htf; fsetdec | clear - Hcl; fsetdec ] ].
      - (* p0_arrow_l : the guess is untouched *)
        split; [ reflexivity | split; [ exact Htf | exact Hcl ] ].
      - (* p0_arrow_r *)
        split; [ reflexivity | split; [ exact Htf | exact Hcl ] ].
      - (* all_l : Sub-ForallR descends P0 only *)
        split; [ reflexivity | split; [ exact Htf | exact Hcl ] ].
      - (* all_r : IMPOSSIBLE — a tagged ∀ inside a tag-free guess *)
        exfalso.
        assert (Hin : ε `in` add ε (ftag_in_uskl ψ)) by (clear; fsetdec).
        rewrite Htf in Hin. clear - Hin; fsetdec.
      - (* tophole_l : the guess is untouched *)
        split; [ reflexivity | split; [ exact Htf | exact Hcl ] ].
      - (* topholeg_r *)
        split; [ reflexivity
               | split; [ clear - Htf; fsetdec | clear - Hcl; fsetdec ] ].
      - (* flexdef_r : a painting has no tags, and the step's OWN premise is
           exactly its Δρ-cleanliness *)
        split; [ reflexivity | split ];
          [ rewrite ftag_in_uskl_ptyp_to_uskl_syn; clear; fsetdec
          | assumption ]. }
    destruct Hstep as (HΔ1 & Htf1 & Hcl1).
    destruct (IHfa_walk Htf1 Hcl1) as (HΔ2 & Htf2 & Hcl2).
    split; [ clear - HΔ1 HΔ2; fsetdec | split; [ exact Htf2 | exact Hcl2 ] ].
Qed.

Lemma flex_apart_walk_tag_free : forall Θ0 Δρ P0 ψa,
  ftag_in_uskl ψa [=] empty ->
  (ftvar_in_uskl ψa) ∩ Δρ [=] empty ->
  flex_apart_walk Θ0 Δρ P0 ψa.
Proof.
  intros Θ0 Δρ P0 ψa Htf Hcl Δρ' P0' ψa' Hw.
  destruct (fa_walk_tag_free Hw Htf Hcl) as (_ & _ & Hcl').
  apply fa_clean; exact Hcl'.
Qed.

(** The shield, from tag-freeness alone. *)
Lemma sub_shield_tag_free : forall Θ0 Ψa P0 ψa,
  Ψa [=] empty ->
  ftag_in_uskl ψa [=] empty ->
  sub_shield Θ0 Ψa empty P0 ψa.
Proof.
  intros Θ0 Ψa P0 ψa HΨ Htf P0' Δρ' _ _ Hcl.
  assert (Hcl' : (ftvar_in_uskl ψa) ∩ Δρ' [=] empty)
    by (clear - Hcl; fsetdec).
  split;
    [ apply flex_apart_walk_tag_free; assumption
    | apply fsh_clean; [ exact Hcl' | clear - HΨ; fsetdec ] ].
Qed.

(* ===================================================================== *)
(*  §4  P7's SUPPLY, ON THE BRANCH THAT WAS BLOCKING                      *)
(*                                                                        *)
(*  Assemble: the counterpart is mono-ish exactly where [κP0] is a mono    *)
(*  PAINT (§2's [ad_refine_mono_paint_rhs_monoish]) — which is the case    *)
(*  for a RAW Θ0-FLEXIBLE P0, since a metasubstitution's images ARE        *)
(*  monotypes.  Then §2 collapses the tag set and §3 shields everything.   *)
(*                                                                        *)
(*  This is precisely the configuration [cex_p6sv_forall_flex.v] uses to   *)
(*  refute the paper's P6-Sv — so the premise P6-L had to carry IS         *)
(*  discharged where P7b's Sub-ForallL needs it.                          *)
(* ===================================================================== *)

Theorem sub_shield_supply_mono_counterpart :
  forall n NM M Θ0 Θ Ψa ψa ψsubj Q P0,
  a_wf_aenv Θ ->
  a_tags_sort NM Ψa ψa ->
  is_tskl ψsubj ->
  ad_pat_sub_g n NM M Ψa Θ ψsubj Q ->
  bskl_monoish Q ->
  sub_shield Θ0 Ψa empty P0 ψa.
Proof.
  intros n NM M Θ0 Θ Ψa ψa ψsubj Q P0 HwfΘ Htags Htsk Hsub Hmi.
  assert (HΨ : Ψa [=] empty)
    by (eapply ad_pat_sub_g_monoish_tag_free; eassumption).
  apply sub_shield_tag_free; [ exact HΨ | ].
  (* tag-freeness of ψa itself: [d_tags_skl] indexes ψa by its OWN tags *)
  assert (Hdt : d_tags_skl Ψa ψa) by (inversion Htags; assumption).
  assert (Heq : Ψa [=] ftag_in_uskl ψa) by (apply d_tags_skl_ftag; exact Hdt).
  clear - HΨ Heq; fsetdec.
Qed.

(** …and the form P7b's Sub-ForallL applies, with the refinement premise it
    has on hand instead of [bskl_monoish] spelled out.  [κP0] being a mono
    paint is what a RAW FLEXIBLE [P0] gives: [msubst_pskl κ (pskl_var_f α)]
    IS [ptyp_to_pskl (κ α)], and every image of a metasubstitution is a
    monotype ([a_inc_lookup_mono]). *)
Corollary sub_shield_supply_mono_p0 :
  forall n NM M Θ0 Θ Ψa ψa ψsubj Q P0s τ,
  a_wf_aenv Θ ->
  a_tags_sort NM Ψa ψa ->
  is_tskl ψsubj ->
  ad_pat_sub_g n NM M Ψa Θ ψsubj Q ->
  P0s = ptyp_to_pskl τ -> mono_ptyp τ ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh P0s) ⊳ Q ->
  forall P0, sub_shield Θ0 Ψa empty P0 ψa.
Proof.
  intros n NM M Θ0 Θ Ψa ψa ψsubj Q P0s τ HwfΘ Htags Htsk Hsub Heq Hm Href P0.
  eapply sub_shield_supply_mono_counterpart;
    [ exact HwfΘ | exact Htags | exact Htsk | exact Hsub | ].
  eapply ad_refine_mono_paint_rhs_monoish;
    [ exact HwfΘ | exact Href | | exact Hm ].
  rewrite Heq. apply ptyp_to_bskl_inh_syn_eq; exact Hm.
Qed.

Print Assumptions sub_shield_supply_mono_p0.

(* ===================================================================== *)
(*  §5  THE NON-COMPOSITE SHAPES OF P0, SO THE RESIDUAL GAP IS EXACT      *)
(*                                                                        *)
(*  Neither walk moves an ATOMIC P0: [ss_step]'s two rows need an arrow or *)
(*  a ∀, and of [fa_step]'s nine only the three ψ-SIDE ones can fire, all  *)
(*  of which leave P0 alone.  So at unit / ◇ / a RIGID variable the shield *)
(*  is one [flex_apart] constructor plus [fsh_flexfree], uniformly in ψa —  *)
(*  no tag reasoning at all.  Together with §4 (which covers a FLEXIBLE    *)
(*  variable, via [κP0] being that variable's monotype image) this leaves  *)
(*  exactly the ARROW and ∀ spine of P0 open.                             *)
(* ===================================================================== *)

Inductive pskl_atomic : pskl -> Prop :=
| pat_unit : pskl_atomic pskl_unit
| pat_var  : forall α, pskl_atomic (pskl_var_f α)
| pat_hole : pskl_atomic pskl_hole.

Lemma ss_walk_atomic : forall A P0 P0',
  ss_walk A P0 P0' -> pskl_atomic P0 -> P0' = P0.
Proof.
  intros A P0 P0' H; induction H; intros Hat; [ reflexivity | ].
  exfalso. destruct H; inversion Hat.
Qed.

Lemma fa_walk_atomic_p0 : forall A Δρ P0 ψa Δρ' P0' ψa',
  fa_walk A Δρ P0 ψa Δρ' P0' ψa' -> pskl_atomic P0 -> P0' = P0.
Proof.
  intros A Δρ P0 ψa Δρ' P0' ψa' H; induction H; intros Hat; [ reflexivity | ].
  (* only the three ψ-side steps survive, and each keeps P0 *)
  destruct H; try solve [ exfalso; inversion Hat ]; auto.
Qed.

(** [flex_apart] at an atomic P0 is one constructor, whatever the guess. *)
Lemma flex_apart_atomic : forall Θ0 Δρ P0 ψa,
  P0 = pskl_unit \/ P0 = pskl_hole \/
  (exists α, P0 = pskl_var_f α /\ binds α abind_tvar Θ0) ->
  flex_apart Θ0 Δρ P0 ψa.
Proof.
  intros Θ0 Δρ P0 ψa [-> | [-> | (α & -> & Hb)]];
    [ apply fa_unit | apply fa_hole | apply fa_var_rigid; exact Hb ].
Qed.

Lemma sub_shield_atomic : forall Θ0 Ψa P0 ψa,
  a_wf_aenv Θ0 ->
  P0 = pskl_unit \/ P0 = pskl_hole \/
  (exists α, P0 = pskl_var_f α /\ binds α abind_tvar Θ0) ->
  sub_shield Θ0 Ψa empty P0 ψa.
Proof.
  intros Θ0 Ψa P0 ψa HwfΘ0 Hshape P0' Δρ' Hsw _ _.
  assert (Hat : pskl_atomic P0)
    by (destruct Hshape as [-> | [-> | (α & -> & _)]];
        [ apply pat_unit | apply pat_hole | apply pat_var ]).
  rewrite (ss_walk_atomic Hsw Hat).
  split.
  - (* the ρ-walk cannot move an atomic P0 either *)
    intros Δρ'' P0'' ψa'' Hfw.
    rewrite (fa_walk_atomic_p0 Hfw Hat).
    apply flex_apart_atomic; exact Hshape.
  - (* an atomic P0 has no flexible free variable *)
    apply fsh_flexfree.
    intros α0 Hα0 Hflex.
    destruct Hshape as [-> | [-> | (α & -> & Hb)]];
      cbn in Hα0; try solve [ clear - Hα0; fsetdec ].
    assert (Hαe : α0 = α) by (clear - Hα0; fsetdec); subst α0.
    (* a RIGID entry is not a flexible one, by uniqueness of the context *)
    assert (Huq : uniq Θ0) by (apply a_wf_aenv_uniq; exact HwfΘ0).
    destruct Hflex as [Hb' | [τ Hb']];
      [ pose proof (binds_unique _ _ _ _ _ Hb Hb' Huq) as Hc
      | pose proof (binds_unique _ _ _ _ _ Hb Hb' Huq) as Hc ];
      discriminate Hc.
Qed.

Print Assumptions sub_shield_atomic.
