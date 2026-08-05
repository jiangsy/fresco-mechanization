(** P7 TASK 0 — THE FLEX-MONO WALL'S LEAF, i.e. what supplies P6-L's
    [sub_shield] premise at P7b's Sub-ForallL
    (docs/DESIGN-completeness-subtyping.md §9.0).

    P6-L ([a_extract_complete_gen]) carries the P6-Sv/P6-Ss repair premise
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

(** The shield, from tag-freeness alone. *)
Lemma sub_shield_tag_free : forall Θ0 Ψa α P0 R ψa,
  Ψa [=] empty ->
  ftag_in_uskl ψa [=] empty ->
  sub_shield Θ0 Ψa empty α P0 R ψa.
Proof.
  intros Θ0 Ψa α P0 R ψa HΨ Htf P0' R' Δρ' _ _ Hcl.
  assert (Hcl' : (ftvar_in_uskl ψa) ∩ Δρ' [=] empty)
    by (clear - Hcl; fsetdec).
  (* ⭕ (2026-08-05) [sub_shield] has only the guess-FIXED conjunct now, and
     it is free from cleanliness alone.  The guarded [flex_apart_walk] half
     this proof also discharged is gone from the definition. *)
  apply flex_apart_p0_clean; exact Hcl'.
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
  forall α R, sub_shield Θ0 Ψa empty α P0 R ψa.
Proof.
  intros n NM M Θ0 Θ Ψa ψa ψsubj Q P0 HwfΘ Htags Htsk Hsub Hmi α R.
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
  forall P0 α R, sub_shield Θ0 Ψa empty α P0 R ψa.
Proof.
  intros n NM M Θ0 Θ Ψa ψa ψsubj Q P0s τ HwfΘ Htags Htsk Hsub Heq Hm Href
    P0 α R.
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

Lemma ss_walk_atomic : forall A α P0 R P0' R',
  ss_walk A α P0 R P0' R' -> pskl_atomic P0 -> P0' = P0.
Proof.
  intros A α P0 R P0' R' H; induction H; intros Hat; [ reflexivity | ].
  (* only the SUBJECT-side steps survive, and each keeps P0 *)
  destruct H; try solve [ exfalso; inversion Hat ]; auto.
Qed.

(** …and the P0-only walk cannot move it either. *)
Lemma p0_walk_atomic : forall A P0 P0',
  p0_walk A P0 P0' -> pskl_atomic P0 -> P0' = P0.
Proof.
  intros A P0 P0' H; induction H; intros Hat; [ reflexivity | ].
  exfalso. destruct H; inversion Hat.
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

Lemma sub_shield_atomic : forall Θ0 Ψa α0 P0 R ψa,
  a_wf_aenv Θ0 ->
  P0 = pskl_unit \/ P0 = pskl_hole \/
  (exists α, P0 = pskl_var_f α /\ binds α abind_tvar Θ0) ->
  sub_shield Θ0 Ψa empty α0 P0 R ψa.
Proof.
  intros Θ0 Ψa α1 P0 R ψa HwfΘ0 Hshape P0' R' Δρ' Hsw _ _.
  assert (Hat : pskl_atomic P0)
    by (destruct Hshape as [-> | [-> | (α & -> & _)]];
        [ apply pat_unit | apply pat_hole | apply pat_var ]).
  rewrite (ss_walk_atomic Hsw Hat).
  (* the P0-only walk cannot move an atomic P0 *)
  intros P0'' Hp0w.
  rewrite (p0_walk_atomic Hp0w Hat).
  apply flex_apart_atomic; exact Hshape.
Qed.

Print Assumptions sub_shield_atomic.

(* ===================================================================== *)
(*  §6  THE FLEX-FREE BRANCH — [sub_shield] FOR ANY FLEX-FREE P0          *)
(*                                                                        *)
(*  DESIGN §10.6 gave [flex_apart] the base row [flex_shield] already had  *)
(*  ([fa_flexfree]), so the two guards now agree on the reading: nothing   *)
(*  to keep apart.  That closes the shield for a flex-free P0 at once,     *)
(*  UNIFORMLY in ψa and in Δρ — no tag reasoning, no shape analysis.       *)
(*                                                                        *)
(*  The only content is that flex-freedom SURVIVES both walks.  Every      *)
(*  P0-moving step takes a SUBTERM (which inherits ftv) or opens a ∀ at a  *)
(*  binder the avoid set keeps out of [dom Θ0] — and a variable outside    *)
(*  the context is bound nowhere, hence flexible nowhere.  The ψ-side      *)
(*  steps leave P0 alone.                                                 *)
(*                                                                        *)
(*  This SUBSUMES §5's [sub_shield_atomic] (unit / ◇ have no free          *)
(*  variable, and a RIGID variable is not a flexible one) and it is        *)
(*  strictly more general in Δρ; §5 is kept because it is the form stated  *)
(*  in DESIGN §9.0's residual table.                                      *)
(* ===================================================================== *)

Lemma a_flex_tvar_in_dom : forall Θ α,
  a_flex_tvar Θ α -> α `in` dom Θ.
Proof.
  intros Θ α [Hb | [τ Hb]]; eapply binds_In; eassumption.
Qed.

(** Opening at a binder OUTSIDE the context cannot create a flexible — which
    is exactly what both walks' AVOID SET delivers.  Contrast
    [pskl_flex_free_open_tvar], which puts the binder INTO the context (as a
    rigid) and is what the ForallR DESCENT uses; here the context is fixed. *)
Lemma pskl_flex_free_open_fresh : forall Θ0 P γ,
  pskl_flex_free Θ0 (pskl_all_syn P) ->
  γ `notin` dom Θ0 ->
  pskl_flex_free Θ0 (open_pskl_wrt_pskl P (pskl_var_f γ)).
Proof.
  intros Θ0 P γ H Hγ α Hα Hflex.
  pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f γ)) as Hup.
  simpl in Hup.
  destruct (α == γ) as [-> | Hne].
  - apply Hγ; apply a_flex_tvar_in_dom; exact Hflex.
  - apply (H α); [ simpl; clear - Hα Hup Hne; fsetdec | exact Hflex ].
Qed.

Lemma ss_walk_flex_free : forall Θ0 α P0 R P0' R',
  ss_walk (dom Θ0) α P0 R P0' R' ->
  pskl_flex_free Θ0 P0 ->
  pskl_flex_free Θ0 P0'.
Proof.
  intros Θ0 α P0 R P0' R' H; induction H; intros Hff; [ exact Hff | ].
  apply IHss_walk. destruct H; try exact Hff.
  - (* sss_arrow_r *)
    destruct (pskl_flex_free_arrow_inv Hff) as [_ Hf]; exact Hf.
  - (* sss_all : the binder misses [dom Θ0] *)
    apply pskl_flex_free_open_fresh; assumption.
Qed.

(** …and the same for the Δρ-CONSTANT P0-only closure, which [sub_shield] now
    carries as its own conjunct (DESIGN §14.3). *)
Lemma p0_walk_flex_free : forall Θ0 P0 P0',
  p0_walk (dom Θ0) P0 P0' ->
  pskl_flex_free Θ0 P0 ->
  pskl_flex_free Θ0 P0'.
Proof.
  intros Θ0 P0 P0' H; induction H; intros Hff; [ exact Hff | ].
  apply IHp0_walk. destruct H.
  - destruct (pskl_flex_free_arrow_inv Hff) as [Hf _]; exact Hf.
  - destruct (pskl_flex_free_arrow_inv Hff) as [_ Hf]; exact Hf.
  - (* the binder misses [dom Θ0] *)
    apply pskl_flex_free_open_fresh; assumption.
  - apply pskl_flex_free_tophole_inv; exact Hff.
Qed.

Lemma flex_apart_p0_flex_free : forall Θ0 Δρ P0 ψa,
  pskl_flex_free Θ0 P0 ->
  flex_apart_p0 Θ0 Δρ P0 ψa.
Proof.
  intros Θ0 Δρ P0 ψa Hff P0' Hw.
  apply fa_flexfree; eapply p0_walk_flex_free; eassumption.
Qed.

(** The flex-free supply, uniformly in ψa AND in Δρ. *)
Theorem sub_shield_flex_free : forall Θ0 Ψa Δρ α P0 R ψa,
  pskl_flex_free Θ0 P0 ->
  sub_shield Θ0 Ψa Δρ α P0 R ψa.
Proof.
  intros Θ0 Ψa Δρ α P0 R ψa Hff P0' R' Δρ' Hsw _ _.
  assert (Hff' : pskl_flex_free Θ0 P0')
    by (eapply ss_walk_flex_free; eassumption).
  apply flex_apart_p0_flex_free; exact Hff'.
Qed.

Print Assumptions sub_shield_flex_free.

(* ===================================================================== *)
(*  §7  THE ∀-FREE BRANCH — WHY §2's [bskl_monoish] WAS TOO STRONG         *)
(*                                                                        *)
(*  §2 collapses the tag set against a MONO-ISH counterpart.  Reading the  *)
(*  rules again shows what actually does the work, and it is much less:    *)
(*  a tag LEAVES the index at exactly ONE rule in the whole system,        *)
(*  [ad_pat_consis__forall_inh_tagged] ([Ψ = ε ∪ Ψ0]), whose counterpart   *)
(*  is a [bskl_all_inh].  Every other row of consistency AND of subtyping  *)
(*  either forces [Ψ = ∅] on the rule or passes Ψ down unchanged (or, at   *)
(*  [__arrow], splits it into two branches that each do the same).  In     *)
(*  particular [__forall_l_tagged] DROPS its own ε rather than solving it, *)
(*  and [__forall_syn_tagged] — a tagged ∀ facing a SYNTHESISED ∀ — passes *)
(*  Ψ through untouched.                                                   *)
(*                                                                        *)
(*  So the real hypothesis is: the counterpart contains NO INHERITED       *)
(*  QUANTIFIER.  That is [bskl_inh_free], and it is strictly weaker than   *)
(*  [bskl_monoish] — it allows ghosts (◇, ∀◇) and synthesised ∀s, both of  *)
(*  which a refinement really can produce ([ad_refine_syn__hole] paints a  *)
(*  fill SYNTHESISED, [__tophole_fill] emits [bskl_all_syn],               *)
(*  [__tophole_keep] emits [bskl_tophole]).  It also drops the [is_tskl]   *)
(*  and [a_wf_aenv] premises §2 needed: the flexible-lookup rows land on   *)
(*  [ptyp_to_bskl_syn], a SYN painting, which is inh-free whatever the     *)
(*  monotype.                                                             *)
(*                                                                        *)
(*  And inh-freeness of the counterpart is READ OFF P0: refinement creates *)
(*  an inherited ∀ only from an inherited ∀ of its input                   *)
(*  ([ad_refine_syn__all]), and the input is [inh{κP0}], whose inherited   *)
(*  ∀s are exactly P0's ∀s (κ's images are MONOTYPES).  Hence:             *)
(*                                                                        *)
(*      P0 has no ∀  ⟹  Q is inh-free  ⟹  Ψa = ∅  ⟹  the shield.        *)
(*                                                                        *)
(*  This is what shrinks DESIGN §9.0's residual row: the open case is no   *)
(*  longer "an ARROW P0 with a non-mono-ish counterpart" but the much      *)
(*  narrower "a P0 carrying a ∀ BELOW its head".                           *)
(* ===================================================================== *)

Fixpoint bskl_inh_free (Q : bskl) : Prop :=
  match Q with
  | bskl_unit => True
  | bskl_var_b _ => True
  | bskl_var_f _ => True
  | bskl_arrow Q1 Q2 => bskl_inh_free Q1 /\ bskl_inh_free Q2
  | bskl_all_syn Q0 => bskl_inh_free Q0
  | bskl_all_inh _ => False
  | bskl_hole => True
  | bskl_tophole Q0 => bskl_inh_free Q0
  end.

(** Opening is invisible to it — the property is about CONSTRUCTORS, and a
    variable carries none. *)
Lemma bskl_inh_free_open_rec : forall Q Qa k,
  bskl_inh_free Qa ->
  (bskl_inh_free (open_bskl_wrt_bskl_rec k Qa Q) <-> bskl_inh_free Q).
Proof.
  intros Q; induction Q; intros Qa k HQa; cbn; try tauto.
  - (* var_b *)
    destruct (lt_eq_lt_dec n k) as [[? | ?] | ?]; cbn; tauto.
  - (* arrow *)
    specialize (IHQ1 Qa k HQa); specialize (IHQ2 Qa k HQa); tauto.
  (* [unit] / [var_f] / [all_inh] / [hole] are convertible identities and
     [try tauto] already closed them *)
  - (* all_syn *) apply IHQ; exact HQa.
  - (* tophole *) apply IHQ; exact HQa.
Qed.

Lemma bskl_inh_free_open : forall Q α,
  bskl_inh_free (open_bskl_wrt_bskl Q (bskl_var_f α)) <-> bskl_inh_free Q.
Proof.
  intros Q α; unfold open_bskl_wrt_bskl;
    apply bskl_inh_free_open_rec; cbn; exact I.
Qed.

(** A SYNTHESISED painting never carries an inherited ∀ — by definition of
    [pskl_to_bskl_syn], which sends [pskl_all_syn] to [bskl_all_syn]. *)
Lemma pskl_to_bskl_syn_inh_free : forall P, bskl_inh_free (pskl_to_bskl_syn P).
Proof. intros P; induction P; cbn; tauto. Qed.

Lemma ptyp_to_bskl_syn_inh_free : forall A, bskl_inh_free (ptyp_to_bskl_syn A).
Proof.
  intros A; unfold ptyp_to_bskl_syn; apply pskl_to_bskl_syn_inh_free.
Qed.

Lemma bskl_monoish_inh_free : forall Q, bskl_monoish Q -> bskl_inh_free Q.
Proof. intros Q H; induction H; cbn; tauto. Qed.

(** (A) CONSISTENCY.  [__forall_inh_tagged] is the sole tag-consuming row and
    it needs an inherited ∀; every other row forces [Ψ = ∅] or passes it on. *)
Lemma ad_pat_consis_inh_free_tag_free : forall Ψ Θ R Q,
  Ψ ⨟ Θ ⊢ₛᵃ R ∼ Q ->
  bskl_inh_free Q ->
  Ψ [=] empty.
Proof.
  intros Ψ Θ R Q H; induction H; intros Hif.
  - (* unit *) assumption.
  - (* var *) assumption.
  - (* arrow *)
    cbn in Hif; destruct Hif as [Hif1 Hif2].
    assert (He1 : Ψ1 [=] empty) by (apply IHad_pat_consis1; exact Hif1).
    assert (He2 : Ψ2 [=] empty) by (apply IHad_pat_consis2; exact Hif2).
    clear - H1 He1 He2; fsetdec.
  - (* forall_inh_tagged : THE row, and it is excluded *) cbn in Hif; tauto.
  - (* forall_inh_untagged *) cbn in Hif; tauto.
  - (* forall_syn_tagged : Ψ passes through a SYN ∀ *)
    pick fresh α for L.
    apply (H0 α ltac:(assumption)).
    apply bskl_inh_free_open; cbn in Hif; exact Hif.
  - (* forall_syn *)
    pick fresh α for L.
    apply (H0 α ltac:(assumption)).
    apply bskl_inh_free_open; cbn in Hif; exact Hif.
  - (* ghostg *) assumption.
  - (* topholeg *) apply IHad_pat_consis; cbn in Hif; exact Hif.
  - (* hole *) assumption.
  - (* tophole *) apply IHad_pat_consis; cbn in Hif; exact Hif.
  - (* tophole_inh : an inherited ∀ again *) cbn in Hif; tauto.
  - (* tophole_drop *) apply IHad_pat_consis; exact Hif.
  - (* flex_l : the counterpart does not move *) apply IHad_pat_consis; exact Hif.
  - (* flex_r : the counterpart becomes a SYN painting *)
    apply IHad_pat_consis; apply ptyp_to_bskl_syn_inh_free.
Qed.

(** (B) SUBTYPING.  Nothing here consumes a tag at all; the index only ever
    reaches consistency (at [__check] and [__arrow]'s domain) or is forced
    empty on the rule. *)
Lemma ad_pat_sub_g_inh_free_tag_free : forall n NM M Ψ Θ ψ Q,
  ad_pat_sub_g n NM M Ψ Θ ψ Q ->
  bskl_inh_free Q ->
  Ψ [=] empty.
Proof.
  intros n NM M Ψ Θ ψ Q H; induction H; intros Hif.
  - (* __infer *) assumption.
  - (* __check : hand it to consistency *)
    eapply ad_pat_consis_inh_free_tag_free; eassumption.
  - (* __forall_r : the counterpart IS an inherited ∀ *) cbn in Hif; tauto.
  - (* __univ_ghost_r *) assumption.
  - (* __arrow : the domain is consistency, the codomain the IH *)
    cbn in Hif; destruct Hif as [Hif1 Hif2].
    assert (He1 : Ψ1 [=] empty)
      by (eapply ad_pat_consis_inh_free_tag_free; eassumption).
    assert (He2 : Ψ2 [=] empty) by (apply IHad_pat_sub_g; exact Hif2).
    clear - H1 He1 He2; fsetdec.
  - (* __forall_l_tagged : ForallL DROPS ε and hands the IH [Ψ ∪ Ψ'] *)
    assert (He : (Ψ `union` Ψ') [=] empty)
      by (apply IHad_pat_sub_g; exact Hif).
    clear - He; fsetdec.
  - (* __forall_l_untagged *)
    assert (He : (Ψ `union` Ψ') [=] empty)
      by (apply IHad_pat_sub_g; exact Hif).
    clear - He; fsetdec.
  - (* __ghost *) assumption.
  - (* __ghostg *) assumption.
  - (* __univ_ghost_l *) apply IHad_pat_sub_g; exact Hif.
  - (* __univ_ghost_lg *) apply IHad_pat_sub_g; exact Hif.
  - (* __flex_mono *) apply IHad_pat_sub_g; exact Hif.
Qed.

Print Assumptions ad_pat_sub_g_inh_free_tag_free.

(** (C) REFINEMENT never CREATES an inherited ∀: [__all] is the only row that
    emits one and it demands one on the left.  The fills are painted
    SYNTHESISED, and the flexible lookups land on monotype paintings. *)
Lemma ad_refine_syn_inh_free : forall Θ Δ Q' Q,
  Θ ⨟ Δ ⊢ᵣᵃ Q' ⊳ Q ->
  bskl_inh_free Q' ->
  bskl_inh_free Q.
Proof.
  intros Θ Δ Q' Q H; induction H; intros Hif.
  - (* unit *) cbn; exact I.
  - (* var *) cbn; exact I.
  - (* arrow *)
    cbn in Hif |- *; destruct Hif as [Hif1 Hif2];
      split; [ apply IHad_refine_syn1 | apply IHad_refine_syn2 ]; assumption.
  - (* all : the INPUT is an inherited ∀ *) cbn in Hif; tauto.
  - (* hole : the fill is painted SYNTHESISED *)
    apply pskl_to_bskl_syn_inh_free.
  - (* tophole_remove *) apply IHad_refine_syn; cbn in Hif; exact Hif.
  - (* tophole_fill : the output is a SYN ∀ *)
    cbn. pick fresh α for L.
    apply (bskl_inh_free_open P α).
    apply (H0 α ltac:(assumption)); exact Hif.
  - (* tophole_keep *) cbn; apply IHad_refine_syn; cbn in Hif; exact Hif.
  - (* flex_l : a monotype PAINTING on the left *)
    apply IHad_refine_syn; apply ptyp_to_bskl_syn_inh_free.
  - (* flex_r : the output is a bare variable *) cbn; exact I.
Qed.

(* ---- reading inh-freeness of the counterpart off P0 ---- *)

Fixpoint pskl_all_free (P : pskl) : Prop :=
  match P with
  | pskl_unit => True
  | pskl_var_b _ => True
  | pskl_var_f _ => True
  | pskl_arrow P1 P2 => pskl_all_free P1 /\ pskl_all_free P2
  | pskl_all_syn _ => False
  | pskl_hole => True
  | pskl_tophole P0 => pskl_all_free P0
  end.

Lemma pskl_all_free_to_bskl_inh : forall P,
  pskl_all_free P -> bskl_inh_free (pskl_to_bskl_inh P).
Proof. intros P; induction P; cbn; tauto. Qed.

Lemma mono_ptyp_to_pskl_all_free : forall A,
  mono_ptyp A -> pskl_all_free (ptyp_to_pskl A).
Proof. intros A H; induction H; cbn; tauto. Qed.

(** A metasubstitution's images are MONOTYPES, so it cannot introduce a ∀. *)
Lemma msubst_pskl_all_free : forall Θ0 Θ κ P,
  κ ∷ Θ0 ⊑ Θ ->
  pskl_all_free P ->
  pskl_all_free (msubst_pskl κ P).
Proof.
  intros Θ0 Θ κ P Hκ; induction P; intros Hff; cbn in Hff |- *; try tauto.
  (* only [var_f] survives — the congruences are propositional *)
  - (* var_f : the image is a monotype *)
    apply mono_ptyp_to_pskl_all_free; eapply a_inc_lookup_mono; exact Hκ.
Qed.

(* ===================================================================== *)
(*  §8  P7's SUPPLY, ∀-FREE FORM                                          *)
(* ===================================================================== *)

(** The counterpart-side statement: an inh-free counterpart shields ANY P0,
    with no [is_tskl] and no wf.  §4's [sub_shield_supply_mono_counterpart]
    is the [bskl_monoish] instance. *)
Theorem sub_shield_supply_inh_free_counterpart :
  forall n NM M Θ0 Θ Ψa ψa ψsubj Q P0,
  a_tags_sort NM Ψa ψa ->
  ad_pat_sub_g n NM M Ψa Θ ψsubj Q ->
  bskl_inh_free Q ->
  forall α R, sub_shield Θ0 Ψa empty α P0 R ψa.
Proof.
  intros n NM M Θ0 Θ Ψa ψa ψsubj Q P0 Htags Hsub Hif α R.
  assert (HΨ : Ψa [=] empty)
    by (eapply ad_pat_sub_g_inh_free_tag_free; eassumption).
  apply sub_shield_tag_free; [ exact HΨ | ].
  assert (Hdt : d_tags_skl Ψa ψa) by (inversion Htags; assumption).
  assert (Heq : Ψa [=] ftag_in_uskl ψa) by (apply d_tags_skl_ftag; exact Hdt).
  clear - HΨ Heq; fsetdec.
Qed.

(** …and the P0-side form P7b's Sub-ForallL applies: a P0 with no ∀ shields
    itself, whatever ψa is, whatever the flexibles and ghosts inside it. *)
Theorem sub_shield_supply_all_free_p0 :
  forall n NM M Θ0 Θ κ Ψa ψa ψsubj Q P0,
  a_tags_sort NM Ψa ψa ->
  κ ∷ Θ0 ⊑ Θ ->
  pskl_all_free P0 ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q ->
  ad_pat_sub_g n NM M Ψa Θ ψsubj Q ->
  forall α R, sub_shield Θ0 Ψa empty α P0 R ψa.
Proof.
  intros n NM M Θ0 Θ κ Ψa ψa ψsubj Q P0 Htags Hκ Hff Href Hsub α R.
  eapply sub_shield_supply_inh_free_counterpart;
    [ exact Htags | exact Hsub | ].
  eapply ad_refine_syn_inh_free; [ exact Href | ].
  apply pskl_all_free_to_bskl_inh.
  eapply msubst_pskl_all_free; [ exact Hκ | exact Hff ].
Qed.

Print Assumptions sub_shield_supply_all_free_p0.
