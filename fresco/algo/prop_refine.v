(** Refinement metatheory over Θ: weakening, Δ-monotonicity, and the
    reflexivity lemmas feeding the appendix-B soundness induction
    (consistency-proofs.tex): inherited paintings refine themselves, and an
    unresolved skeleton is consistent with the synthesised painting of its
    own erasure (the paper's GhostR subsidiary induction). *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.prop_basic.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.algo.prop_basic.

Set Implicit Arguments.

(* ===================================================================== *)
(*  Δ-monotonicity and painting transport                                 *)
(* ===================================================================== *)

(** Changing the ∀-scope set preserves well-formedness as long as no free
    variable of the skeleton newly enters it.  Membership in [Δ] only matters
    at a [∀◇], whose body is read at [Θ∖Δ], so what has to be kept is
    exactly "[Δ] removes no free variable that [Δ0] kept".  In particular
    [Δ] may shrink freely, and may grow by variables [P] does not mention. *)
Lemma a_wf_pskl_delta_mono : forall Θ Δ0 P,
  {{ Θ ⨟ Δ0 ⊢ₚₛ P }}a ->
  forall Δ, (forall α, α `in` ftvar_in_pskl P -> α `in` Δ -> α `in` Δ0) ->
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a.
Proof.
  intros Θ Δ0 P H; induction H; intros Δ' Hagree; simpl in Hagree.
  - constructor.
  - constructor. assumption.
  - constructor; [ apply IHa_wf_pskl1 | apply IHa_wf_pskl2 ];
      intros β Hβ; apply Hagree; fsetdec.
  - apply a_wf_pskl__all with (L := L `union` ftvar_in_pskl P).
    intros α Hα. apply H0; [ fsetdec | ].
    intros β Hβ Hβin.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f α)) as Hup.
    simpl in Hup.
    destruct (β == α) as [-> | Hne]; [ fsetdec | ].
    assert (β `in` Δ) by (apply Hagree; fsetdec). fsetdec.
  - constructor.
  - constructor; [ assumption | ].
    apply (a_wf_pskl_tvar_mono_ftv H0).
    intros β Hβ Hb. apply a_binds_tvar_aenv_minus in Hb.
    apply a_binds_tvar_aenv_minus. destruct Hb as [Hb Hn]. split; [ exact Hb | ].
    intro Hin. apply Hn. apply Hagree; assumption.
Qed.

Lemma lc_pskl_to_bskl_inh : forall P,
  lc_pskl P -> lc_bskl (pskl_to_bskl_inh P).
Proof.
  intros P H; induction H; simpl; auto.
  apply lc_bskl_all_inh. intros α.
  rewrite <- pskl_to_bskl_inh_open; auto.
Qed.

Lemma guarded_pskl_to_bskl_inh : forall P,
  guarded_pskl P -> guarded_bskl (pskl_to_bskl_inh P).
Proof.
  intros P H; inversion H; subst; simpl; constructor;
    auto using lc_pskl_to_bskl_inh.
Qed.

(** The LHS of a coloured refinement is an inherited skeleton: the rows
    that do not carry [is_iskl] as a premise have a unit / variable / hole
    LHS, or ([__flex_r]) inherit it from their sub-derivation. *)
Lemma ad_refine_syn_is_iskl : forall Θ Δ Q Q',
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad ->
  is_iskl Q.
Proof.
  intros * H; induction H; try assumption; constructor.
Qed.

(** Hence the [is_iskl] premises of the structural rows are DERIVABLE from
    their sub-derivations; these constructors omit them. *)
Lemma ad_refine_syn_arrow_intro : forall Θ Δ Q1 Q2 Q3 Q4,
  {{ Θ ⨟ Δ ⊢ᵣ Q1 ⊳ Q3 }}ad ->
  {{ Θ ⨟ Δ ⊢ᵣ Q2 ⊳ Q4 }}ad ->
  {{ Θ ⨟ Δ ⊢ᵣ (bskl_arrow Q1 Q2) ⊳ (bskl_arrow Q3 Q4) }}ad.
Proof.
  intros * H1 H2. apply ad_refine_syn__arrow; auto.
  constructor; eapply ad_refine_syn_is_iskl; eassumption.
Qed.

Lemma ad_refine_syn_all_intro : forall L Θ Δ Q Q',
  (forall α, α `notin` L ->
     {{ ((α ~ abind_tvar) ++ Θ) ⨟ (add α Δ) ⊢ᵣ
       (open_bskl_wrt_bskl Q (bskl_var_f α)) ⊳
       (open_bskl_wrt_bskl Q' (bskl_var_f α)) }}ad) ->
  {{ Θ ⨟ Δ ⊢ᵣ (bskl_all_inh Q) ⊳ (bskl_all_inh Q') }}ad.
Proof.
  intros * H. apply ad_refine_syn__all with (L := L); auto.
  apply is_iskl__all with (L := L). intros α Hα.
  eapply ad_refine_syn_is_iskl; eauto.
Qed.

Lemma ad_refine_syn_tophole_remove_intro : forall Θ Δ Q Q',
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad ->
  {{ Θ ⨟ Δ ⊢ᵣ (bskl_tophole Q) ⊳ Q' }}ad.
Proof.
  intros * H. apply ad_refine_syn__tophole_remove; auto.
  constructor; eapply ad_refine_syn_is_iskl; eassumption.
Qed.

Lemma ad_refine_syn_tophole_fill_intro : forall L Θ Δ Q Q',
  (forall α, α `notin` L ->
     {{ ((α ~ abind_tvar) ++ Θ) ⨟ Δ ⊢ᵣ
       (bskl_tophole Q) ⊳ (open_bskl_wrt_bskl Q' (bskl_var_f α)) }}ad) ->
  {{ Θ ⨟ Δ ⊢ᵣ (bskl_tophole Q) ⊳ (bskl_all_syn Q') }}ad.
Proof.
  intros * H. apply ad_refine_syn__tophole_fill with (L := L); auto.
  pick fresh α for L. eapply ad_refine_syn_is_iskl; eauto.
Qed.

Lemma ad_refine_syn_tophole_keep_intro : forall Θ Δ Q Q',
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad ->
  {{ Θ ⨟ Δ ⊢ᵣ (bskl_tophole Q) ⊳ (bskl_tophole Q') }}ad.
Proof.
  intros * H. apply ad_refine_syn__tophole_keep; auto.
  constructor; eapply ad_refine_syn_is_iskl; eassumption.
Qed.

(* ===================================================================== *)
(*  Binds-monotone weakening of the refinement judgments                   *)
(* ===================================================================== *)

Lemma ad_refine_syn_weaken : forall Θ Δ Q Q',
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad ->
  forall Θ',
  (forall x b, binds x b Θ -> binds x b Θ') ->
  {{ Θ' ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad.
Proof.
  intros Θ Δ Q Q' H; induction H; intros Θ' Hmon.
  - apply ad_refine_syn__unit.
  - apply ad_refine_syn__var.
  - apply ad_refine_syn__arrow; auto.
  - eapply ad_refine_syn__all with (L := L); [ assumption | ].
    intros α Hα. apply H1; auto.
    intros x b Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? ?] | Hb']; subst;
      [ unfold binds; left; reflexivity
      | unfold binds; right; apply Hmon; auto ].
  - apply ad_refine_syn__hole; assumption.
  - apply ad_refine_syn__tophole_remove; auto.
  - eapply ad_refine_syn__tophole_fill with (L := L); [ assumption | ].
    intros α Hα. apply H1; auto.
    intros x b Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? ?] | Hb']; subst;
      [ unfold binds; left; reflexivity
      | unfold binds; right; apply Hmon; auto ].
  - apply ad_refine_syn__tophole_keep; auto.
  - eapply ad_refine_syn__flex_l; eauto.
  - eapply ad_refine_syn__flex_r; eauto.
Qed.

Lemma ad_refine_pskl_weaken : forall Θ Δ P P',
  {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ P' }}ad ->
  forall Θ',
  (forall x b, binds x b Θ -> binds x b Θ') ->
  {{ Θ' ⨟ Δ ⊢ᵣₚ P ⊳ P' }}ad.
Proof.
  intros Θ Δ P P' H; induction H; intros Θ' Hmon.
  - apply ad_refine_pskl__unit.
  - apply ad_refine_pskl__var.
  - apply ad_refine_pskl__arrow; auto.
  - eapply ad_refine_pskl__all with (L := L).
    intros α Hα. apply H0; auto.
    intros x b Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? ?] | Hb']; subst;
      [ unfold binds; left; reflexivity
      | unfold binds; right; apply Hmon; auto ].
  - apply ad_refine_pskl__hole; assumption.
  - apply ad_refine_pskl__tophole_remove; auto.
  - eapply ad_refine_pskl__tophole_fill with (L := L).
    intros α Hα. apply H0; auto.
    intros x b Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? ?] | Hb']; subst;
      [ unfold binds; left; reflexivity
      | unfold binds; right; apply Hmon; auto ].
  - apply ad_refine_pskl__tophole_keep; auto.
  - eapply ad_refine_pskl__flex_l; eauto.
  - eapply ad_refine_pskl__flex_r; eauto.
Qed.

(* ===================================================================== *)
(*  Δ-antitonicity and reflexivity of refinement                          *)
(* ===================================================================== *)

(** Refinement survives SHRINKING the ∀-scope set: [Δ] is only read by the
    [__hole] row, as [Δ ∩ ftv(fill) = ∅].  Growing [Δ] is not sound in
    general — the fill may mention the added variable. *)
Lemma ad_refine_syn_delta_mono : forall Θ Δ0 Q Q',
  {{ Θ ⨟ Δ0 ⊢ᵣ Q ⊳ Q' }}ad ->
  forall Δ, Δ [<=] Δ0 ->
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad.
Proof.
  intros Θ Δ0 Q Q' H; induction H; intros Δ' Hsub;
    eauto using ad_refine_syn.
  - apply ad_refine_syn__all with (L := L); [ assumption | ].
    intros α Hα. apply H1; auto. fsetdec.
  - apply ad_refine_syn__hole. fsetdec.
Qed.

(** A refinement whose LEFT side is ghost-free never uses the ◇ rule, the
    only rule that reads [Δ]; so it holds at every [Δ]. *)
Lemma ad_refine_syn_ghost_free_delta : forall Θ Δ0 Q P,
  {{ Θ ⨟ Δ0 ⊢ᵣ Q ⊳ P }}ad ->
  bskl_ghost_free Q ->
  forall Δ, {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ P }}ad.
Proof.
  intros Θ Δ0 Q P H; induction H; intros Hg Δ'; simpl in Hg;
    try contradiction; eauto using ad_refine_syn.
  - destruct Hg; eauto using ad_refine_syn.
  - apply ad_refine_syn__all with (L := L); [ assumption | ]. intros α Hα.
    apply H1; auto. apply bskl_ghost_free_open_rec; exact Hg.
  - eapply ad_refine_syn__flex_l; [ exact H | ].
    apply IHad_refine_syn; auto.
    unfold ptyp_to_bskl_syn. apply pskl_to_bskl_syn_ghost_free.
    apply ptyp_to_pskl_ghost_free.
Qed.

(** Refinement reads its context only through defined-flexible lookups,
    and a derivation whose sides avoid [S] only ever looks up variables
    outside [S] (an unfolded definition avoids [S] too).  So the context
    may be swapped for any [Θ'] agreeing on those lookups. *)
Lemma ad_refine_syn_defs_avoid : forall Θ Δ Qs Qt,
  {{ Θ ⨟ Δ ⊢ᵣ Qs ⊳ Qt }}ad ->
  forall S Θ',
  (forall β τ, binds β (abind_flex_mono_def τ) Θ -> β `notin` S ->
     binds β (abind_flex_mono_def τ) Θ' /\ S ∩ ftvar_in_ptyp τ [=] empty) ->
  S ∩ ftvar_in_bskl Qs [=] empty ->
  S ∩ ftvar_in_bskl Qt [=] empty ->
  {{ Θ' ⨟ Δ ⊢ᵣ Qs ⊳ Qt }}ad.
Proof.
  intros Θ Δ Qs Qt H; induction H; intros S Θ' Hm Hs Ht; simpl in Hs, Ht.
  - apply ad_refine_syn__unit.
  - apply ad_refine_syn__var.
  - apply ad_refine_syn_arrow_intro;
      [ apply (IHad_refine_syn1 S) | apply (IHad_refine_syn2 S) ];
      try assumption; clear - Hs Ht; fsetdec.
  - apply ad_refine_syn_all_intro with (L := L `union` S). intros β Hβ.
    apply (H1 β ltac:(clear - Hβ; fsetdec) S); [ | | ].
    + intros γ τ Hb Hγ. apply binds_app_1 in Hb as [Hb | Hb];
        [ apply binds_one_iff in Hb as [_ Hb]; discriminate | ].
      destruct (Hm γ τ Hb Hγ) as [Hb' Hd].
      split; [ apply binds_app_3; exact Hb' | exact Hd ].
    + pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f β))
        as Hup; simpl in Hup. clear - Hs Hup Hβ; fsetdec.
    + pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q' (bskl_var_f β))
        as Hup; simpl in Hup. clear - Ht Hup Hβ; fsetdec.
  - apply ad_refine_syn__hole; assumption.
  - apply ad_refine_syn_tophole_remove_intro; eauto.
  - apply ad_refine_syn_tophole_fill_intro with (L := L `union` S). intros β Hβ.
    apply (H1 β ltac:(clear - Hβ; fsetdec) S); [ | simpl; exact Hs | ].
    + intros γ τ Hb Hγ. apply binds_app_1 in Hb as [Hb | Hb];
        [ apply binds_one_iff in Hb as [_ Hb]; discriminate | ].
      destruct (Hm γ τ Hb Hγ) as [Hb' Hd].
      split; [ apply binds_app_3; exact Hb' | exact Hd ].
    + pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q' (bskl_var_f β))
        as Hup; simpl in Hup. clear - Ht Hup Hβ; fsetdec.
  - apply ad_refine_syn_tophole_keep_intro; eauto.
  - assert (Hα : α `notin` S)
      by (intros Hin; assert (Hx : α `in` S ∩ singleton α)
            by (clear - Hin; fsetdec);
          rewrite Hs in Hx; clear - Hx; fsetdec).
    destruct (Hm α τ H Hα) as [Hb' Hd].
    apply ad_refine_syn__flex_l with (τ := τ); [ exact Hb' | ].
    apply (IHad_refine_syn S); [ exact Hm | | exact Ht ].
    rewrite ftvar_ptyp_to_bskl_syn; exact Hd.
  - assert (Hα : α `notin` S)
      by (intros Hin; assert (Hx : α `in` S ∩ singleton α)
            by (clear - Hin; fsetdec);
          rewrite Ht in Hx; clear - Hx; fsetdec).
    destruct (Hm α τ H Hα) as [Hb' Hd].
    apply ad_refine_syn__flex_r with (τ := τ); [ exact Hb' | ].
    apply (IHad_refine_syn S); [ exact Hm | exact Hs | ].
    rewrite ftvar_ptyp_to_bskl_syn; exact Hd.
Qed.

Lemma ad_refine_pskl_delta_mono : forall Θ Δ0 P P',
  {{ Θ ⨟ Δ0 ⊢ᵣₚ P ⊳ P' }}ad ->
  forall Δ, Δ [<=] Δ0 ->
  {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ P' }}ad.
Proof.
  intros Θ Δ0 P P' H; induction H; intros Δ' Hsub;
    eauto using ad_refine_pskl.
  - apply ad_refine_pskl__all with (L := L).
    intros α Hα. apply H0; auto. fsetdec.
  - apply ad_refine_pskl__hole. fsetdec.
Qed.

(** Reflexivity needs no scoping at all: the reflexive derivation fills
    every [◇] with [◇] (so [__hole]'s side condition is vacuous) and the
    remaining rows carry no premise beyond the LHS being inherited, which
    an inherited painting is.  Hence the general form, at an arbitrary
    [Θ'] and [Δ']; the wf hypothesis only supplies local closure, so the
    induction runs on that. *)
Lemma ad_refine_syn_refl_inh_gen : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  forall Θ' Δ',
  {{ Θ' ⨟ Δ' ⊢ᵣ (pskl_to_bskl_inh P) ⊳ (pskl_to_bskl_inh P) }}ad.
Proof.
  intros Θ Δ P H.
  assert (Hlc : lc_pskl P) by (clear - H; induction H; eauto using lc_pskl).
  clear H. pose proof Hlc as Hlc0. revert Hlc0.
  induction Hlc; intros Hlc0 Θ' Δ';
    pose proof (is_iskl_pskl_to_bskl_inh _ Hlc0) as Hi;
    simpl in Hi |- *.
  - apply ad_refine_syn__unit.
  - apply ad_refine_syn__var.
  - apply ad_refine_syn__arrow; auto.
  - apply ad_refine_syn__all with (L := {}); [ exact Hi | ].
    intros α _.
    repeat rewrite <- pskl_to_bskl_inh_open. auto.
  - replace (pskl_to_bskl_inh pskl_hole)
      with (pskl_to_bskl_syn pskl_hole) at 2 by reflexivity.
    apply ad_refine_syn__hole. simpl. fsetdec.
  - apply ad_refine_syn__tophole_keep; auto.
Qed.

Lemma ad_refine_syn_refl_inh : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  {{ Θ ⨟ Δ ⊢ᵣ (pskl_to_bskl_inh P) ⊳ (pskl_to_bskl_inh P) }}ad.
Proof. intros. eapply ad_refine_syn_refl_inh_gen; eauto. Qed.

Lemma ad_refine_pskl_refl_gen : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  forall Θ' Δ', {{ Θ' ⨟ Δ' ⊢ᵣₚ P ⊳ P }}ad.
Proof.
  intros Θ Δ P H; induction H; intros Θ' Δ'; simpl.
  - apply ad_refine_pskl__unit.
  - apply ad_refine_pskl__var.
  - apply ad_refine_pskl__arrow; auto.
  - apply ad_refine_pskl__all with (L := L). auto.
  - apply ad_refine_pskl__hole. simpl. fsetdec.
  - apply ad_refine_pskl__tophole_keep. auto.
Qed.

Lemma ad_refine_pskl_refl : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ P }}ad.
Proof. intros. eapply ad_refine_pskl_refl_gen; eauto. Qed.

(** Refinement is reflexive on a monotype painting. *)
Lemma ad_refine_syn_mono_refl : forall Θ Δ τ,
  mono_ptyp τ ->
  {{ Θ ⨟ Δ ⊢ᵣ (ptyp_to_bskl_syn τ) ⊳ (ptyp_to_bskl_syn τ) }}ad.
Proof.
  intros Θ Δ τ Hm; induction Hm; simpl.
  - apply ad_refine_syn__unit.
  - apply ad_refine_syn__var.
  - apply ad_refine_syn_arrow_intro; auto.
Qed.

(* ===================================================================== *)
(*  Consistency reflexivity along the erasure (the GhostR subsidiary       *)
(*  induction of the paper's soundness proof): an unresolved skeleton is   *)
(*  consistent, with no solved tags, with the synthesised painting of its  *)
(*  own erasure.                                                          *)
(* ===================================================================== *)

Lemma ad_pat_consis_refl_erase : forall R' Θ,
  lc_uskl R' ->
  (forall α, α `in` ftvar_in_uskl R' -> a_binds_tvar α Θ) ->
  ad_pat_consis empty Θ R' (pskl_to_bskl_syn ⌊ R' ⌋ˢ).
Proof.
  intros R' Θ Hlc; revert Θ; induction Hlc; intros Θ Hvis; simpl.
  - apply ad_pat_consis__unit. fsetdec.
  - apply ad_pat_consis__var; [ fsetdec | ].
    apply Hvis. simpl. fsetdec.
  - apply ad_pat_consis__arrow with (Ψ1 := empty) (Ψ2 := empty);
      [ apply IHHlc1 | apply IHHlc2 | fsetdec ];
      intros α Hα; apply Hvis; simpl; fsetdec.
  - (* all_syn ↦ ∀ syn *)
    apply ad_pat_consis__forall_syn with (L := dom Θ).
    intros α Hα.
    rewrite <- pskl_to_bskl_syn_open.
    replace (open_pskl_wrt_pskl ⌊ R ⌋ˢ (pskl_var_f α))
      with (⌊ open_uskl_wrt_uskl R (uskl_var_f α) ⌋ˢ)
      by (unfold open_uskl_wrt_uskl, open_pskl_wrt_pskl;
          apply uskl_to_pskl_open_rec).
    apply H0.
    intros β Hβ.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper
                  R (uskl_var_f α)) as Hup.
    simpl in Hup.
    assert (HY' : β `in` (singleton α `union` ftvar_in_uskl R))
      by (clear - Hβ Hup; fsetdec).
    destruct (union_1 HY') as [HYX | HYR].
    + apply singleton_1 in HYX; subst.
      left. unfold binds; left; reflexivity.
    + apply a_binds_tvar_weaken_cons; auto.
  - (* all_tag ↦ ∀ syn (ForallSyn on a tagged head, tag unsolved) *)
    apply ad_pat_consis__forall_syn_tagged with (L := dom Θ).
    intros α Hα.
    rewrite <- pskl_to_bskl_syn_open.
    replace (open_pskl_wrt_pskl ⌊ R ⌋ˢ (pskl_var_f α))
      with (⌊ open_uskl_wrt_uskl R (uskl_var_f α) ⌋ˢ)
      by (unfold open_uskl_wrt_uskl, open_pskl_wrt_pskl;
          apply uskl_to_pskl_open_rec).
    apply H0.
    intros β Hβ.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper
                  R (uskl_var_f α)) as Hup.
    simpl in Hup.
    assert (HY' : β `in` (singleton α `union` ftvar_in_uskl R))
      by (clear - Hβ Hup; fsetdec).
    destruct (union_1 HY') as [HYX | HYR].
    + apply singleton_1 in HYX; subst.
      left. unfold binds; left; reflexivity.
    + apply a_binds_tvar_weaken_cons; auto.
  - (* hole ↦ □ : the RHS is the inherited painting of □ *)
    replace bskl_hole with (pskl_to_bskl_inh pskl_hole) by reflexivity.
    apply ad_pat_consis__hole; [ fsetdec | apply a_wf_pskl__hole ].
  - (* tophole ↦ ∀◇ *)
    apply ad_pat_consis__tophole. auto.
  - (* holeg ↦ □ *)
    apply ad_pat_consis__ghostg. fsetdec.
  - (* topholeg ↦ ∀◈ *)
    apply ad_pat_consis__topholeg. auto.
Qed.
