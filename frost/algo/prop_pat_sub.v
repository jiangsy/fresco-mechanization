(** STRUCTURAL KIT for [ad_pat_sub] and [ad_partial_precise]
    (docs/DESIGN-subtyping.md P2).

    The tag-context congruences and the [⊴]-stability lemmas — the exact
    mirrors of [ad_pat_consis_psi_cong] (prop_consis_sound.v) and of the
    [prop_stability.v] family: every declarative-over-Θ judgment is stable
    under information increase, because its only context-sensitive rules are
    variable visibility ([a_isub_binds_tvarish]), definition lookups
    ([a_isub_binds_flex_def]), rigid-binder extension ([a_isub_cons_tvar]),
    and skeleton well-formedness ([a_wf_pskl_isub]). *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
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

Set Implicit Arguments.

(* ===================================================================== *)
(*  §1  Tag-context congruence                                            *)
(* ===================================================================== *)

Lemma ad_pat_sub_psi_cong : forall NM M Ψ Θ R Q,
  Ψ ⨟ Θ ⊢ₛᵃ[ NM | M ] R ⊑ Q ->
  forall Ψc, Ψ [=] Ψc ->
  Ψc ⨟ Θ ⊢ₛᵃ[ NM | M ] R ⊑ Q.
Proof.
  intros NM M Ψ Θ R Q H; induction H; intros Ψc Heq.
  - (* Infer *) apply ad_pat_sub__infer; auto. fsetdec.
  - (* Check keeps the SAME Ψ on its consistency premise: transport it. *)
    apply ad_pat_sub__check; auto.
    eapply ad_pat_consis_psi_cong; eauto.
  - (* ForallR : the same Ψ threads through the binder premise *)
    eapply ad_pat_sub__forall_r with (L := L).
    intros α Hα. apply H0; auto.
  - (* UnivGhostR *) apply ad_pat_sub__univ_ghost_r; auto. fsetdec.
  - (* Arrow : sub-premise keeps its own Ψ2 *)
    eapply ad_pat_sub__arrow; eauto. fsetdec.
  - (* ForallL tagged : rec at Ψc ∪ Ψ' *)
    eapply ad_pat_sub__forall_l_tagged; eauto;
      first [ apply IHad_pat_sub; fsetdec | fsetdec ].
  - (* ForallL untagged *)
    eapply ad_pat_sub__forall_l_untagged; eauto;
      first [ apply IHad_pat_sub; fsetdec | fsetdec ].
  - (* Ghost *) apply ad_pat_sub__ghost; auto. fsetdec.
  - (* GhostG *) apply ad_pat_sub__ghostg; auto. fsetdec.
  - (* UnivGhostL *)
    apply ad_pat_sub__univ_ghost_l; [ auto | apply IHad_pat_sub; exact Heq ].
  - (* UnivGhostLG *)
    apply ad_pat_sub__univ_ghost_lg; [ auto | apply IHad_pat_sub; exact Heq ].
  - (* FlexMono *)
    eapply ad_pat_sub__flex_mono; [ eauto | apply IHad_pat_sub; exact Heq ].
Qed.

Lemma ad_partial_precise_psi_cong : forall Θ Δ Ψ P ψ,
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  forall Ψc, Ψ [=] Ψc ->
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψc ] ψ.
Proof.
  intros Θ Δ Ψ P ψ H; induction H; intros Ψc Heq;
    econstructor; eauto; fsetdec.
Qed.

(* ===================================================================== *)
(*  §2  Stability under information increase [⊴]                          *)
(* ===================================================================== *)

Lemma ad_pat_sub_isub : forall NM M Ψ Θ R Q,
  Ψ ⨟ Θ ⊢ₛᵃ[ NM | M ] R ⊑ Q ->
  forall Θ', Θ ⊴ Θ' ->
  Ψ ⨟ Θ' ⊢ₛᵃ[ NM | M ] R ⊑ Q.
Proof.
  intros NM M Ψ Θ R Q H; induction H; intros Θ' Hle.
  - apply ad_pat_sub__infer; eauto using ad_pat_consis_isub.
  - apply ad_pat_sub__check; eauto using ad_pat_consis_isub.
  - eapply ad_pat_sub__forall_r with (L := L); eauto.
    intros α Hα. eauto using a_isub_cons_tvar.
  - apply ad_pat_sub__univ_ghost_r; eauto using ad_pat_consis_isub.
  - eapply ad_pat_sub__arrow; eauto using ad_pat_consis_isub.
  - eapply ad_pat_sub__forall_l_tagged; eauto using a_wf_pskl_isub.
  - eapply ad_pat_sub__forall_l_untagged; eauto using a_wf_pskl_isub.
  - apply ad_pat_sub__ghost; eauto using a_wf_pskl_isub.
  - apply ad_pat_sub__ghostg; auto.
  - apply ad_pat_sub__univ_ghost_l; auto.
  - apply ad_pat_sub__univ_ghost_lg; auto.
  - eapply ad_pat_sub__flex_mono; eauto using a_isub_binds_flex_def.
Qed.

Lemma ad_partial_precise_isub : forall Θ Δ Ψ P ψ,
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  forall Θ', Θ ⊴ Θ' ->
  Θ' ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ.
Proof.
  intros Θ Δ Ψ P ψ H; induction H; intros Θ' Hle.
  - apply ad_ppre__unit; auto.
  - apply ad_ppre__var; auto.
    destruct H0 as [HΔ | Htv]; eauto using a_isub_binds_tvarish.
  - eapply ad_ppre__arrow; eauto.
  - eapply ad_ppre__forall with (L := L); eauto.
  - apply ad_ppre__hole; auto.
  - apply ad_ppre__tophole_remove; auto.
  - eapply ad_ppre__tophole_fill with (L := L).
    intros X HX. eauto using a_isub_cons_tvar.
  - apply ad_ppre__tophole_keep; auto.
  - eapply ad_ppre__flex_l; eauto using a_isub_binds_flex_def.
  - eapply ad_ppre__flex_r; eauto using a_isub_binds_flex_def.
Qed.

(* ===================================================================== *)
(*  §3  Context weakening (binds-monotone)                                *)
(* ===================================================================== *)

Lemma ad_pat_sub_weaken : forall NM M Ψ Θ R Q,
  Ψ ⨟ Θ ⊢ₛᵃ[ NM | M ] R ⊑ Q ->
  forall Θ',
  (forall x b, binds x b Θ -> binds x b Θ') ->
  Ψ ⨟ Θ' ⊢ₛᵃ[ NM | M ] R ⊑ Q.
Proof.
  intros NM M Ψ Θ R Q H; induction H; intros Θ' Hmon.
  - apply ad_pat_sub__infer; eauto using ad_pat_consis_weaken.
  - apply ad_pat_sub__check; eauto using ad_pat_consis_weaken.
  - eapply ad_pat_sub__forall_r with (L := L).
    intros α Hα. apply H0; auto.
    intros x b Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? ?] | Hb']; subst;
      [ unfold binds; left; reflexivity
      | unfold binds; right; apply Hmon; auto ].
  - apply ad_pat_sub__univ_ghost_r; eauto using ad_pat_consis_weaken.
  - eapply ad_pat_sub__arrow; eauto using ad_pat_consis_weaken.
  - eapply ad_pat_sub__forall_l_tagged; eauto using a_wf_pskl_weaken.
  - eapply ad_pat_sub__forall_l_untagged; eauto using a_wf_pskl_weaken.
  - apply ad_pat_sub__ghost; eauto using a_wf_pskl_weaken.
  - apply ad_pat_sub__ghostg; auto.
  - apply ad_pat_sub__univ_ghost_l; auto.
  - apply ad_pat_sub__univ_ghost_lg; auto.
  - eapply ad_pat_sub__flex_mono; eauto.
Qed.

Lemma ad_partial_precise_weaken : forall Θ Δ Ψ P ψ,
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  forall Θ',
  (forall x b, binds x b Θ -> binds x b Θ') ->
  Θ' ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ.
Proof.
  intros Θ Δ Ψ P ψ H; induction H; intros Θ' Hmon.
  - apply ad_ppre__unit; auto.
  - apply ad_ppre__var; auto.
    destruct H0 as [HΔ | [Hb | [Hb | [τ Hb]]]];
      [ left | right; left | right; right; left
      | right; right; right; exists τ ]; auto.
  - eapply ad_ppre__arrow; eauto.
  - eapply ad_ppre__forall with (L := L); eauto.
  - apply ad_ppre__hole; auto.
  - apply ad_ppre__tophole_remove; auto.
  - eapply ad_ppre__tophole_fill with (L := L).
    intros X HX. apply H0; auto.
    intros x b Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? ?] | Hb']; subst;
      [ unfold binds; left; reflexivity
      | unfold binds; right; apply Hmon; auto ].
  - apply ad_ppre__tophole_keep; auto.
  - eapply ad_ppre__flex_l; eauto.
  - eapply ad_ppre__flex_r; eauto.
Qed.

(* ===================================================================== *)
(*  §4  Suffix-strip foundations                                          *)
(*                                                                        *)
(*  ForallR's soundness case must discard the trailing suffix Ξ the body  *)
(*  run deposits above the binder.  The paper says "by context            *)
(*  strengthening for unused variables in Ξ" — but conclusion-only        *)
(*  strengthening is FALSE for ad_pat_sub (a ForallL witness may mention  *)
(*  a Ξ-variable the conclusion does not expose), exactly as the decl     *)
(*  layer discovered for d_sub (prop_syntax_directed.v NOTE).  The        *)
(*  repair is the decl route: SUBSTITUTE the stripped variable away       *)
(*  (unit for undefined flex, its own definition for defined flex),       *)
(*  rewriting witnesses too.  This section holds the substituend-generic  *)
(*  foundations; the ad_pat_consis/ad_pat_sub strip inductions build on   *)
(*  them.                                                                 *)
(* ===================================================================== *)

(** Guardedness survives substitution by a guarded, lc substituend
    (unit and monotype paintings are both guarded). *)
Lemma guarded_pskl_subst : forall P Q X,
  guarded_pskl P ->
  guarded_pskl Q ->
  lc_pskl Q ->
  guarded_pskl (subst_pskl_in_pskl Q X P).
Proof.
  intros P Q X H HgQ HlcQ. induction H; simpl.
  - apply guarded_pskl__unit.
  - match goal with |- context [ if ?e then _ else _ ] => destruct e end;
      [ exact HgQ | apply guarded_pskl__var ].
  - apply guarded_pskl__arrow; apply subst_pskl_in_pskl_lc_pskl; auto.
Qed.

(** Substituting a context (flex) entry away preserves disciplined wf:
    the mid entry is dropped; the substituend must be well-formed at the
    EMPTY Δ (so ⊤◇-bodies stay disciplined) and guarded (so ⊤◇-bodies
    stay guarded). *)
Lemma a_wf_pskl_subst_ctx : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  forall Θ1 β b Θ2 Q,
  Θ = Θ1 ++ (β ~ b) ++ Θ2 ->
  β `notin` dom (Θ1 ++ Θ2) ->
  β `notin` Δ ->
  guarded_pskl Q ->
  (Θ1 ++ Θ2) ⨟ empty ⊢ₚₛᵃ Q ->
  (Θ1 ++ Θ2) ⨟ Δ ⊢ₚₛᵃ subst_pskl_in_pskl Q β P.
Proof.
  intros Θ Δ P H; induction H;
    intros Θ1 β b0 Θ2 Q0 Heqc Hfr HfrΔ HgQ HwfQ; subst; simpl.
  - apply a_wf_pskl__unit.
  - match goal with
    | |- context [ if ?e then _ else _ ] => destruct e as [-> | Hne]
    end.
    + eapply a_wf_pskl_delta_mono; [ exact HwfQ | clear; fsetdec ].
    + apply a_wf_pskl__var.
      destruct H as [HΔ | Ht]; [ left; exact HΔ | right ].
      apply a_binds_tvar_strip_mid with (c := β) (b := b0);
        [ exact Ht
        | intro He; inversion He; subst; exact (Hne eq_refl)
        | intro He; inversion He; subst; exact (Hne eq_refl)
        | intros τ0 He; inversion He; subst; exact (Hne eq_refl) ].
  - apply a_wf_pskl__arrow; eauto.
  - apply a_wf_pskl__all
      with (L := L `union` {{β}} `union` dom (Θ1 ++ Θ2) `union` Δ).
    intros Y HY.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | intro He; subst; clear - HY; fsetdec
        | eapply a_wf_pskl_lc; eauto ].
    match goal with
    | IH : forall X, X `notin` L -> _ |- _ => eapply IH
    end; eauto.
  - apply a_wf_pskl__hole.
  - apply a_wf_pskl__tophole.
    + apply guarded_pskl_subst; auto. eapply a_wf_pskl_lc; eauto.
    + match goal with
      | IH : context [ _ ⨟ _ ⊢ₚₛᵃ subst_pskl_in_pskl _ _ _ ] |- _ =>
          eapply IH
      end; eauto; try (clear; fsetdec).
Qed.

(** Erasure commutes with the unit substitution. *)
Lemma uskl_to_pskl_subst_unit : forall S β,
  ⌊ subst_bskl_in_uskl uskl_unit β S ⌋ˢ
  = subst_pskl_in_pskl pskl_unit β ⌊ S ⌋ˢ.
Proof.
  induction S; intros; simpl; try (f_equal; auto; fail).
  repeat match goal with
         | |- context [ if ?e then _ else _ ] => destruct e
         end; try reflexivity; try contradiction.
Qed.
