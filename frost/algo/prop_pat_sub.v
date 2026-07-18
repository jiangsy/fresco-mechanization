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
(*  run deposits above the binder — the paper's "context strengthening    *)
(*  for unused variables in Ξ".  The statement is TRUE, but not provable  *)
(*  by direct induction: a ForallL witness may mention a Ξ-variable the   *)
(*  conclusion does not expose, so conclusion-only freshness does not     *)
(*  propagate to the premises (the decl layer hit the same for d_sub,     *)
(*  prop_syntax_directed.v NOTE).  The inductive generalization is        *)
(*  SUBSTITUTION: strip the variable by substituting it away (unit for    *)
(*  undefined flex, its own definition for defined flex), rewriting       *)
(*  witnesses too; strengthening is then the fresh-subjects corollary.    *)
(*  This section holds the substituend-generic foundations; the           *)
(*  ad_pat_consis/ad_pat_sub strip inductions build on them.              *)
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

(** Free variables of monotype paintings. *)
Lemma ftvar_in_pskl_ptyp_to_pskl : forall τ,
  ftvar_in_pskl (ptyp_to_pskl τ) [=] ftvar_in_ptyp τ.
Proof. induction τ; simpl; fsetdec. Qed.

Lemma ftvar_in_uskl_ptyp_to_uskl_syn : forall τ,
  ftvar_in_uskl (ptyp_to_uskl_syn τ) [=] ftvar_in_ptyp τ.
Proof.
  intros. rewrite <- ptyp_to_uskl_syn_eq.
  rewrite ftvar_in_uskl_pskl. apply ftvar_in_pskl_ptyp_to_pskl.
Qed.

Lemma ftvar_in_bskl_ptyp_to_bskl_syn : forall τ,
  ftvar_in_bskl (ptyp_to_bskl_syn τ) [=] ftvar_in_ptyp τ.
Proof.
  intros. rewrite <- (ftvar_in_pskl_bskl_to_pskl (ptyp_to_bskl_syn τ)).
  unfold ptyp_to_bskl_syn. rewrite bskl_to_pskl_pskl_to_bskl_syn.
  apply ftvar_in_pskl_ptyp_to_pskl.
Qed.

(** A definition cannot live on an undefined-flex mid entry. *)
Lemma binds_mid_flex_absurd : forall Θ1 β (τ : ptyp) Θ2,
  binds β (abind_flex_mono_def τ) (Θ1 ++ (β ~ abind_flex_mono) ++ Θ2) ->
  β `notin` dom (Θ1 ++ Θ2) ->
  False.
Proof.
  intros * Hb Hfr. unfold binds in Hb.
  apply in_app_or in Hb; destruct Hb as [Hb | Hb];
    [ apply binds_In in Hb; simpl_env in *; fsetdec | ].
  apply in_app_or in Hb; destruct Hb as [Hb | Hb];
    [ | apply binds_In in Hb; simpl_env in *; fsetdec ].
  destruct Hb as [Heq | Habs]; [ inversion Heq | inversion Habs ].
Qed.

(** STRIP an undefined flexible mid entry from [ad_pat_consis] by
    substituting unit for it (witness-rewriting; see the §4 header). *)
Lemma ad_pat_consis_subst_flex : forall Ψ Θ S Q,
  Ψ ⨟ Θ ⊨ₛᵃ S ≈ Q ->
  forall Θ1 β Θ2,
  Θ = Θ1 ++ (β ~ abind_flex_mono) ++ Θ2 ->
  β `notin` dom (Θ1 ++ Θ2) ->
  (forall γ τ, binds γ (abind_flex_mono_def τ) (Θ1 ++ Θ2) ->
     β `notin` ftvar_in_ptyp τ) ->
  Ψ ⨟ (Θ1 ++ Θ2) ⊨ₛᵃ (subst_bskl_in_uskl uskl_unit β S)
                    ≈ (subst_bskl_in_bskl bskl_unit β Q).
Proof.
  intros Ψ Θ S Q H; induction H;
    intros Θ1 β Θ2 Heqc Hfr Hdefs; subst; simpl.
  - apply ad_pat_consis__unit; assumption.
  - repeat match goal with
           | |- context [ if ?e then _ else _ ] => destruct e
           end; try contradiction.
    + apply ad_pat_consis__unit; assumption.
    + apply ad_pat_consis__var; [ assumption | ].
      match goal with Hne : X <> β |- _ =>
        apply a_binds_tvar_strip_mid with (c := β) (b := abind_flex_mono);
          [ assumption
          | intro He; inversion He; subst; exact (Hne eq_refl)
          | intro He; inversion He; subst; exact (Hne eq_refl)
          | intros τ0 He; inversion He; subst; exact (Hne eq_refl) ]
      end.
  - eapply ad_pat_consis__arrow; eauto.
  - apply ad_pat_consis__forall_inh_tagged
      with (L := L `union` {{β}} `union` dom (Θ1 ++ Θ2)) (Ψ0 := Ψ0);
      [ | assumption ].
    intros X HX.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | intro He; subst; clear - HX; fsetdec | apply lc_uskl_unit ].
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      [ | intro He; subst; clear - HX; fsetdec | apply lc_bskl_unit ].
    match goal with
    | IH : forall X, X `notin` L -> forall Θ1 : list _, _ |- _ =>
        specialize (IH X ltac:(clear - HX; fsetdec)
                      ((X ~ abind_tvar) ++ Θ1) β Θ2);
        simpl_env in IH; simpl_env; apply IH
    end;
      [ reflexivity
      | clear - Hfr HX; simpl_env in *; fsetdec
      | intros γ τ Hb;
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
        [ discriminate | eauto ] ].
  - apply ad_pat_consis__forall_inh_untagged
      with (L := L `union` {{β}} `union` dom (Θ1 ++ Θ2)).
    intros X HX.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | intro He; subst; clear - HX; fsetdec | apply lc_uskl_unit ].
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      [ | intro He; subst; clear - HX; fsetdec | apply lc_bskl_unit ].
    match goal with
    | IH : forall X, X `notin` L -> forall Θ1 : list _, _ |- _ =>
        specialize (IH X ltac:(clear - HX; fsetdec)
                      ((X ~ abind_tvar) ++ Θ1) β Θ2);
        simpl_env in IH; simpl_env; apply IH
    end;
      [ reflexivity
      | clear - Hfr HX; simpl_env in *; fsetdec
      | intros γ τ Hb;
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
        [ discriminate | eauto ] ].
  - apply ad_pat_consis__forall_syn_tagged
      with (L := L `union` {{β}} `union` dom (Θ1 ++ Θ2)).
    intros X HX.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | intro He; subst; clear - HX; fsetdec | apply lc_uskl_unit ].
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      [ | intro He; subst; clear - HX; fsetdec | apply lc_bskl_unit ].
    match goal with
    | IH : forall X, X `notin` L -> forall Θ1 : list _, _ |- _ =>
        specialize (IH X ltac:(clear - HX; fsetdec)
                      ((X ~ abind_tvar) ++ Θ1) β Θ2);
        simpl_env in IH; simpl_env; apply IH
    end;
      [ reflexivity
      | clear - Hfr HX; simpl_env in *; fsetdec
      | intros γ τ Hb;
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
        [ discriminate | eauto ] ].
  - apply ad_pat_consis__forall_syn
      with (L := L `union` {{β}} `union` dom (Θ1 ++ Θ2)).
    intros X HX.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | intro He; subst; clear - HX; fsetdec | apply lc_uskl_unit ].
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      [ | intro He; subst; clear - HX; fsetdec | apply lc_bskl_unit ].
    match goal with
    | IH : forall X, X `notin` L -> forall Θ1 : list _, _ |- _ =>
        specialize (IH X ltac:(clear - HX; fsetdec)
                      ((X ~ abind_tvar) ++ Θ1) β Θ2);
        simpl_env in IH; simpl_env; apply IH
    end;
      [ reflexivity
      | clear - Hfr HX; simpl_env in *; fsetdec
      | intros γ τ Hb;
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
        [ discriminate | eauto ] ].
  - apply ad_pat_consis__ghostg; assumption.
  - apply ad_pat_consis__topholeg; eauto.
  - rewrite pskl_to_bskl_inh_subst_unit.
    apply ad_pat_consis__hole; [ assumption | ].
    eapply a_wf_pskl_subst_ctx with (b := abind_flex_mono);
      [ eassumption | reflexivity | exact Hfr | clear; fsetdec
      | apply guarded_pskl__unit | apply a_wf_pskl__unit ].
  - apply ad_pat_consis__tophole; eauto.
  - apply ad_pat_consis__tophole_inh
      with (L := L `union` {{β}} `union` dom (Θ1 ++ Θ2)).
    intros X HX.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      [ | intro He; subst; clear - HX; fsetdec | apply lc_bskl_unit ].
    match goal with
    | IH : forall X, X `notin` L -> forall Θ1 : list _, _ |- _ =>
        specialize (IH X ltac:(clear - HX; fsetdec)
                       ((X ~ abind_tvar) ++ Θ1) β Θ2);
        simpl in IH; simpl_env in IH
    end.
    match goal with
    | IH : _ -> _ -> _ -> _ ⨟ _ ⊨ₛᵃ _ ≈ _ |- _ => simpl_env; apply IH
    end;
      [ reflexivity
      | clear - Hfr HX; simpl_env in *; fsetdec
      | intros γ τ Hb;
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
        [ discriminate | eauto ] ].
  - apply ad_pat_consis__tophole_drop; eauto.
  - (* flex_l *)
    match goal with |- context [ if ?e then _ else _ ] => destruct e as [-> | Hne] end.
    + exfalso. eapply binds_mid_flex_absurd; eauto.
    + assert (Hb' : binds α (abind_flex_mono_def τ) (Θ1 ++ Θ2)).
      { eapply binds_strip_mid; eauto.
        intro He; inversion He; subst; exact (Hne eq_refl). }
      apply ad_pat_consis__flex_l with (τ := τ); [ exact Hb' | ].
      match goal with
      | IH : forall Θ1 : list _, _ |- _ =>
          specialize (IH Θ1 β Θ2 ltac:(reflexivity) Hfr Hdefs)
      end.
      rewrite subst_bskl_in_uskl_fresh_eq in *; [ auto | ].
      rewrite ftvar_in_uskl_ptyp_to_uskl_syn. eauto.
  - (* flex_r *)
    match goal with |- context [ if ?e then _ else _ ] => destruct e as [-> | Hne] end.
    + exfalso. eapply binds_mid_flex_absurd; eauto.
    + assert (Hb' : binds α (abind_flex_mono_def τ) (Θ1 ++ Θ2)).
      { eapply binds_strip_mid; eauto.
        intro He; inversion He; subst; exact (Hne eq_refl). }
      apply ad_pat_consis__flex_r with (τ := τ); [ exact Hb' | ].
      match goal with
      | IH : forall Θ1 : list _, _ |- _ =>
          specialize (IH Θ1 β Θ2 ltac:(reflexivity) Hfr Hdefs)
      end.
      rewrite subst_bskl_in_bskl_fresh_eq in *; [ auto | ].
      rewrite ftvar_in_bskl_ptyp_to_bskl_syn. eauto.
Qed.

(** Monotype paintings are locally closed in every sort. *)
Lemma mono_ptyp_to_uskl_syn_lc : forall τ,
  mono_ptyp τ -> lc_uskl (ptyp_to_uskl_syn τ).
Proof.
  induction 1; simpl;
    [ apply lc_uskl_unit | apply lc_uskl_var_f | apply lc_uskl_arrow; auto ].
Qed.

Lemma mono_ptyp_to_bskl_syn_lc : forall τ,
  mono_ptyp τ -> lc_bskl (ptyp_to_bskl_syn τ).
Proof.
  induction 1; simpl;
    [ apply lc_bskl_unit | apply lc_bskl_var_f | apply lc_bskl_arrow; auto ].
Qed.

Lemma mono_ptyp_lc : forall τ, mono_ptyp τ -> lc_ptyp τ.
Proof.
  induction 1; [ apply lc_ptyp_unit | apply lc_ptyp_var_f
               | apply lc_ptyp_arrow; auto ].
Qed.

(** The inh painting commutes with substitution by a monotype: syn and
    inh paintings agree on monotypes ([ptyp_to_bskl_inh_syn_eq]). *)
Lemma pskl_to_bskl_inh_subst_mono : forall P τ X,
  mono_ptyp τ ->
  subst_bskl_in_bskl (ptyp_to_bskl_syn τ) X (pskl_to_bskl_inh P)
  = pskl_to_bskl_inh (subst_pskl_in_pskl (ptyp_to_pskl τ) X P).
Proof.
  induction P; intros τ X Hm; simpl; try reflexivity;
    try (rewrite IHP1; auto; rewrite IHP2; auto; reflexivity);
    try (rewrite IHP; auto; reflexivity).
  repeat match goal with |- context [ if ?e then _ else _ ] => destruct e end;
    try contradiction; try reflexivity.
  symmetry. apply ptyp_to_bskl_inh_syn_eq; assumption.
Qed.

(** The unique definition on a defined mid entry. *)
Lemma binds_mid_def_eq : forall Θ1 β (τ τ0 : ptyp) Θ2,
  binds β (abind_flex_mono_def τ)
    (Θ1 ++ (β ~ abind_flex_mono_def τ0) ++ Θ2) ->
  β `notin` dom (Θ1 ++ Θ2) ->
  τ = τ0.
Proof.
  intros * Hb Hfr. unfold binds in Hb.
  apply in_app_or in Hb; destruct Hb as [Hb | Hb];
    [ apply binds_In in Hb; simpl_env in *; exfalso; fsetdec | ].
  apply in_app_or in Hb; destruct Hb as [Hb | Hb];
    [ | apply binds_In in Hb; simpl_env in *; exfalso; fsetdec ].
  destruct Hb as [Heq | Habs]; [ inversion Heq; reflexivity | inversion Habs ].
Qed.

(** STRIP a DEFINED flexible mid entry from [ad_pat_consis] by
    substituting its definition's paintings for it (msubst-style collapse;
    the lookup rules at the stripped variable dissolve into their premise). *)
Lemma ad_pat_consis_subst_flex_def : forall Ψ Θ S Q,
  Ψ ⨟ Θ ⊨ₛᵃ S ≈ Q ->
  forall Θ1 β τ0 Θ2,
  Θ = Θ1 ++ (β ~ abind_flex_mono_def τ0) ++ Θ2 ->
  β `notin` dom (Θ1 ++ Θ2) ->
  mono_ptyp τ0 ->
  β `notin` ftvar_in_ptyp τ0 ->
  (forall X, X `in` ftvar_in_ptyp τ0 -> a_binds_tvar X (Θ1 ++ Θ2)) ->
  (forall γ τ, binds γ (abind_flex_mono_def τ) (Θ1 ++ Θ2) ->
     β `notin` ftvar_in_ptyp τ) ->
  Ψ ⨟ (Θ1 ++ Θ2) ⊨ₛᵃ (subst_bskl_in_uskl (ptyp_to_uskl_syn τ0) β S)
                    ≈ (subst_bskl_in_bskl (ptyp_to_bskl_syn τ0) β Q).
Proof.
  intros Ψ Θ S Q H; induction H;
    intros Θ1 β τ0 Θ2 Heqc Hfr Hm Hfrτ Hvis Hdefs; subst; simpl.
  - apply ad_pat_consis__unit; assumption.
  - repeat match goal with
           | |- context [ if ?e then _ else _ ] => destruct e
           end; try contradiction.
    + eapply ad_pat_consis_psi_cong;
        [ apply consis_mono_refl; assumption
        | match goal with HΨ : _ [=] empty |- _ => clear - HΨ; fsetdec end ].
    + apply ad_pat_consis__var; [ assumption | ].
      match goal with Hne : X <> β |- _ =>
        eapply a_binds_tvar_strip_mid;
          [ eassumption
          | intro He; inversion He; subst; exact (Hne eq_refl)
          | intro He; inversion He; subst; exact (Hne eq_refl)
          | intros τ1 He; inversion He; subst; exact (Hne eq_refl) ]
      end.
  - eapply ad_pat_consis__arrow; eauto.
  - apply ad_pat_consis__forall_inh_tagged
      with (L := L `union` {{β}} `union` dom (Θ1 ++ Θ2)) (Ψ0 := Ψ0);
      [ | assumption ].
    intros X HX.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | intro He; subst; clear - HX; fsetdec
        | apply mono_ptyp_to_uskl_syn_lc; assumption ].
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      [ | intro He; subst; clear - HX; fsetdec
        | apply mono_ptyp_to_bskl_syn_lc; assumption ].
    match goal with
    | IH : forall X, X `notin` L -> forall Θ1 : list _, _ |- _ =>
        specialize (IH X ltac:(clear - HX; fsetdec)
                      ((X ~ abind_tvar) ++ Θ1) β τ0 Θ2);
        simpl_env in IH; simpl_env; apply IH
    end;
      [ reflexivity
      | clear - Hfr HX; simpl_env in *; fsetdec
      | assumption
      | assumption
      | intros Y HY; apply a_binds_tvar_weaken_cons; auto
      | intros γ τ Hb;
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
        [ discriminate | eauto ] ].
  - apply ad_pat_consis__forall_inh_untagged
      with (L := L `union` {{β}} `union` dom (Θ1 ++ Θ2)).
    intros X HX.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | intro He; subst; clear - HX; fsetdec
        | apply mono_ptyp_to_uskl_syn_lc; assumption ].
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      [ | intro He; subst; clear - HX; fsetdec
        | apply mono_ptyp_to_bskl_syn_lc; assumption ].
    match goal with
    | IH : forall X, X `notin` L -> forall Θ1 : list _, _ |- _ =>
        specialize (IH X ltac:(clear - HX; fsetdec)
                      ((X ~ abind_tvar) ++ Θ1) β τ0 Θ2);
        simpl_env in IH; simpl_env; apply IH
    end;
      [ reflexivity
      | clear - Hfr HX; simpl_env in *; fsetdec
      | assumption
      | assumption
      | intros Y HY; apply a_binds_tvar_weaken_cons; auto
      | intros γ τ Hb;
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
        [ discriminate | eauto ] ].
  - apply ad_pat_consis__forall_syn_tagged
      with (L := L `union` {{β}} `union` dom (Θ1 ++ Θ2)).
    intros X HX.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | intro He; subst; clear - HX; fsetdec
        | apply mono_ptyp_to_uskl_syn_lc; assumption ].
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      [ | intro He; subst; clear - HX; fsetdec
        | apply mono_ptyp_to_bskl_syn_lc; assumption ].
    match goal with
    | IH : forall X, X `notin` L -> forall Θ1 : list _, _ |- _ =>
        specialize (IH X ltac:(clear - HX; fsetdec)
                      ((X ~ abind_tvar) ++ Θ1) β τ0 Θ2);
        simpl_env in IH; simpl_env; apply IH
    end;
      [ reflexivity
      | clear - Hfr HX; simpl_env in *; fsetdec
      | assumption
      | assumption
      | intros Y HY; apply a_binds_tvar_weaken_cons; auto
      | intros γ τ Hb;
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
        [ discriminate | eauto ] ].
  - apply ad_pat_consis__forall_syn
      with (L := L `union` {{β}} `union` dom (Θ1 ++ Θ2)).
    intros X HX.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | intro He; subst; clear - HX; fsetdec
        | apply mono_ptyp_to_uskl_syn_lc; assumption ].
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      [ | intro He; subst; clear - HX; fsetdec
        | apply mono_ptyp_to_bskl_syn_lc; assumption ].
    match goal with
    | IH : forall X, X `notin` L -> forall Θ1 : list _, _ |- _ =>
        specialize (IH X ltac:(clear - HX; fsetdec)
                      ((X ~ abind_tvar) ++ Θ1) β τ0 Θ2);
        simpl_env in IH; simpl_env; apply IH
    end;
      [ reflexivity
      | clear - Hfr HX; simpl_env in *; fsetdec
      | assumption
      | assumption
      | intros Y HY; apply a_binds_tvar_weaken_cons; auto
      | intros γ τ Hb;
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
        [ discriminate | eauto ] ].
  - apply ad_pat_consis__ghostg; assumption.
  - apply ad_pat_consis__topholeg; eauto.
  - rewrite pskl_to_bskl_inh_subst_mono; [ | assumption ].
    apply ad_pat_consis__hole; [ assumption | ].
    eapply a_wf_pskl_subst_ctx with (b := abind_flex_mono_def τ0);
      [ eassumption | reflexivity | exact Hfr | clear; fsetdec
      | apply mono_ptyp_to_pskl_guarded; assumption
      | apply a_scope_pskl_of_ptyp_vis;
        [ apply mono_ptyp_lc; assumption
        | intros Y HY; right; apply Hvis; assumption ] ].
  - apply ad_pat_consis__tophole; eauto.
  - apply ad_pat_consis__tophole_inh
      with (L := L `union` {{β}} `union` dom (Θ1 ++ Θ2)).
    intros X HX.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      [ | intro He; subst; clear - HX; fsetdec
        | apply mono_ptyp_to_bskl_syn_lc; assumption ].
    match goal with
    | IH : forall X, X `notin` L -> forall Θ1 : list _, _ |- _ =>
        specialize (IH X ltac:(clear - HX; fsetdec)
                       ((X ~ abind_tvar) ++ Θ1) β τ0 Θ2);
        simpl_env in IH; simpl_env; apply IH
    end;
      [ reflexivity
      | clear - Hfr HX; simpl_env in *; fsetdec
      | assumption
      | assumption
      | intros Y HY; apply a_binds_tvar_weaken_cons; auto
      | intros γ τ Hb;
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
        [ discriminate | eauto ] ].
  - apply ad_pat_consis__tophole_drop; eauto.
  - (* flex_l *)
    match goal with
    | |- context [ if ?e then _ else _ ] => destruct e as [-> | Hne]
    end.
    + (* the lookup at the stripped variable dissolves *)
      assert (Heqdef : τ = τ0) by (eapply binds_mid_def_eq; eauto).
      rewrite Heqdef in *; clear Heqdef.
      match goal with
      | IH : forall Θ1 : list _, _ |- _ =>
          specialize (IH Θ1 β τ0 Θ2 ltac:(reflexivity) Hfr Hm Hfrτ Hvis Hdefs)
      end.
      rewrite subst_bskl_in_uskl_fresh_eq in *; [ auto | ].
      rewrite ftvar_in_uskl_ptyp_to_uskl_syn. exact Hfrτ.
    + assert (Hb' : binds α (abind_flex_mono_def τ) (Θ1 ++ Θ2)).
      { eapply binds_strip_mid; eauto.
        intro He; inversion He; subst; exact (Hne eq_refl). }
      apply ad_pat_consis__flex_l with (τ := τ); [ exact Hb' | ].
      match goal with
      | IH : forall Θ1 : list _, _ |- _ =>
          specialize (IH Θ1 β τ0 Θ2 ltac:(reflexivity) Hfr Hm Hfrτ Hvis Hdefs)
      end.
      rewrite subst_bskl_in_uskl_fresh_eq in *; [ auto | ].
      rewrite ftvar_in_uskl_ptyp_to_uskl_syn. eauto.
  - (* flex_r *)
    match goal with
    | |- context [ if ?e then _ else _ ] => destruct e as [-> | Hne]
    end.
    + assert (Heqdef : τ = τ0) by (eapply binds_mid_def_eq; eauto).
      rewrite Heqdef in *; clear Heqdef.
      match goal with
      | IH : forall Θ1 : list _, _ |- _ =>
          specialize (IH Θ1 β τ0 Θ2 ltac:(reflexivity) Hfr Hm Hfrτ Hvis Hdefs)
      end.
      rewrite subst_bskl_in_bskl_fresh_eq in *; [ auto | ].
      rewrite ftvar_in_bskl_ptyp_to_bskl_syn. exact Hfrτ.
    + assert (Hb' : binds α (abind_flex_mono_def τ) (Θ1 ++ Θ2)).
      { eapply binds_strip_mid; eauto.
        intro He; inversion He; subst; exact (Hne eq_refl). }
      apply ad_pat_consis__flex_r with (τ := τ); [ exact Hb' | ].
      match goal with
      | IH : forall Θ1 : list _, _ |- _ =>
          specialize (IH Θ1 β τ0 Θ2 ltac:(reflexivity) Hfr Hm Hfrτ Hvis Hdefs)
      end.
      rewrite subst_bskl_in_bskl_fresh_eq in *; [ auto | ].
      rewrite ftvar_in_bskl_ptyp_to_bskl_syn. eauto.
Qed.
