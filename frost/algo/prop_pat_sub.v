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
Require Import src.frost.algo.prop_decorate.

Set Implicit Arguments.

(* ===================================================================== *)
(*  §1  Tag-context congruence                                            *)
(* ===================================================================== *)

Lemma ad_pat_sub_psi_cong : forall NM M Ψ Θ R Q,
  Ψ ⨟ Θ ⊢ₛᵃ[ NM | M ] R ⩽ Q ->
  forall Ψc, Ψ [=] Ψc ->
  Ψc ⨟ Θ ⊢ₛᵃ[ NM | M ] R ⩽ Q.
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
  Ψ ⨟ Θ ⊢ₛᵃ[ NM | M ] R ⩽ Q ->
  forall Θ', Θ ⊴ Θ' ->
  Ψ ⨟ Θ' ⊢ₛᵃ[ NM | M ] R ⩽ Q.
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
  Ψ ⨟ Θ ⊢ₛᵃ[ NM | M ] R ⩽ Q ->
  forall Θ',
  (forall x b, binds x b Θ -> binds x b Θ') ->
  Ψ ⨟ Θ' ⊢ₛᵃ[ NM | M ] R ⩽ Q.
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
  Ψ ⨟ Θ ⊢ₛᵃ S ∼ Q ->
  forall Θ1 β Θ2,
  Θ = Θ1 ++ (β ~ abind_flex_mono) ++ Θ2 ->
  β `notin` dom (Θ1 ++ Θ2) ->
  (forall γ τ, binds γ (abind_flex_mono_def τ) (Θ1 ++ Θ2) ->
     β `notin` ftvar_in_ptyp τ) ->
  Ψ ⨟ (Θ1 ++ Θ2) ⊢ₛᵃ (subst_bskl_in_uskl uskl_unit β S)
                    ∼ (subst_bskl_in_bskl bskl_unit β Q).
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
    | IH : _ -> _ -> _ -> _ ⨟ _ ⊢ₛᵃ _ ∼ _ |- _ => simpl_env; apply IH
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
  Ψ ⨟ Θ ⊢ₛᵃ S ∼ Q ->
  forall Θ1 β τ0 Θ2,
  Θ = Θ1 ++ (β ~ abind_flex_mono_def τ0) ++ Θ2 ->
  β `notin` dom (Θ1 ++ Θ2) ->
  mono_ptyp τ0 ->
  β `notin` ftvar_in_ptyp τ0 ->
  (forall X, X `in` ftvar_in_ptyp τ0 -> a_binds_tvar X (Θ1 ++ Θ2)) ->
  (forall γ τ, binds γ (abind_flex_mono_def τ) (Θ1 ++ Θ2) ->
     β `notin` ftvar_in_ptyp τ) ->
  Ψ ⨟ (Θ1 ++ Θ2) ⊢ₛᵃ (subst_bskl_in_uskl (ptyp_to_uskl_syn τ0) β S)
                    ∼ (subst_bskl_in_bskl (ptyp_to_bskl_syn τ0) β Q).
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

(** Ghost-freeness survives the unit substitution. *)
Lemma uskl_ghost_free_subst_unit : forall ψ β,
  uskl_ghost_free ψ ->
  uskl_ghost_free (subst_bskl_in_uskl uskl_unit β ψ).
Proof.
  intros ψ β H; induction H; simpl.
  - apply uskl_ghost_free__unit.
  - match goal with |- context [ if ?e then _ else _ ] => destruct e end;
      [ apply uskl_ghost_free__unit | apply uskl_ghost_free__var ].
  - apply uskl_ghost_free__arrow; auto.
  - apply uskl_ghost_free__all_etag with (L := L `union` {{β}}).
    intros X HX.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      [ auto | intro He; subst; clear - HX; fsetdec | apply lc_uskl_unit ].
  - apply uskl_ghost_free__all_syn with (L := L `union` {{β}}).
    intros X HX.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      [ auto | intro He; subst; clear - HX; fsetdec | apply lc_uskl_unit ].
Qed.

(** Tag-sorting survives the unit substitution. *)
Lemma a_tags_sort_subst_unit : forall NM Ψ' ψ β,
  a_tags_sort NM Ψ' ψ ->
  a_tags_sort NM Ψ' (subst_bskl_in_uskl uskl_unit β ψ).
Proof.
  intros NM Ψ' ψ β H; destruct H.
  - apply a_tags_sort__sk;
      [ apply is_tskl_subst_unit; assumption
      | apply d_tags_skl_subst_unit; assumption ].
  - apply a_tags_sort__ty;
      [ apply is_tskl_subst_unit; assumption
      | apply d_tags_skl_subst_unit; assumption
      | apply uskl_ghost_free_subst_unit; assumption ].
Qed.

(** STRIP an undefined flexible mid entry from [ad_pat_sub] by
    substituting unit — the ForallL witnesses are rewritten too, which is
    exactly why this is provable where naive strengthening is not. *)
Lemma ad_pat_sub_subst_flex : forall NM M Ψ Θ S Q,
  Ψ ⨟ Θ ⊢ₛᵃ[ NM | M ] S ⩽ Q ->
  forall Θ1 β Θ2,
  Θ = Θ1 ++ (β ~ abind_flex_mono) ++ Θ2 ->
  β `notin` dom (Θ1 ++ Θ2) ->
  (forall γ τ, binds γ (abind_flex_mono_def τ) (Θ1 ++ Θ2) ->
     β `notin` ftvar_in_ptyp τ) ->
  Ψ ⨟ (Θ1 ++ Θ2) ⊢ₛᵃ[ NM | M ] (subst_bskl_in_uskl uskl_unit β S)
                              ⩽ (subst_bskl_in_bskl bskl_unit β Q).
Proof.
  intros NM M Ψ Θ S Q H; induction H;
    intros Θ1 β Θ2 Heqc Hfr Hdefs; subst; simpl.
  - apply ad_pat_sub__infer;
      [ assumption
      | eapply ad_pat_consis_subst_flex; eauto
      | apply is_sskl_subst_unit; assumption ].
  - rewrite pskl_to_bskl_inh_subst_unit.
    apply ad_pat_sub__check;
      [ apply guarded_uskl_subst_unit; assumption
      | apply guarded_pskl_subst_unit; assumption | ].
    rewrite <- pskl_to_bskl_inh_subst_unit.
    eapply ad_pat_consis_subst_flex; eauto.
  - apply ad_pat_sub__forall_r
      with (L := L `union` {{β}} `union` dom (Θ1 ++ Θ2)).
    intros X HX.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      [ | intro He; subst; clear - HX; fsetdec | apply lc_bskl_unit ].
    specialize (H0 X ltac:(clear - HX; fsetdec)
                  ((X ~ abind_tvar) ++ Θ1) β Θ2).
    simpl_env in H0. simpl_env. apply H0;
      [ reflexivity
      | clear - Hfr HX; simpl_env in *; fsetdec
      | intros γ τ Hb;
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
        [ discriminate | eauto ] ].
  - apply ad_pat_sub__univ_ghost_r;
      [ assumption
      | apply guarded_uskl_subst_unit; assumption
      | apply guarded_bskl_subst_unit; assumption
      | apply is_sskl_subst_unit; assumption
      | eapply ad_pat_consis_subst_flex; eauto ].
  - eapply ad_pat_sub__arrow;
      [ eapply ad_pat_consis_subst_flex; eauto | eauto | assumption ].
  - specialize (IHad_pat_sub Θ1 β Θ2 ltac:(reflexivity) Hfr Hdefs).
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl in IHad_pat_sub;
      [ | apply lc_uskl_unit ].
    eapply ad_pat_sub__forall_l_tagged;
      [ assumption
      | eassumption
      | apply a_tags_sort_subst_unit; eassumption
      | rewrite uskl_to_pskl_subst_unit;
        eapply a_wf_pskl_subst_ctx with (b := abind_flex_mono);
          [ eassumption | reflexivity | exact Hfr | clear; fsetdec
          | apply guarded_pskl__unit | apply a_wf_pskl__unit ]
      | exact IHad_pat_sub ].
  - specialize (IHad_pat_sub Θ1 β Θ2 ltac:(reflexivity) Hfr Hdefs).
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl in IHad_pat_sub;
      [ | apply lc_uskl_unit ].
    eapply ad_pat_sub__forall_l_untagged;
      [ assumption
      | eassumption
      | apply a_tags_sort_subst_unit; eassumption
      | rewrite uskl_to_pskl_subst_unit;
        eapply a_wf_pskl_subst_ctx with (b := abind_flex_mono);
          [ eassumption | reflexivity | exact Hfr | clear; fsetdec
          | apply guarded_pskl__unit | apply a_wf_pskl__unit ]
      | exact IHad_pat_sub ].
  - rewrite pskl_to_bskl_inh_subst_unit.
    apply ad_pat_sub__ghost;
      [ assumption
      | eapply a_wf_pskl_subst_ctx with (b := abind_flex_mono);
          [ eassumption | reflexivity | exact Hfr | clear; fsetdec
          | apply guarded_pskl__unit | apply a_wf_pskl__unit ]
      | rewrite <- pskl_to_bskl_inh_subst_unit;
        apply mod_comp_sk_subst_unit; assumption ].
  - apply ad_pat_sub__ghostg; [ assumption | ].
    change bskl_hole with (subst_bskl_in_bskl bskl_unit β bskl_hole).
    apply mod_comp_sk_subst_unit; assumption.
  - apply ad_pat_sub__univ_ghost_l; [ assumption | eauto ].
  - apply ad_pat_sub__univ_ghost_lg; [ assumption | eauto ].
  - match goal with
    | |- context [ if ?e then _ else _ ] => destruct e as [-> | Hne]
    end.
    + exfalso. eapply binds_mid_flex_absurd; eauto.
    + assert (Hb' : binds α (abind_flex_mono_def τ) (Θ1 ++ Θ2)).
      { eapply binds_strip_mid; eauto.
        intro He; inversion He; subst; exact (Hne eq_refl). }
      eapply ad_pat_sub__flex_mono; [ exact Hb' | ].
      match goal with
      | IH : forall Θ1 : list _, _ |- _ =>
          specialize (IH Θ1 β Θ2 ltac:(reflexivity) Hfr Hdefs)
      end.
      rewrite subst_bskl_in_uskl_fresh_eq in *; [ auto | ].
      rewrite ftvar_in_uskl_ptyp_to_uskl_syn. eauto.
Qed.

(** Closure of the syntactic predicates under substitution by a monotype
    painting (the defined-entry strip's substituend). *)
Lemma mono_ptyp_to_uskl_syn_guarded : forall τ,
  mono_ptyp τ -> guarded_uskl (ptyp_to_uskl_syn τ).
Proof.
  destruct 1; simpl;
    [ apply guarded_uskl__unit | apply guarded_uskl__var
    | apply guarded_uskl__arrow; apply mono_ptyp_to_uskl_syn_lc; auto ].
Qed.

Lemma mono_ptyp_to_bskl_syn_guarded : forall τ,
  mono_ptyp τ -> guarded_bskl (ptyp_to_bskl_syn τ).
Proof.
  destruct 1; simpl;
    [ apply guarded_bskl__unit | apply guarded_bskl__var
    | apply guarded_bskl__arrow; apply mono_ptyp_to_bskl_syn_lc; auto ].
Qed.

Lemma mono_ptyp_to_bskl_syn_is_sskl : forall τ,
  mono_ptyp τ -> is_sskl (ptyp_to_bskl_syn τ).
Proof.
  induction 1; simpl;
    [ apply is_sskl__unit | apply is_sskl__var | apply is_sskl__arrow; auto ].
Qed.

Lemma mono_ptyp_to_uskl_syn_is_tskl : forall τ,
  mono_ptyp τ -> is_tskl (ptyp_to_uskl_syn τ).
Proof.
  induction 1; simpl;
    [ apply is_tskl__unit | apply is_tskl__var | apply is_tskl__arrow; auto ].
Qed.

Lemma mono_ptyp_to_uskl_syn_ghost_free : forall τ,
  mono_ptyp τ -> uskl_ghost_free (ptyp_to_uskl_syn τ).
Proof.
  induction 1; simpl;
    [ apply uskl_ghost_free__unit | apply uskl_ghost_free__var
    | apply uskl_ghost_free__arrow; auto ].
Qed.

Lemma mono_ptyp_to_uskl_syn_tags : forall τ Ψ,
  mono_ptyp τ -> Ψ [=] empty -> d_tags_skl Ψ (ptyp_to_uskl_syn τ).
Proof.
  intros τ Ψ Hm; revert Ψ; induction Hm; intros Ψ He; simpl.
  - apply d_tags_skl__unit; assumption.
  - apply d_tags_skl__var; assumption.
  - apply d_tags_skl__arrow with (Ψ1 := empty) (Ψ2 := empty);
      [ apply IHHm1 | apply IHHm2 | | ]; clear - He; fsetdec.
Qed.

Lemma guarded_uskl_subst_mono : forall R τ β,
  guarded_uskl R -> mono_ptyp τ ->
  guarded_uskl (subst_bskl_in_uskl (ptyp_to_uskl_syn τ) β R).
Proof.
  intros R τ β H Hm; destruct H; simpl.
  - apply guarded_uskl__unit.
  - match goal with |- context [ if ?e then _ else _ ] => destruct e end;
      [ apply mono_ptyp_to_uskl_syn_guarded; assumption
      | apply guarded_uskl__var ].
  - apply guarded_uskl__arrow;
      apply subst_bskl_in_uskl_lc_uskl;
      auto using mono_ptyp_to_uskl_syn_lc.
Qed.

Lemma guarded_bskl_subst_mono : forall Q τ β,
  guarded_bskl Q -> mono_ptyp τ ->
  guarded_bskl (subst_bskl_in_bskl (ptyp_to_bskl_syn τ) β Q).
Proof.
  intros Q τ β H Hm; destruct H; simpl.
  - apply guarded_bskl__unit.
  - match goal with |- context [ if ?e then _ else _ ] => destruct e end;
      [ apply mono_ptyp_to_bskl_syn_guarded; assumption
      | apply guarded_bskl__var ].
  - apply guarded_bskl__arrow;
      apply subst_bskl_in_bskl_lc_bskl;
      auto using mono_ptyp_to_bskl_syn_lc.
Qed.

Lemma is_sskl_subst_mono : forall Q τ β,
  is_sskl Q -> mono_ptyp τ ->
  is_sskl (subst_bskl_in_bskl (ptyp_to_bskl_syn τ) β Q).
Proof.
  intros Q τ β H Hm; induction H; simpl.
  - apply is_sskl__unit.
  - match goal with |- context [ if ?e then _ else _ ] => destruct e end;
      [ apply mono_ptyp_to_bskl_syn_is_sskl; assumption | apply is_sskl__var ].
  - apply is_sskl__arrow; auto.
  - apply is_sskl__all with (L := L `union` {{β}}).
    intros X HX.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      [ auto | intro He; subst; clear - HX; fsetdec
      | apply mono_ptyp_to_bskl_syn_lc; assumption ].
  - apply is_sskl__hole.
  - apply is_sskl__tophole; auto.
Qed.

Lemma mod_comp_sk_subst_mono : forall S m τ β,
  mod_comp_sk S m -> mono_ptyp τ ->
  mod_comp_sk (subst_bskl_in_bskl (ptyp_to_bskl_syn τ) β S) m.
Proof.
  intros S m τ β H Hm; induction H.
  - apply mod_comp_sk__ti; apply is_sskl_subst_mono; assumption.
  - apply mod_comp_sk__tc; apply is_sskl_subst_mono; assumption.
  - simpl; apply mod_comp_sk__fn; assumption.
Qed.

Lemma is_tskl_subst_mono : forall ψ τ β,
  is_tskl ψ -> mono_ptyp τ ->
  is_tskl (subst_bskl_in_uskl (ptyp_to_uskl_syn τ) β ψ).
Proof.
  intros ψ τ β H Hm; induction H; simpl.
  - apply is_tskl__unit.
  - match goal with |- context [ if ?e then _ else _ ] => destruct e end;
      [ apply mono_ptyp_to_uskl_syn_is_tskl; assumption | apply is_tskl__var ].
  - apply is_tskl__arrow; auto.
  - apply is_tskl__all_etag with (L := L `union` {{β}}).
    intros X HX.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      [ auto | intro He; subst; clear - HX; fsetdec
      | apply mono_ptyp_to_uskl_syn_lc; assumption ].
  - apply is_tskl__holeg.
  - apply is_tskl__topholeg; auto.
Qed.

Lemma d_tags_skl_subst_mono : forall Δ ψ τ β,
  d_tags_skl Δ ψ -> mono_ptyp τ ->
  d_tags_skl Δ (subst_bskl_in_uskl (ptyp_to_uskl_syn τ) β ψ).
Proof.
  intros Δ ψ τ β H Hm; induction H; simpl.
  - apply d_tags_skl__unit; assumption.
  - match goal with |- context [ if ?e then _ else _ ] => destruct e end;
      [ apply mono_ptyp_to_uskl_syn_tags; assumption
      | apply d_tags_skl__var; assumption ].
  - apply d_tags_skl__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2); assumption.
  - apply d_tags_skl__all_etag with (L := L `union` {{β}}) (Ψ0 := Ψ0);
      [ | assumption | assumption ].
    intros Y HY.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      [ auto | intro He; subst; clear - HY; fsetdec
      | apply mono_ptyp_to_uskl_syn_lc; assumption ].
  - apply d_tags_skl__holeg; assumption.
  - apply d_tags_skl__topholeg; assumption.
Qed.

Lemma uskl_ghost_free_subst_mono : forall ψ τ β,
  uskl_ghost_free ψ -> mono_ptyp τ ->
  uskl_ghost_free (subst_bskl_in_uskl (ptyp_to_uskl_syn τ) β ψ).
Proof.
  intros ψ τ β H Hm; induction H; simpl.
  - apply uskl_ghost_free__unit.
  - match goal with |- context [ if ?e then _ else _ ] => destruct e end;
      [ apply mono_ptyp_to_uskl_syn_ghost_free; assumption
      | apply uskl_ghost_free__var ].
  - apply uskl_ghost_free__arrow; auto.
  - apply uskl_ghost_free__all_etag with (L := L `union` {{β}}).
    intros X HX.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      [ auto | intro He; subst; clear - HX; fsetdec
      | apply mono_ptyp_to_uskl_syn_lc; assumption ].
  - apply uskl_ghost_free__all_syn with (L := L `union` {{β}}).
    intros X HX.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      [ auto | intro He; subst; clear - HX; fsetdec
      | apply mono_ptyp_to_uskl_syn_lc; assumption ].
Qed.

Lemma a_tags_sort_subst_mono : forall NM Ψ' ψ τ β,
  a_tags_sort NM Ψ' ψ -> mono_ptyp τ ->
  a_tags_sort NM Ψ' (subst_bskl_in_uskl (ptyp_to_uskl_syn τ) β ψ).
Proof.
  intros NM Ψ' ψ τ β H Hm; destruct H.
  - apply a_tags_sort__sk;
      auto using is_tskl_subst_mono, d_tags_skl_subst_mono.
  - apply a_tags_sort__ty;
      auto using is_tskl_subst_mono, d_tags_skl_subst_mono,
                 uskl_ghost_free_subst_mono.
Qed.

(** Erasure of a monotype painting, and of the painting substitution. *)
Lemma uskl_to_pskl_ptyp_to_uskl_syn : forall τ,
  ⌊ ptyp_to_uskl_syn τ ⌋ˢ = ptyp_to_pskl τ.
Proof.
  intros. rewrite <- ptyp_to_uskl_syn_eq.
  apply uskl_to_pskl_pskl_to_uskl.
Qed.

Lemma uskl_to_pskl_subst_mono : forall S τ β,
  ⌊ subst_bskl_in_uskl (ptyp_to_uskl_syn τ) β S ⌋ˢ
  = subst_pskl_in_pskl (ptyp_to_pskl τ) β ⌊ S ⌋ˢ.
Proof.
  induction S; intros; simpl; try (f_equal; auto; fail).
  repeat match goal with
         | |- context [ if ?e then _ else _ ] => destruct e
         end; try contradiction;
    [ apply uskl_to_pskl_ptyp_to_uskl_syn | reflexivity ].
Qed.

(** STRIP a DEFINED flexible mid entry from [ad_pat_sub] by substituting
    its definition's paintings (the FlexMono lookup at the stripped
    variable dissolves into its premise). *)
Lemma ad_pat_sub_subst_flex_def : forall NM M Ψ Θ S Q,
  Ψ ⨟ Θ ⊢ₛᵃ[ NM | M ] S ⩽ Q ->
  forall Θ1 β τ0 Θ2,
  Θ = Θ1 ++ (β ~ abind_flex_mono_def τ0) ++ Θ2 ->
  β `notin` dom (Θ1 ++ Θ2) ->
  mono_ptyp τ0 ->
  β `notin` ftvar_in_ptyp τ0 ->
  (forall X, X `in` ftvar_in_ptyp τ0 -> a_binds_tvar X (Θ1 ++ Θ2)) ->
  (forall γ τ, binds γ (abind_flex_mono_def τ) (Θ1 ++ Θ2) ->
     β `notin` ftvar_in_ptyp τ) ->
  Ψ ⨟ (Θ1 ++ Θ2) ⊢ₛᵃ[ NM | M ]
      (subst_bskl_in_uskl (ptyp_to_uskl_syn τ0) β S)
    ⩽ (subst_bskl_in_bskl (ptyp_to_bskl_syn τ0) β Q).
Proof.
  intros NM M Ψ Θ S Q H; induction H;
    intros Θ1 β τ0 Θ2 Heqc Hfr Hm Hfrτ Hvis Hdefs; subst; simpl.
  - apply ad_pat_sub__infer;
      [ assumption
      | eapply ad_pat_consis_subst_flex_def; eauto
      | apply is_sskl_subst_mono; assumption ].
  - rewrite pskl_to_bskl_inh_subst_mono; [ | assumption ].
    apply ad_pat_sub__check;
      [ apply guarded_uskl_subst_mono; assumption
      | apply guarded_pskl_subst;
          [ assumption
          | apply mono_ptyp_to_pskl_guarded; assumption
          | apply mono_ptyp_to_pskl_lc; assumption ] | ].
    rewrite <- pskl_to_bskl_inh_subst_mono; [ | assumption ].
    eapply ad_pat_consis_subst_flex_def; eauto.
  - apply ad_pat_sub__forall_r
      with (L := L `union` {{β}} `union` dom (Θ1 ++ Θ2)).
    intros X HX.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      [ | intro He; subst; clear - HX; fsetdec
        | apply mono_ptyp_to_bskl_syn_lc; assumption ].
    specialize (H0 X ltac:(clear - HX; fsetdec)
                  ((X ~ abind_tvar) ++ Θ1) β τ0 Θ2).
    simpl_env in H0. simpl_env. apply H0;
      [ reflexivity
      | clear - Hfr HX; simpl_env in *; fsetdec
      | assumption
      | assumption
      | intros Y HY; apply a_binds_tvar_weaken_cons; auto
      | intros γ τ Hb;
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
        [ discriminate | eauto ] ].
  - apply ad_pat_sub__univ_ghost_r;
      [ assumption
      | apply guarded_uskl_subst_mono; assumption
      | apply guarded_bskl_subst_mono; assumption
      | apply is_sskl_subst_mono; assumption
      | eapply ad_pat_consis_subst_flex_def; eauto ].
  - eapply ad_pat_sub__arrow;
      [ eapply ad_pat_consis_subst_flex_def; eauto | eauto | assumption ].
  - specialize (IHad_pat_sub Θ1 β τ0 Θ2
                  ltac:(reflexivity) Hfr Hm Hfrτ Hvis Hdefs).
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl in IHad_pat_sub;
      [ | apply mono_ptyp_to_uskl_syn_lc; assumption ].
    eapply ad_pat_sub__forall_l_tagged;
      [ assumption
      | eassumption
      | apply a_tags_sort_subst_mono; eassumption
      | rewrite uskl_to_pskl_subst_mono;
        eapply a_wf_pskl_subst_ctx with (b := abind_flex_mono_def τ0);
          [ eassumption | reflexivity | exact Hfr | clear; fsetdec
          | apply mono_ptyp_to_pskl_guarded; assumption
          | apply a_scope_pskl_of_ptyp_vis;
              [ apply mono_ptyp_lc; assumption
              | intros Y HY; right; apply Hvis; assumption ] ]
      | exact IHad_pat_sub ].
  - specialize (IHad_pat_sub Θ1 β τ0 Θ2
                  ltac:(reflexivity) Hfr Hm Hfrτ Hvis Hdefs).
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl in IHad_pat_sub;
      [ | apply mono_ptyp_to_uskl_syn_lc; assumption ].
    eapply ad_pat_sub__forall_l_untagged;
      [ assumption
      | eassumption
      | apply a_tags_sort_subst_mono; eassumption
      | rewrite uskl_to_pskl_subst_mono;
        eapply a_wf_pskl_subst_ctx with (b := abind_flex_mono_def τ0);
          [ eassumption | reflexivity | exact Hfr | clear; fsetdec
          | apply mono_ptyp_to_pskl_guarded; assumption
          | apply a_scope_pskl_of_ptyp_vis;
              [ apply mono_ptyp_lc; assumption
              | intros Y HY; right; apply Hvis; assumption ] ]
      | exact IHad_pat_sub ].
  - rewrite pskl_to_bskl_inh_subst_mono; [ | assumption ].
    apply ad_pat_sub__ghost;
      [ assumption
      | eapply a_wf_pskl_subst_ctx with (b := abind_flex_mono_def τ0);
          [ eassumption | reflexivity | exact Hfr | clear; fsetdec
          | apply mono_ptyp_to_pskl_guarded; assumption
          | apply a_scope_pskl_of_ptyp_vis;
              [ apply mono_ptyp_lc; assumption
              | intros Y HY; right; apply Hvis; assumption ] ]
      | rewrite <- pskl_to_bskl_inh_subst_mono; [ | assumption ];
        apply mod_comp_sk_subst_mono; assumption ].
  - apply ad_pat_sub__ghostg; [ assumption | ].
    change bskl_hole
      with (subst_bskl_in_bskl (ptyp_to_bskl_syn τ0) β bskl_hole).
    apply mod_comp_sk_subst_mono; assumption.
  - apply ad_pat_sub__univ_ghost_l; [ assumption | eauto ].
  - apply ad_pat_sub__univ_ghost_lg; [ assumption | eauto ].
  - match goal with
    | |- context [ if ?e then _ else _ ] => destruct e as [-> | Hne]
    end.
    + assert (Heqdef : τ = τ0) by (eapply binds_mid_def_eq; eauto).
      rewrite Heqdef in *; clear Heqdef.
      specialize (IHad_pat_sub Θ1 β τ0 Θ2
                    ltac:(reflexivity) Hfr Hm Hfrτ Hvis Hdefs).
      rewrite subst_bskl_in_uskl_fresh_eq in IHad_pat_sub;
        [ exact IHad_pat_sub | ].
      rewrite ftvar_in_uskl_ptyp_to_uskl_syn. exact Hfrτ.
    + assert (Hb' : binds α (abind_flex_mono_def τ) (Θ1 ++ Θ2)).
      { eapply binds_strip_mid; eauto.
        intro He; inversion He; subst; exact (Hne eq_refl). }
      eapply ad_pat_sub__flex_mono; [ exact Hb' | ].
      specialize (IHad_pat_sub Θ1 β τ0 Θ2
                    ltac:(reflexivity) Hfr Hm Hfrτ Hvis Hdefs).
      rewrite subst_bskl_in_uskl_fresh_eq in IHad_pat_sub;
        [ exact IHad_pat_sub | ].
      rewrite ftvar_in_uskl_ptyp_to_uskl_syn. eauto.
Qed.

(** THE SUFFIX DRIVER: discard a trailing (fresh, well-formed) suffix Ξ
    from an [ad_pat_sub] judgment whose subjects do not mention it — the
    paper's "context strengthening for unused variables in Ξ", proved by
    iterating the substitution strips head-first (the head entry is never
    mentioned by any other entry, since definitions scope to tails). *)
Lemma ad_pat_sub_strip_suffix : forall Ξ NM M Ψ Θ S Q,
  a_suffix Ξ ->
  a_wf_aenv (Ξ ++ Θ) ->
  (forall γ, γ `in` dom Ξ ->
     γ `notin` (ftvar_in_uskl S `union` ftvar_in_bskl Q)) ->
  Ψ ⨟ (Ξ ++ Θ) ⊢ₛᵃ[ NM | M ] S ⩽ Q ->
  Ψ ⨟ Θ ⊢ₛᵃ[ NM | M ] S ⩽ Q.
Proof.
  induction Ξ as [ | [β b] Ξ' IH ]; intros * Hsuf Hwf Hfv H; [ exact H | ].
  inversion Hsuf as [ | ? ? ? Hsuf' Hbind ]; subst.
  assert (Hβfv : β `notin` (ftvar_in_uskl S `union` ftvar_in_bskl Q))
    by (apply Hfv; simpl; fsetdec).
  inversion Hbind; subst.
  - (* undefined head *)
    inversion Hwf as [ | ? ? Hβd Hwf' | | | | ]; subst.
    assert (Hstr : Ψ ⨟ (Ξ' ++ Θ) ⊢ₛᵃ[ NM | M ]
                     (subst_bskl_in_uskl uskl_unit β S)
                   ⩽ (subst_bskl_in_bskl bskl_unit β Q)).
    { eapply ad_pat_sub_subst_flex with (Θ1 := nil);
        [ exact H | simpl_env; reflexivity | simpl; exact Hβd
        | intros γ τ Hb; simpl in Hb;
          assert (Hsc : ftvar_in_ptyp τ [<=] dom (Ξ' ++ Θ))
            by (eapply a_wf_aenv_def_ftv_dom; eauto);
          clear - Hsc Hβd; fsetdec ]. }
    rewrite subst_bskl_in_uskl_fresh_eq in Hstr;
      [ | clear - Hβfv; fsetdec ].
    rewrite subst_bskl_in_bskl_fresh_eq in Hstr;
      [ | clear - Hβfv; fsetdec ].
    apply IH; auto.
    intros γ Hγ. apply Hfv. simpl. clear - Hγ. fsetdec.
  - (* defined head *)
    inversion Hwf as [ | | ? τ0' ? Hβd Hwfτ Hmono Hwf' | | | ]; subst.
    assert (Hfrτ : β `notin` ftvar_in_ptyp A).
    { intro HX.
      pose proof (a_wf_ptyp_ftv_tvarish Hwfτ HX) as Ht.
      destruct Ht as [Hb | [Hb | [τ1 Hb]]]; apply binds_In in Hb;
        clear - Hb Hβd; fsetdec. }
    assert (Hstr : Ψ ⨟ (Ξ' ++ Θ) ⊢ₛᵃ[ NM | M ]
                     (subst_bskl_in_uskl (ptyp_to_uskl_syn A) β S)
                   ⩽ (subst_bskl_in_bskl (ptyp_to_bskl_syn A) β Q)).
    { eapply ad_pat_sub_subst_flex_def with (Θ1 := nil);
        [ exact H | simpl_env; reflexivity | simpl; exact Hβd
        | exact Hmono | exact Hfrτ
        | intros X HX; eapply a_wf_ptyp_ftv_tvarish; eauto
        | intros γ τ Hb; simpl in Hb;
          assert (Hsc : ftvar_in_ptyp τ [<=] dom (Ξ' ++ Θ))
            by (eapply a_wf_aenv_def_ftv_dom; eauto);
          clear - Hsc Hβd; fsetdec ]. }
    rewrite subst_bskl_in_uskl_fresh_eq in Hstr;
      [ | clear - Hβfv; fsetdec ].
    rewrite subst_bskl_in_bskl_fresh_eq in Hstr;
      [ | clear - Hβfv; fsetdec ].
    apply IH; auto.
    intros γ Hγ. apply Hfv. simpl. clear - Hγ. fsetdec.
Qed.

(** Renaming the opened rigid binder in [ad_pat_sub] (mirror of
    [ad_pat_consis_rename_tvar]; the tag/guardedness closures come from
    the [_mono] pack at [τ := ptyp_var_f Y]). *)
Lemma ad_pat_sub_rename_tvar : forall NM M Ψ Θ1 α Θ0 S Q Y,
  Ψ ⨟ (Θ1 ++ (α ~ abind_tvar) ++ Θ0) ⊢ₛᵃ[ NM | M ] S ⩽ Q ->
  α `notin` dom (Θ1 ++ Θ0) ->
  (forall β τ, binds β (abind_flex_mono_def τ) (Θ1 ++ Θ0) ->
     α `notin` ftvar_in_ptyp τ) ->
  Ψ ⨟ (Θ1 ++ (Y ~ abind_tvar) ++ Θ0) ⊢ₛᵃ[ NM | M ]
      (subst_bskl_in_uskl (uskl_var_f Y) α S)
    ⩽ (subst_bskl_in_bskl (bskl_var_f Y) α Q).
Proof.
  intros * H.
  remember (Θ1 ++ (α ~ abind_tvar) ++ Θ0) as Θfull eqn:HeqΘ.
  revert Θ1 HeqΘ.
  induction H; intros Θ1 ->; intros Hdom Hdefs; simpl.
  - apply ad_pat_sub__infer; auto.
    + apply ad_pat_consis_rename_tvar; auto.
    + change (bskl_var_f Y) with (ptyp_to_bskl_syn (ptyp_var_f Y)).
      apply is_sskl_subst_mono; auto using mono_ptyp.
  - rewrite subst_var_bskl_inh.
    apply ad_pat_sub__check.
    + change (uskl_var_f Y) with (ptyp_to_uskl_syn (ptyp_var_f Y)).
      apply guarded_uskl_subst_mono; auto using mono_ptyp.
    + apply guarded_pskl_subst; auto using guarded_pskl__var, lc_pskl_var_f.
    + rewrite <- subst_var_bskl_inh.
      apply ad_pat_consis_rename_tvar; auto.
  - apply ad_pat_sub__forall_r with (L := L `union` singleton α).
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
  - apply ad_pat_sub__univ_ghost_r; auto.
    + change (uskl_var_f Y) with (ptyp_to_uskl_syn (ptyp_var_f Y)).
      apply guarded_uskl_subst_mono; auto using mono_ptyp.
    + change (bskl_var_f Y) with (ptyp_to_bskl_syn (ptyp_var_f Y)).
      apply guarded_bskl_subst_mono; auto using mono_ptyp.
    + change (bskl_var_f Y) with (ptyp_to_bskl_syn (ptyp_var_f Y)).
      apply is_sskl_subst_mono; auto using mono_ptyp.
    + apply ad_pat_consis_rename_tvar; auto.
  - specialize (IHad_pat_sub Θ1 ltac:(reflexivity) Hdom Hdefs).
    eapply ad_pat_sub__arrow.
    + eapply ad_pat_consis_rename_tvar; eauto.
    + exact IHad_pat_sub.
    + eassumption.
  - specialize (IHad_pat_sub Θ1 ltac:(reflexivity) Hdom Hdefs).
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl in IHad_pat_sub;
      [ | apply lc_uskl_var_f ].
    eapply ad_pat_sub__forall_l_tagged.
    5: exact IHad_pat_sub.
    + assumption.
    + eassumption.
    + change (uskl_var_f Y) with (ptyp_to_uskl_syn (ptyp_var_f Y)).
      apply a_tags_sort_subst_mono;
        [ assumption | apply mono_ptyp__var ].
    + change (uskl_var_f Y) with (ptyp_to_uskl_syn (ptyp_var_f Y)).
      rewrite uskl_to_pskl_subst_mono. simpl.
      apply a_wf_pskl_rename_tvar;
        first [ assumption | clear; fsetdec ].
  - specialize (IHad_pat_sub Θ1 ltac:(reflexivity) Hdom Hdefs).
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl in IHad_pat_sub;
      [ | apply lc_uskl_var_f ].
    eapply ad_pat_sub__forall_l_untagged.
    5: exact IHad_pat_sub.
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
    apply ad_pat_sub__ghost; auto.
    + apply a_wf_pskl_rename_tvar; [ assumption | clear; fsetdec ].
    + rewrite <- subst_var_bskl_inh.
      change (bskl_var_f Y) with (ptyp_to_bskl_syn (ptyp_var_f Y)).
      apply mod_comp_sk_subst_mono; auto using mono_ptyp.
  - apply ad_pat_sub__ghostg; auto.
  - apply ad_pat_sub__univ_ghost_l; auto.
  - apply ad_pat_sub__univ_ghost_lg; auto.
  - match goal with
    | |- context [ if ?e then _ else _ ] => destruct e as [-> | Hne]
    end.
    + (* the subject flex cannot be the renamed rigid *)
      exfalso.
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
      eapply ad_pat_sub__flex_mono.
      { unfold binds in Hb' |- *. apply in_app_or in Hb'.
        apply in_or_app.
        destruct Hb' as [Hb' | Hb'];
          [ left; exact Hb' | right; simpl; right; exact Hb' ]. }
      specialize (IHad_pat_sub Θ1 ltac:(reflexivity) Hdom Hdefs).
      rewrite subst_bskl_in_uskl_fresh_eq in IHad_pat_sub;
        [ exact IHad_pat_sub | ].
      rewrite ftvar_in_uskl_ptyp_syn. eauto.
Qed.

(** Unique mid-split of a uniq environment at a shared key. *)
Lemma app_mid_uniq_split : forall (Ξ : aenv) Ξ' Θ Θ' α (b b' : abind),
  uniq (Ξ ++ (α ~ b) ++ Θ) ->
  Ξ ++ (α ~ b) ++ Θ = Ξ' ++ (α ~ b') ++ Θ' ->
  Ξ = Ξ' /\ b = b' /\ Θ = Θ'.
Proof.
  induction Ξ as [ | [γ c] Ξ2 IH ]; intros Ξ' Θ Θ' α b b' Huq Heq.
  - destruct Ξ' as [ | [γ' c'] Ξ'' ].
    + simpl in Heq. inversion Heq; subst. auto.
    + simpl in Heq. inversion Heq; subst.
      exfalso.
      inversion Huq; subst.
      simpl_env in *. fsetdec.
  - destruct Ξ' as [ | [γ' c'] Ξ'' ].
    + simpl in Heq. inversion Heq; subst.
      exfalso.
      inversion Huq; subst.
      simpl_env in *. fsetdec.
    + simpl in Heq. inversion Heq; subst.
      inversion Huq; subst.
      destruct (IH Ξ'' Θ Θ' α b b' H1 H2) as [E1 [E2 E3]]; subst.
      auto.
Qed.

(** Strip the shared rigid binder — and the Barendregt suffix above it —
    from an information increase (the ⊴-half of soundness's ForallR). *)
Lemma a_isub_strip_tvar_mid : forall α Ξ Θ0 Θ1,
  uniq (Ξ ++ (α ~ abind_tvar) ++ Θ1) ->
  uniq (Ξ ++ Θ0) ->
  α `notin` dom Θ0 ->
  ((α ~ abind_tvar) ++ Θ0) ⊴ (Ξ ++ (α ~ abind_tvar) ++ Θ1) ->
  Θ0 ⊴ Θ1.
Proof.
  intros α Ξ Θ0 Θ1 Huq HuqΞ Hα [[ρ [Hid Hinc]] Hdef].
  destruct (a_inc_tvar_inv Hinc) as [Ξ' [Θ2 [Heq [Hsuf Hinc']]]].
  destruct (app_mid_uniq_split _ _ _ _ _ _ _ Huq Heq) as [<- [_ <-]].
  split.
  - exists ρ. split; [ exact Hid | exact Hinc' ].
  - intros β τ Hb.
    assert (HβΘ0 : β `in` dom Θ0) by (eapply binds_In; eauto).
    assert (Hbw : binds β (abind_flex_mono_def τ)
                    (Ξ ++ (α ~ abind_tvar) ++ Θ1))
      by (apply Hdef; unfold binds; right; exact Hb).
    unfold binds in Hbw. apply in_app_or in Hbw.
    destruct Hbw as [Hbw | Hbw].
    { exfalso.
      assert (HβΞ : β `in` dom Ξ) by (eapply binds_In; exact Hbw).
      clear - HuqΞ HβΘ0 HβΞ.
      destruct_uniq. unfold disjoint in *. fsetdec. }
    simpl in Hbw. destruct Hbw as [Heqp | Hbw].
    { exfalso. inversion Heqp. }
    exact Hbw.
Qed.

(* ===================================================================== *)
(*  §5  Ghost-free fills (the TY axis)                                    *)
(*                                                                        *)
(*  On the TY axis P0 is a TYPE — hole- and ⊤◇-free (the paper's          *)
(*  implicit "P0 ranges over types"; registered as an external side       *)
(*  condition).  A fill whose SOURCE is ghost-free never uses the hole /  *)
(*  ⊤◇ rules, so it consults the context only through variable            *)
(*  visibility and definition lookups — so it can be strengthened (the   *)
(*  trailing Ξ dropped) and its opened binder renamed into a Δ-slot,     *)
(*  with no F-hygiene at all: what ForallR's fill re-attachment needs.   *)
(* ===================================================================== *)

Fixpoint pskl_ghost_free (P : pskl) : Prop :=
  match P with
  | pskl_unit => True
  | pskl_var_b _ => True
  | pskl_var_f _ => True
  | pskl_arrow P1 P2 => pskl_ghost_free P1 /\ pskl_ghost_free P2
  | pskl_all_syn P0 => pskl_ghost_free P0
  | pskl_hole => False
  | pskl_tophole _ => False
  end.

Fixpoint bskl_ghost_free (Q : bskl) : Prop :=
  match Q with
  | bskl_unit => True
  | bskl_var_b _ => True
  | bskl_var_f _ => True
  | bskl_arrow Q1 Q2 => bskl_ghost_free Q1 /\ bskl_ghost_free Q2
  | bskl_all_syn Q0 => bskl_ghost_free Q0
  | bskl_all_inh Q0 => bskl_ghost_free Q0
  | bskl_hole => False
  | bskl_tophole _ => False
  end.

Lemma pskl_to_bskl_inh_ghost_free : forall P,
  pskl_ghost_free P ->
  bskl_ghost_free (pskl_to_bskl_inh P).
Proof. induction P; simpl; intuition. Qed.

Lemma pskl_ghost_free_open_rec : forall P X k,
  pskl_ghost_free P ->
  pskl_ghost_free (open_pskl_wrt_pskl_rec k (pskl_var_f X) P).
Proof.
  induction P; intros X k Hg; simpl in *; intuition.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; auto.
Qed.

Lemma bskl_ghost_free_open_rec : forall Q X k,
  bskl_ghost_free Q ->
  bskl_ghost_free (open_bskl_wrt_bskl_rec k (bskl_var_f X) Q).
Proof.
  induction Q; intros X k Hg; simpl in *; intuition.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; auto.
Qed.

Lemma mono_ptyp_to_bskl_syn_ghost_free : forall τ,
  mono_ptyp τ -> bskl_ghost_free (ptyp_to_bskl_syn τ).
Proof. induction 1; simpl; intuition. Qed.

(** Well-formedness survives dropping an [a_suffix]-and-rigid prefix. *)
Lemma a_wf_aenv_strip_prefix_suffix_local : forall Ξ α Θ,
  a_wf_aenv (Ξ ++ (α ~ abind_tvar) ++ Θ) ->
  a_wf_aenv Θ.
Proof.
  induction Ξ as [ | [γ b] Ξ' IH ]; intros α Θ Hwf; simpl_env in *.
  - inversion Hwf; subst; assumption.
  - inversion Hwf; subst; simpl_env in *; eapply IH; eassumption.
Qed.

(** Strengthening + renaming for ghost-free-source fills: drop the
    trailing suffix Ξ and rename the shared rigid binder into a Δ-slot
    (the two transports ForallR's fill re-attachment needs, fused so the
    induction runs once). *)
Lemma ad_refine_syn_f_ghost_free_strip_rename : forall F Θfull Δ Q P,
  ad_refine_syn_f F Θfull Δ Q P ->
  forall Ξ α Θ1 Y,
  Θfull = Ξ ++ (α ~ abind_tvar) ++ Θ1 ->
  bskl_ghost_free Q ->
  a_wf_aenv Θfull ->
  uniq Θfull ->
  (forall X, X `in` (ftvar_in_bskl Q `union` ftvar_in_bskl P) ->
     X `notin` dom Ξ) ->
  ad_refine_syn_f F Θ1 (add Y (remove α Δ))
    (subst_bskl_in_bskl (bskl_var_f Y) α Q)
    (subst_bskl_in_bskl (bskl_var_f Y) α P).
Proof.
  intros F Θfull Δ Q P H; induction H;
    intros Ξ0 α0 Θt Y Heqc Hg Hwf Huq Hfv; subst; simpl in *.
  - apply ad_refine_syn_f__unit.
  - repeat match goal with
           | |- context [ if ?e then _ else _ ] => destruct e
           end; try contradiction.
    + apply ad_refine_syn_f__var. left. clear; fsetdec.
    + apply ad_refine_syn_f__var.
      destruct H as [HΔ | Hbt];
        [ left; match goal with Hne : X <> α0 |- _ =>
                  clear - HΔ Hne; fsetdec end | right ].
      match goal with Hne : X <> α0 |- _ =>
        assert (HXΞ : X `notin` dom Ξ0) by (apply Hfv; clear; fsetdec);
        destruct Hbt as [Hb | [Hb | [τ Hb]]];
          [ left | right; left | right; right; exists τ ];
          (eapply binds_strip_mid in Hb;
             [ | intro He; inversion He; subst; exact (Hne eq_refl) ];
           unfold binds in Hb; apply in_app_or in Hb;
           destruct Hb as [Hb | Hb];
             [ exfalso; apply HXΞ; eapply binds_In; exact Hb | exact Hb ])
      end.
  - destruct Hg as [Hg1 Hg2].
    apply ad_refine_syn_f__arrow;
      [ eapply IHad_refine_syn_f1 | eapply IHad_refine_syn_f2 ];
      eauto; intros X HX; apply Hfv; clear - HX; fsetdec.
  - apply ad_refine_syn_f__all
      with (L := L `union` {{α0}} `union` {{Y}} `union` dom (Ξ0 ++ Θt)
                   `union` ftvar_in_bskl Q `union` ftvar_in_bskl P).
    intros X HX.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      [ | intro He; subst; clear - HX; fsetdec | apply lc_bskl_var_f ].
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      [ | intro He; subst; clear - HX; fsetdec | apply lc_bskl_var_f ].
    eapply ad_refine_syn_f_delta_mono;
      [ eapply (H0 X ltac:(clear - HX; fsetdec) Ξ0 α0 Θt Y);
        [ reflexivity
        | apply bskl_ghost_free_open_rec; assumption
        | assumption
        | assumption
        | intros Z HZ;
          pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper
                        Q (bskl_var_f X)) as Hup1;
          pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper
                        P (bskl_var_f X)) as Hup2;
          simpl in Hup1, Hup2;
          assert (HZQP : Z `in` (ftvar_in_bskl Q `union` ftvar_in_bskl P)
                         \/ Z `in` singleton X)
            by (clear - HZ Hup1 Hup2; fsetdec);
          destruct HZQP as [HZQP | HZX];
            [ apply Hfv; clear - HZQP; fsetdec
            | assert (HZeq : Z = X) by (clear - HZX; fsetdec);
              subst Z; clear - HX; simpl_env in *; fsetdec ] ]
      | clear - HX; fsetdec ].
  - destruct Hg.
  - destruct Hg.
  - destruct Hg.
  - destruct Hg.
  - (* flex_l *)
    match goal with
    | |- context [ if ?e then _ else _ ] => destruct e as [-> | Hne]
    end.
    + exfalso.
      assert (Hα0Ξ : α0 `notin` dom Ξ0)
        by (clear - Huq; simpl_env in Huq; destruct_uniq;
            unfold disjoint in *; simpl_env in *; fsetdec).
      assert (Hα0Θ : α0 `notin` dom Θt)
        by (clear - Huq; simpl_env in Huq; destruct_uniq;
            unfold disjoint in *; simpl_env in *; fsetdec).
      match goal with
      | Hb : binds _ (abind_flex_mono_def _) _ |- _ =>
          unfold binds in Hb; apply in_app_or in Hb;
          destruct Hb as [Hb | Hb];
            [ apply binds_In in Hb; clear - Hb Hα0Ξ; fsetdec | ];
          destruct Hb as [Heqp | Hb];
            [ inversion Heqp
            | apply binds_In in Hb; clear - Hb Hα0Θ; fsetdec ]
      end.
    + assert (HaΞ : α `notin` dom Ξ0)
        by (apply Hfv; clear; fsetdec).
      match goal with
      | HbX : binds α (abind_flex_mono_def τ) _ |- _ =>
          unfold binds in HbX; apply in_app_or in HbX;
          destruct HbX as [Hbb | Hbb];
            [ exfalso; apply HaΞ; eapply binds_In; exact Hbb | ];
          destruct Hbb as [Heqp | Hbb];
            [ inversion Heqp; subst; exact (Hne eq_refl) | ]
      end.
      assert (HwfΘt : a_wf_aenv Θt)
        by (eapply a_wf_aenv_strip_prefix_suffix_local; simpl_env in *; eauto).
      assert (Hτsc : ftvar_in_ptyp τ [<=] dom Θt)
        by (eapply a_wf_aenv_def_ftv_dom; eauto).
      assert (Hα0Θt : α0 `notin` dom Θt)
        by (clear - Huq; simpl_env in Huq; destruct_uniq;
            unfold disjoint in *; simpl_env in *; fsetdec).
      eapply ad_refine_syn_f__flex_l; [ exact Hbb | ].
      rewrite <- (subst_bskl_in_bskl_fresh_eq
                    (ptyp_to_bskl_syn τ) (bskl_var_f Y) α0).
      2:{ rewrite ftvar_in_bskl_ptyp_to_bskl_syn.
          clear - Hτsc Hα0Θt. fsetdec. }
      eapply IHad_refine_syn_f; eauto.
      * apply mono_ptyp_to_bskl_syn_ghost_free.
        eapply a_wf_aenv_binds_def_mono; [ exact HwfΘt | exact Hbb ].
      * intros Z HZ.
        rewrite ftvar_in_bskl_ptyp_to_bskl_syn in HZ.
        assert (HZfv : Z `in` ftvar_in_ptyp τ \/ Z `in` ftvar_in_bskl Q)
          by (clear - HZ; fsetdec).
        destruct HZfv as [HZτ | HZQ];
          [ | apply Hfv; clear - HZQ; fsetdec ].
        assert (HZΘt : Z `in` dom Θt) by (clear - Hτsc HZτ; fsetdec).
        clear - Huq HZΘt. simpl_env in Huq. destruct_uniq.
        unfold disjoint in *. simpl_env in *. fsetdec.
  - (* flex_r *)
    match goal with
    | |- context [ if ?e then _ else _ ] => destruct e as [-> | Hne]
    end.
    + exfalso.
      assert (Hα0Ξ : α0 `notin` dom Ξ0)
        by (clear - Huq; simpl_env in Huq; destruct_uniq;
            unfold disjoint in *; simpl_env in *; fsetdec).
      assert (Hα0Θ : α0 `notin` dom Θt)
        by (clear - Huq; simpl_env in Huq; destruct_uniq;
            unfold disjoint in *; simpl_env in *; fsetdec).
      match goal with
      | Hb : binds _ (abind_flex_mono_def _) _ |- _ =>
          unfold binds in Hb; apply in_app_or in Hb;
          destruct Hb as [Hb | Hb];
            [ apply binds_In in Hb; clear - Hb Hα0Ξ; fsetdec | ];
          destruct Hb as [Heqp | Hb];
            [ inversion Heqp
            | apply binds_In in Hb; clear - Hb Hα0Θ; fsetdec ]
      end.
    + assert (HaΞ : α `notin` dom Ξ0)
        by (apply Hfv; clear; fsetdec).
      match goal with
      | HbX : binds α (abind_flex_mono_def τ) _ |- _ =>
          unfold binds in HbX; apply in_app_or in HbX;
          destruct HbX as [Hbb | Hbb];
            [ exfalso; apply HaΞ; eapply binds_In; exact Hbb | ];
          destruct Hbb as [Heqp | Hbb];
            [ inversion Heqp; subst; exact (Hne eq_refl) | ]
      end.
      assert (HwfΘt : a_wf_aenv Θt)
        by (eapply a_wf_aenv_strip_prefix_suffix_local; simpl_env in *; eauto).
      assert (Hτsc : ftvar_in_ptyp τ [<=] dom Θt)
        by (eapply a_wf_aenv_def_ftv_dom; eauto).
      assert (Hα0Θt : α0 `notin` dom Θt)
        by (clear - Huq; simpl_env in Huq; destruct_uniq;
            unfold disjoint in *; simpl_env in *; fsetdec).
      eapply ad_refine_syn_f__flex_r; [ exact Hbb | ].
      rewrite <- (subst_bskl_in_bskl_fresh_eq
                    (ptyp_to_bskl_syn τ) (bskl_var_f Y) α0).
      2:{ rewrite ftvar_in_bskl_ptyp_to_bskl_syn.
          clear - Hτsc Hα0Θt. fsetdec. }
      eapply IHad_refine_syn_f; eauto.
      intros Z HZ.
      rewrite ftvar_in_bskl_ptyp_to_bskl_syn in HZ.
      assert (HZfv : Z `in` ftvar_in_ptyp τ \/ Z `in` ftvar_in_bskl P)
        by (clear - HZ; fsetdec).
      destruct HZfv as [HZτ | HZP];
        [ | apply Hfv; clear - HZP; fsetdec ].
      assert (HZΘt : Z `in` dom Θt) by (clear - Hτsc HZτ; fsetdec).
      clear - Huq HZΘt. simpl_env in Huq. destruct_uniq.
      unfold disjoint in *. simpl_env in *. fsetdec.
Qed.

(** INVERSION: a ghost-free-source fill whose target erases back to the
    source is the inh painting itself — "the run lands on B" (the Check
    case of subtyping soundness).  The flex rules cannot escape: a
    variable's erasure pins the target variable node syntactically. *)
Lemma ad_refine_syn_f_ghost_free_erasure_inv : forall F Θ Δ Qsrc Ptgt,
  ad_refine_syn_f F Θ Δ Qsrc Ptgt ->
  forall B,
  Qsrc = pskl_to_bskl_inh B ->
  pskl_ghost_free B ->
  bskl_to_pskl Ptgt = B ->
  Ptgt = pskl_to_bskl_inh B.
Proof.
  intros F Θ Δ Qsrc Ptgt H; induction H; intros B HeqQ Hg HeqP;
    destruct B; simpl in HeqQ; inversion HeqQ; subst; simpl in *.
  - (* unit *) reflexivity.
  - (* var *) reflexivity.
  - (* arrow *)
    destruct Hg as [Hg1 Hg2].
    inversion HeqP.
    f_equal;
      [ apply (IHad_refine_syn_f1 (bskl_to_pskl P1))
      | apply (IHad_refine_syn_f2 (bskl_to_pskl P2)) ];
      auto; congruence.
  - (* all_inh *)
    inversion HeqP.
    match goal with
    | Heq2 : bskl_to_pskl P = _ |- _ => rewrite <- Heq2 in H0, H, Hg
    end.
    f_equal.
    destruct (atom_fresh
                (L `union` ftvar_in_bskl P
                   `union` ftvar_in_bskl
                       (pskl_to_bskl_inh (bskl_to_pskl P))))
      as [X Fr].
    apply open_bskl_wrt_bskl_inj with (α1 := X);
      [ clear - Fr; fsetdec | clear - Fr; fsetdec | ].
    rewrite <- pskl_to_bskl_inh_open.
    apply H0; [ clear - Fr; fsetdec | | | ].
    + symmetry. apply pskl_to_bskl_inh_open.
    + unfold open_pskl_wrt_pskl. apply pskl_ghost_free_open_rec.
      exact Hg.
    + rewrite bskl_to_pskl_open. reflexivity.
  - (* hole : B would be a ghost *) destruct Hg.
  - (* tophole_remove *) destruct Hg.
  - (* tophole_fill *) destruct Hg.
  - (* tophole_keep *) destruct Hg.
  - (* flex_l : the source variable pins the target *)
    destruct Q; simpl in HeqP; inversion HeqP; subst; reflexivity.
  - (* flex_r : Qsrc is a rule variable, so every B-shape survives the
       top-level destruct; the erasure equation discriminates all but the
       variable one. *)
    inversion HeqP; subst; reflexivity.
  - inversion HeqP; subst; reflexivity.
  - inversion HeqP; subst; reflexivity.
  - inversion HeqP; subst; reflexivity.
  - inversion HeqP; subst; reflexivity.
  - inversion HeqP; subst; reflexivity.
  - inversion HeqP; subst; reflexivity.
Qed.

(** Ghost-freeness survives substitution by a monotype painting. *)
Lemma pskl_ghost_free_subst_mono : forall P τ β,
  pskl_ghost_free P -> mono_ptyp τ ->
  pskl_ghost_free (subst_pskl_in_pskl (ptyp_to_pskl τ) β P).
Proof.
  induction P; intros τ β Hg Hm; simpl in *; intuition.
  match goal with |- context [ if ?e then _ else _ ] => destruct e end;
    [ | simpl; auto ].
  clear - Hm. induction Hm; simpl; intuition.
Qed.

(** FOLD a definition back into a fill's source: if the τ-image of Q0
    fills to Qt, then Q0 itself does — every β̂-node of Q0 caps its
    τ-subtree with [flex_l], rebuilt from the case's own premises.
    (Flex-Assign's re-entry premise speaks about the substituted input;
    its conclusion about the original.) *)
Lemma ad_refine_syn_f_fold_def_source : forall F Θ Δ Qs Qt,
  ad_refine_syn_f F Θ Δ Qs Qt ->
  forall β τ Q0,
  binds β (abind_flex_mono_def τ) Θ ->
  mono_ptyp τ ->
  Qs = subst_bskl_in_bskl (ptyp_to_bskl_syn τ) β Q0 ->
  ad_refine_syn_f F Θ Δ Q0 Qt.
Proof.
  intros F Θ Δ Qs Qt H; induction H;
    intros β τ0 Q0 Hb Hm HeqQs;
    destruct Q0; simpl in HeqQs;
    try match goal with
        | Hif : context [ if ?e then _ else _ ] |- _ =>
            let He := fresh "Hne" in destruct e as [-> | He]
        end;
    try discriminate HeqQs.
  - (* unit / Q0 = unit *) apply ad_refine_syn_f__unit.
  - (* unit / Q0 = var β, τ = unit *)
    eapply ad_refine_syn_f__flex_l; [ exact Hb | ].
    rewrite <- HeqQs. apply ad_refine_syn_f__unit.
  - (* var / Q0 = var β, τ = var *)
    eapply ad_refine_syn_f__flex_l; [ exact Hb | ].
    rewrite <- HeqQs. apply ad_refine_syn_f__var; assumption.
  - (* var / Q0 = var x ≠ β *)
    inversion HeqQs; subst. apply ad_refine_syn_f__var; assumption.
  - (* arrow / Q0 = var β, τ arrow *)
    eapply ad_refine_syn_f__flex_l; [ exact Hb | ].
    rewrite <- HeqQs. apply ad_refine_syn_f__arrow; assumption.
  - (* arrow / Q0 = arrow *)
    inversion HeqQs; subst.
    apply ad_refine_syn_f__arrow;
      [ eapply IHad_refine_syn_f1; eauto
      | eapply IHad_refine_syn_f2; eauto ].
  - (* all_inh / Q0 = var β : a monotype painting is never a ∀ *)
    destruct τ0; simpl in HeqQs; discriminate.
  - (* all_inh / Q0 = all_inh *)
    inversion HeqQs; subst.
    apply ad_refine_syn_f__all with (L := L `union` {{β}}).
    intros X HX.
    match goal with
    | IH : forall X, X `notin` L -> _ |- _ =>
        eapply (IH X ltac:(clear - HX; fsetdec))
    end; [ exact Hb | exact Hm | ].
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      [ reflexivity
      | intro He; subst; clear - HX; fsetdec
      | apply mono_ptyp_to_bskl_syn_lc; exact Hm ].
  - (* hole / Q0 = var β *)
    destruct τ0; simpl in HeqQs; discriminate.
  - (* hole / Q0 = hole *)
    apply ad_refine_syn_f__hole; assumption.
  - (* tophole_remove / Q0 = var β *)
    destruct τ0; simpl in HeqQs; discriminate.
  - (* tophole_remove / Q0 = tophole *)
    inversion HeqQs; subst.
    apply ad_refine_syn_f__tophole_remove.
    eapply IHad_refine_syn_f; eauto.
  - (* tophole_fill / Q0 = var β *)
    destruct τ0; simpl in HeqQs; discriminate.
  - (* tophole_fill / Q0 = tophole *)
    inversion HeqQs; subst.
    apply ad_refine_syn_f__tophole_fill with (L := L `union` {{β}}).
    intros X HX.
    match goal with
    | IH : forall X, X `notin` L -> _ |- _ =>
        eapply (IH X ltac:(clear - HX; fsetdec))
    end; [ | exact Hm | simpl; reflexivity ].
    unfold binds. simpl. right. exact Hb.
  - (* tophole_keep / Q0 = var β *)
    destruct τ0; simpl in HeqQs; discriminate.
  - (* tophole_keep / Q0 = tophole *)
    inversion HeqQs; subst.
    apply ad_refine_syn_f__tophole_keep; [ assumption | ].
    eapply IHad_refine_syn_f; eauto.
  - (* flex_l / Q0 = var β : cap with the rebuilt lookup *)
    eapply ad_refine_syn_f__flex_l; [ exact Hb | ].
    rewrite <- HeqQs.
    eapply ad_refine_syn_f__flex_l; eassumption.
  - (* flex_l / Q0 = var x ≠ β : rebuild *)
    inversion HeqQs; subst.
    eapply ad_refine_syn_f__flex_l; eassumption.
  (* flex_r : the source is a rule variable — every Q0 shape survives;
     fold under the target lookup uniformly. *)
  - eapply ad_refine_syn_f__flex_r; [ eassumption | ];
      eapply IHad_refine_syn_f; [ exact Hb | exact Hm | ];
      simpl;
      try match goal with
          | |- context [ if ?e then _ else _ ] => destruct e
          end; congruence.
  - eapply ad_refine_syn_f__flex_r; [ eassumption | ];
      eapply IHad_refine_syn_f; [ exact Hb | exact Hm | ];
      simpl;
      try match goal with
          | |- context [ if ?e then _ else _ ] => destruct e
          end; congruence.
  - eapply ad_refine_syn_f__flex_r; [ eassumption | ];
      eapply IHad_refine_syn_f; [ exact Hb | exact Hm | ];
      simpl;
      try match goal with
          | |- context [ if ?e then _ else _ ] => destruct e
          end; congruence.
  - eapply ad_refine_syn_f__flex_r; [ eassumption | ];
      eapply IHad_refine_syn_f; [ exact Hb | exact Hm | ];
      simpl;
      try match goal with
          | |- context [ if ?e then _ else _ ] => destruct e
          end; congruence.
  - eapply ad_refine_syn_f__flex_r; [ eassumption | ];
      eapply IHad_refine_syn_f; [ exact Hb | exact Hm | ];
      simpl;
      try match goal with
          | |- context [ if ?e then _ else _ ] => destruct e
          end; congruence.
  - eapply ad_refine_syn_f__flex_r; [ eassumption | ];
      eapply IHad_refine_syn_f; [ exact Hb | exact Hm | ];
      simpl;
      try match goal with
          | |- context [ if ?e then _ else _ ] => destruct e
          end; congruence.
  - eapply ad_refine_syn_f__flex_r; [ eassumption | ];
      eapply IHad_refine_syn_f; [ exact Hb | exact Hm | ];
      simpl;
      try match goal with
          | |- context [ if ?e then _ else _ ] => destruct e
          end; congruence.
  - eapply ad_refine_syn_f__flex_r; [ eassumption | ];
      eapply IHad_refine_syn_f; [ exact Hb | exact Hm | ];
      simpl;
      try match goal with
          | |- context [ if ?e then _ else _ ] => destruct e
          end; congruence.
  - eapply ad_refine_syn_f__flex_r; [ eassumption | ];
      eapply IHad_refine_syn_f; [ exact Hb | exact Hm | ];
      simpl;
      try match goal with
          | |- context [ if ?e then _ else _ ] => destruct e
          end; congruence.
Qed.

(* ===================================================================== *)
(*  §7  Look decoration (lemma:look-decoration) and tags-sort existence   *)
(*                                                                        *)
(*  Every locally-closed skeleton [Q] admits a decoration [ψ]: a fresh    *)
(*  tag on every quantifier, ghosts turned dotted.  Stated with an        *)
(*  avoid-set [L] so sibling subtrees get disjoint tags (the arrow rule   *)
(*  of [d_tags_skl] needs [Ψ1 ∩ Ψ2 = ∅]) and so consumers can discharge   *)
(*  the cofinite tag-freshness premise of [a_subtag__forall_l_*].         *)
(*  (Moved here from prop_decorate_sub.v so prop_sub_sound can pick       *)
(*  decorations when instantiating the cofinite ForallL premise.)         *)
(* ===================================================================== *)

Lemma uskl_to_pskl_close_rec : forall ψ X k,
  uskl_to_pskl (close_uskl_wrt_uskl_rec k X ψ)
  = close_pskl_wrt_pskl_rec k X (uskl_to_pskl ψ).
Proof.
  induction ψ; intros X k; simpl; try (f_equal; auto; fail).
  - destruct (lt_ge_dec n k); reflexivity.
  - match goal with |- context [ if ?e then _ else _ ] => destruct e end;
      reflexivity.
Qed.

Lemma uskl_to_pskl_close : forall ψ X,
  ⌊ close_uskl_wrt_uskl X ψ ⌋ˢ = close_pskl_wrt_pskl X ⌊ ψ ⌋ˢ.
Proof.
  intros. unfold close_uskl_wrt_uskl, close_pskl_wrt_pskl.
  apply uskl_to_pskl_close_rec.
Qed.

Lemma is_tskl_lc : forall ψ, is_tskl ψ -> lc_uskl ψ.
Proof.
  intros ψ H; induction H; try (constructor; auto; fail).
  destruct (atom_fresh L) as [X HX].
  eapply lc_uskl_all_etag_exists; eauto.
Qed.

Lemma pskl_decorate_exists : forall Q,
  lc_pskl Q ->
  forall L, exists Ψ ψ,
    AtomSetImpl.inter Ψ L [=] empty /\
    is_tskl ψ /\
    d_tags_skl Ψ ψ /\
    ⌊ ψ ⌋ˢ = Q /\
    (pskl_ghost_free Q -> uskl_ghost_free ψ).
Proof.
  intros Q Hlc; induction Hlc; intros L.
  - (* unit *)
    exists empty, uskl_unit. repeat apply conj;
      [ fsetdec | apply is_tskl__unit | apply d_tags_skl__unit; fsetdec
      | reflexivity | intros _; apply uskl_ghost_free__unit ].
  - (* var *)
    exists empty, (uskl_var_f α). repeat apply conj;
      [ fsetdec | apply is_tskl__var | apply d_tags_skl__var; fsetdec
      | reflexivity | intros _; apply uskl_ghost_free__var ].
  - (* arrow *)
    destruct (IHHlc1 L) as [Ψ1 [ψ1 [Hd1 [Ht1 [Hg1 [He1 Hgf1]]]]]].
    destruct (IHHlc2 (L `union` Ψ1))
      as [Ψ2 [ψ2 [Hd2 [Ht2 [Hg2 [He2 Hgf2]]]]]].
    exists (Ψ1 `union` Ψ2), (uskl_arrow ψ1 ψ2). repeat apply conj.
    + clear - Hd1 Hd2. fsetdec.
    + apply is_tskl__arrow; assumption.
    + apply d_tags_skl__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
        [ assumption | assumption | clear - Hd2; fsetdec | fsetdec ].
    + simpl. rewrite He1, He2. reflexivity.
    + intros Hg. simpl in Hg. destruct Hg as [Hga Hgb].
      apply uskl_ghost_free__arrow; [ apply Hgf1; auto | apply Hgf2; auto ].
  - (* all_syn → all_etag ε *)
    destruct (atom_fresh (L `union` ftvar_in_pskl P1)) as [X0 FrX].
    destruct (H0 X0 (L `union` singleton X0))
      as [Ψ0 [ψ0 [Hd0 [Ht0 [Hg0 [He0 Hgf0]]]]]].
    destruct (atom_fresh (L `union` Ψ0)) as [ε Frε].
    exists (add ε Ψ0), (uskl_all_etag ε (close_uskl_wrt_uskl X0 ψ0)).
    repeat apply conj.
    + clear - Hd0 Frε. fsetdec.
    + apply is_tskl__all_etag with (L := singleton X0).
      intros Y HY.
      rewrite <- subst_bskl_in_uskl_spec.
      change (uskl_var_f Y) with (ptyp_to_uskl_syn (ptyp_var_f Y)).
      apply is_tskl_subst_mono; [ exact Ht0 | apply mono_ptyp__var ].
    + apply d_tags_skl__all_etag with (L := singleton X0) (Ψ0 := Ψ0);
        [ | clear - Frε; fsetdec | fsetdec ].
      intros Y HY.
      rewrite <- subst_bskl_in_uskl_spec.
      change (uskl_var_f Y) with (ptyp_to_uskl_syn (ptyp_var_f Y)).
      apply d_tags_skl_subst_mono; [ exact Hg0 | apply mono_ptyp__var ].
    + simpl. rewrite uskl_to_pskl_close. rewrite He0.
      rewrite close_pskl_wrt_pskl_open_pskl_wrt_pskl;
        [ reflexivity | clear - FrX; fsetdec ].
    + intros Hg. simpl in Hg.
      apply uskl_ghost_free__all_etag with (L := singleton X0).
      intros Y HY.
      rewrite <- subst_bskl_in_uskl_spec.
      change (uskl_var_f Y) with (ptyp_to_uskl_syn (ptyp_var_f Y)).
      apply uskl_ghost_free_subst_mono; [ | apply mono_ptyp__var ].
      apply Hgf0. unfold open_pskl_wrt_pskl. apply pskl_ghost_free_open_rec.
      exact Hg.
  - (* hole → holeg *)
    exists empty, uskl_holeg. repeat apply conj;
      [ fsetdec | apply is_tskl__holeg | apply d_tags_skl__holeg; fsetdec
      | reflexivity | intros Hg; simpl in Hg; contradiction ].
  - (* tophole → topholeg *)
    destruct (IHHlc L) as [Ψ0 [ψ0 [Hd0 [Ht0 [Hg0 [He0 Hgf0]]]]]].
    exists Ψ0, (uskl_topholeg ψ0). repeat apply conj.
    + exact Hd0.
    + apply is_tskl__topholeg; assumption.
    + apply d_tags_skl__topholeg; assumption.
    + simpl. rewrite He0. reflexivity.
    + intros Hg. simpl in Hg. contradiction.
Qed.

(** [ptyp]s have no ghosts, so [guess^TY] outputs are ghost-free. *)
Lemma ptyp_to_pskl_ghost_free : forall A, pskl_ghost_free (ptyp_to_pskl A).
Proof. induction A; simpl; auto. Qed.

Lemma a_extract_ty_ghost_free : forall α M P P0 Ξ P1,
  a_extract a_sub_mode_ty α M P P0 Ξ P1 ->
  pskl_ghost_free P1.
Proof.
  intros * Hex; inversion Hex; subst.
  match goal with
  | Hg : a_guess a_sub_mode_ty _ _ _ |- _ => inversion Hg; subst
  end.
  apply ptyp_to_pskl_ghost_free.
Qed.

(** Existence of a fresh [a_tags_sort]-sorted decoration of an extract
    output — what consumers instantiate the cofinite ForallL premise with.
    The TY case needs the output ghost-free, which [guess^TY] guarantees. *)
Lemma a_tags_sort_decorate_exists : forall NM α M P P0 Ξ P1,
  a_extract NM α M P P0 Ξ P1 ->
  lc_pskl P1 ->
  forall L, exists Ψg ψg,
    AtomSetImpl.inter Ψg L [=] empty /\
    a_tags_sort NM Ψg ψg /\
    ⌊ ψg ⌋ˢ = P1.
Proof.
  intros NM α M P P0 Ξ P1 Hex Hlc L.
  destruct (pskl_decorate_exists Hlc L)
    as [Ψg [ψg [Hint [Htskl [Hdtags [Herase Hgf]]]]]].
  exists Ψg, ψg. repeat apply conj; [ exact Hint | | exact Herase ].
  destruct NM.
  - apply a_tags_sort__ty; [ exact Htskl | exact Hdtags | ].
    apply Hgf. eapply a_extract_ty_ghost_free; eauto.
  - apply a_tags_sort__sk; [ exact Htskl | exact Hdtags ].
Qed.
