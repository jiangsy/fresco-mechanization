(** COMPLETENESS OF SKELETON INFERENCE (section D, thm:complete-skeleton-
    inference) — the landing file for theorem 3 and its kit.

    This file holds, so far, the two wf anchors the theorem's induction
    leans on (plan: memory `remech-theorem3-plan`):

    - [ad_pat_target_wf] (K1): a declarative skeleton-inference derivation's
      target erasure is well-formed — BOTTOM-UP, anchored by the
      counterpart-wf premise the three base rows carry (hand-off §5) and
      rebuilt by every composite row.  This is what replaces any top-down
      wf hypothesis on the completeness statement: theorem 3 derives the wf
      of ANY sub-derivation's solution target on demand (the App case's
      [inh ◇ ⊳ syn P] side conditions, the Sub case's counterpart wf).

    - [a_pat_output_wf] (K7): the ALGORITHM's run has a well-formed output
      — a corollary of theorem 1 + K1 (the App case feeds the function
      premise's question with the argument run's output). *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_extra.
Require Import src.frost.ltac_utils.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.decorated_algo.def_decorated.
Require Import src.frost.decorated_algo.def_decl_algo.
Require Import src.frost.decorated_algo.def_decl_algo_sub.
Require Import src.frost.decorated_algo.def_decl_algo_sub_hyg.
Require Import src.frost.decorated_algo.def_decl_algo_typing.
Require Import src.frost.decorated_algo.prop_ctx_mono.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_metasubst.
Require Import src.frost.algo.prop_inc_strengthen.
Require Import src.frost.algo.prop_compose.
Require Import src.frost.decorated_algo.prop_decorate.
Require Import src.frost.algo.prop_sub_msubst_equiv.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_completeness_consis.
Require Import src.frost.algo.prop_precise.
Require Import src.frost.algo.prop_consis_rename.
Require Import src.frost.algo.prop_soundness_consis.
Require Import src.frost.algo.prop_wf_output.
Require Import src.frost.algo.prop_soundness_pat.
Require Import src.frost.algo.prop_soundness_typing.

Set Implicit Arguments.

(* ===================================================================== *)
(*  K1 — a declarative skeleton-inference derivation's target is wf       *)
(*  (bottom-up: the base rows carry it, every composite row rebuilds it)  *)
(* ===================================================================== *)

Lemma ad_pat_target_wf : forall M Θ e Q,
  Θ ⊢ᵃ[ M ] e ⇨ Q ->
  a_wf_aenv Θ ->
  Θ ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q).
Proof.
  intros M Θ e Q H; induction H; intros Hwf.
  - (* unit : on the rule *) exact H.
  - (* var : on the rule *) exact H1.
  - (* anno : on the rule *) exact H0.
  - (* freeze *) apply IHad_pat; exact Hwf.
  - (* abs : arrow of the rule's wf P and the body's target *)
    destruct (atom_fresh (L `union` dom Θ)) as [x Hx].
    assert (Hwfx : a_wf_aenv ((x ~ abind_var_skl P) ++ Θ)).
    { apply a_wf_aenv__var;
        [ clear - Hx; fsetdec
        | eapply a_wf_pskl_to_a_scope_pskl;
            [ exact H0 | intros y b1 Hb1; exact Hb1
            | intros α Hα; exfalso; clear - Hα; fsetdec ]
        | exact Hwf ]. }
    pose proof (H3 x ltac:(clear - Hx; fsetdec) Hwfx) as HwfQ.
    simpl. apply a_wf_pskl__arrow.
    + rewrite bskl_to_pskl_pskl_to_bskl_inh. exact H0.
    + eapply a_wf_pskl_mono;
        [ exact HwfQ
        | apply (@aenv_tbinds_le_strip_tm nil x (abind_var_skl P) Θ);
          intros [] ].
  - (* abs_anno *)
    destruct (atom_fresh (L `union` dom Θ)) as [x Hx].
    assert (Hwfx : a_wf_aenv ((x ~ abind_var_typ A) ++ Θ)).
    { apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact H0 | exact Hwf ]. }
    pose proof (H4 x ltac:(clear - Hx; fsetdec) Hwfx) as HwfQ.
    simpl. apply a_wf_pskl__arrow.
    + rewrite bskl_to_pskl_btyp_to_bskl. rewrite H1.
      apply a_wf_ptyp_to_wf_pskl. exact H0.
    + eapply a_wf_pskl_mono;
        [ exact HwfQ
        | apply (@aenv_tbinds_le_strip_tm nil x (abind_var_typ A) Θ);
          intros [] ].
  - (* app : invert the function target's arrow *)
    pose proof (IHad_pat2 Hwf) as Hwfarr.
    simpl in Hwfarr.
    inversion Hwfarr as [ | | Θz Δz Pa Pb Hwa Hwb | | | ]; subst.
    exact Hwb.
  - (* abs_check : rebuild ⊤(◇ → body) *)
    destruct (atom_fresh (L `union` dom Θ)) as [x Hx].
    assert (Hwfx : a_wf_aenv ((x ~ abind_var_skl pskl_hole) ++ Θ)).
    { apply a_wf_aenv__var;
        [ clear - Hx; fsetdec | apply a_scope_pskl__hole | exact Hwf ]. }
    pose proof (H0 x ltac:(clear - Hx; fsetdec) Hwfx) as HwfQ.
    assert (HwfQ' : Θ ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl (pskl_to_bskl_syn P)))
      by (eapply a_wf_pskl_mono;
          [ exact HwfQ
          | apply (@aenv_tbinds_le_strip_tm nil x (abind_var_skl pskl_hole) Θ);
            intros [] ]).
    rewrite bskl_to_pskl_pskl_to_bskl_syn in HwfQ'.
    simpl. apply a_wf_pskl__tophole.
    + apply guarded_pskl__arrow;
        [ apply lc_pskl_hole | ].
      rewrite bskl_to_pskl_pskl_to_bskl_syn.
      eapply a_wf_pskl_lc; exact HwfQ'.
    + apply a_wf_pskl__arrow;
        [ apply a_wf_pskl__hole | ].
      rewrite bskl_to_pskl_pskl_to_bskl_syn. exact HwfQ'.
  - (* abs_anno_check *)
    destruct (atom_fresh (L `union` dom Θ)) as [x Hx].
    assert (Hwfx : a_wf_aenv ((x ~ abind_var_typ A) ++ Θ)).
    { apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact H | exact Hwf ]. }
    pose proof (H1 x ltac:(clear - Hx; fsetdec) Hwfx) as HwfQ.
    assert (HwfQ' : Θ ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl (pskl_to_bskl_syn P)))
      by (eapply a_wf_pskl_mono;
          [ exact HwfQ
          | apply (@aenv_tbinds_le_strip_tm nil x (abind_var_typ A) Θ);
            intros [] ]).
    rewrite bskl_to_pskl_pskl_to_bskl_syn in HwfQ'.
    assert (HwfpA : Θ ⨟ empty ⊢ₚₛᵃ (ptyp_to_pskl A))
      by (apply a_wf_ptyp_to_wf_pskl; exact H).
    simpl. apply a_wf_pskl__tophole.
    + apply guarded_pskl__arrow;
        [ eapply a_wf_pskl_lc;
          rewrite btyp_to_bskl_ptyp_to_btyp_syn,
                  bskl_to_pskl_pskl_to_bskl_syn; exact HwfpA
        | rewrite bskl_to_pskl_pskl_to_bskl_syn;
          eapply a_wf_pskl_lc; exact HwfQ' ].
    + apply a_wf_pskl__arrow;
        [ rewrite btyp_to_bskl_ptyp_to_btyp_syn,
                  bskl_to_pskl_pskl_to_bskl_syn; exact HwfpA
        | rewrite bskl_to_pskl_pskl_to_bskl_syn; exact HwfQ' ].
Qed.

(* ===================================================================== *)
(*  K7 — the ALGORITHM's skeleton-inference output is wf: a corollary of  *)
(*  theorem 1 (the run's decorated image) and K1 (its target is wf).      *)
(* ===================================================================== *)

Corollary a_pat_output_wf : forall m Θ0 P0 e P Θ1,
  Θ0 ⊢ₐ[ m ; P0 ] e ⇨ P ⊣ Θ1 ->
  a_wf_aenv Θ0 ->
  (forall x Ps, binds x (abind_var_skl Ps) Θ0 -> Θ0 ⨟ empty ⊢ₚₛᵃ Ps) ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  a_sk_mode_compat m P0 ->
  a_wf_exp Θ0 e ->
  Θ1 ⨟ empty ⊢ₚₛᵃ P.
Proof.
  intros * Hrun Hwf Hskl HwfP0 Hmod Hexp.
  destruct (a_pat_sound Hrun Hwf Hskl HwfP0 Hmod Hexp)
    as [Hle [Hwf1 [Qt [HeQt [Hpat _]]]]].
  rewrite <- HeQt. eapply ad_pat_target_wf; [ exact Hpat | exact Hwf1 ].
Qed.

(* ===================================================================== *)
(*  K2 — reverse term-entry lookups along an information increase (the    *)
(*  Var case reads the SOLUTION context's entry; the run subtypes the     *)
(*  QUESTION context's, and [a_inc]'s term rows relate them only up to    *)
(*  the equational theory).                                               *)
(* ===================================================================== *)

(* A pending suffix carries no term entry. *)
Lemma a_suffix_no_var_skl : forall Ξ x (P : pskl),
  a_suffix Ξ -> binds x (abind_var_skl P) Ξ -> False.
Proof.
  intros Ξ x P H; induction H; intros Hb; [ inversion Hb | ].
  destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heq] | Hb'];
    [ subst; inversion H0 | auto ].
Qed.

Lemma a_suffix_no_var_typ : forall Ξ x (A : ptyp),
  a_suffix Ξ -> binds x (abind_var_typ A) Ξ -> False.
Proof.
  intros Ξ x A H; induction H; intros Hb; [ inversion Hb | ].
  destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heq] | Hb'];
    [ subst; inversion H0 | auto ].
Qed.

(** A skeleton entry's payload is scoped in the WHOLE context (its own
    tail suffices, so a fortiori). *)
Lemma a_wf_aenv_binds_var_skl_ftv : forall Θ x (P : pskl),
  a_wf_aenv Θ ->
  binds x (abind_var_skl P) Θ ->
  ftvar_in_pskl P [<=] dom Θ.
Proof.
  intros Θ x P H; induction H; intros Hb; try solve [ inversion Hb ];
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> Heq] | Hb'];
    try discriminate Heq; simpl;
    try solve [ pose proof (IHa_wf_aenv Hb'); fsetdec ].
  inversion Heq; subst.
  pose proof (a_scope_pskl_ftv_dom' H0). fsetdec.
Qed.

Lemma a_wf_aenv_binds_var_typ_ftv : forall Θ x (A : ptyp),
  a_wf_aenv Θ ->
  binds x (abind_var_typ A) Θ ->
  ftvar_in_ptyp A [<=] dom Θ.
Proof.
  intros Θ x A H; induction H; intros Hb; try solve [ inversion Hb ];
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> Heq] | Hb'];
    try discriminate Heq; simpl;
    try solve [ pose proof (IHa_wf_aenv Hb'); fsetdec ].
  inversion Heq; subst.
  pose proof (a_wf_ptyp_ftv_dom H0) as Hs. simpl. clear - Hs. fsetdec.
Qed.

(** ⭐ K2 — the Θ-side term entry of an increase comes from a Θ0-side one,
    with the payloads related by the equational theory under the FULL κ.
    The flex rows shrink κ, which is harmless because the source tail's
    payloads cannot mention the peeled flexible (wf-ordering). *)
Lemma a_inc_binds_var_skl_rev : forall Θ0 κ Θ x (P : pskl),
  κ ∷ Θ0 ⊑ Θ ->
  a_wf_aenv Θ0 ->
  binds x (abind_var_skl P) Θ ->
  exists P0,
    binds x (abind_var_skl P0) Θ0 /\
    Θ ⊢ P ≡ˢ (msubst_pskl κ P0).
Proof.
  intros Θ0 κ Θ x P Hinc; induction Hinc; intros Hwf Hb.
  - (* empty : the target is a pure suffix *)
    exfalso; eapply a_suffix_no_var_skl; eassumption.
  - (* flex : target unchanged, κ gains (α,τ) — the payload is α-free *)
    inversion Hwf as [ | αz Θz Hα Hwf0 | | | | ]; subst.
    destruct (IHHinc Hwf0 Hb) as [P0 [Hb0 Heq]].
    exists P0. split; [ apply binds_cons_3; exact Hb0 | ].
    assert (Hfr : α `notin` ftvar_in_pskl P0).
    { pose proof (@a_wf_aenv_binds_var_skl_ftv _ _ _ Hwf0 Hb0) as Hs.
      clear - Hs Hα. fsetdec. }
    replace ((α, τ) :: κ) with (nil ++ ((α, τ) :: nil) ++ κ)
      by reflexivity.
    rewrite msubst_pskl_mid_skip;
      [ exact Heq
      | intros α0 Hα0; simpl in Hα0;
        assert (α0 = α) by (clear - Hα0; fsetdec); subst; exact Hfr ].
  - (* flex_def : same shape *)
    inversion Hwf as [ | | αz τz Θz Hα Hwfτ Hmz Hwf0 | | | ]; subst.
    destruct (IHHinc Hwf0 Hb) as [P0 [Hb0 Heq]].
    exists P0. split; [ apply binds_cons_3; exact Hb0 | ].
    assert (Hfr : α `notin` ftvar_in_pskl P0).
    { pose proof (@a_wf_aenv_binds_var_skl_ftv _ _ _ Hwf0 Hb0) as Hs.
      clear - Hs Hα. fsetdec. }
    replace ((α, τ') :: κ) with (nil ++ ((α, τ') :: nil) ++ κ)
      by reflexivity.
    rewrite msubst_pskl_mid_skip;
      [ exact Heq
      | intros α0 Hα0; simpl in Hα0;
        assert (α0 = α) by (clear - Hα0; fsetdec); subst; exact Hfr ].
  - (* var (type entry) : x may be THIS entry (wrong sort) or below *)
    inversion Hwf as [ | | | | xz Az Θz Hx HwfA Hwf0 | ]; subst.
    apply binds_app_1 in Hb as [Hb | Hb];
      [ exfalso; eapply a_suffix_no_var_skl; eassumption | ].
    apply binds_app_1 in Hb as [Hb | Hb].
    + destruct Hb as [Hp | []]. inversion Hp.
    + destruct (IHHinc Hwf0 Hb) as [P0 [Hb0 Heq]].
      exists P0. split; [ apply binds_cons_3; exact Hb0 | ].
      eapply a_pskl_tyequiv_weaken;
        [ intros y c Hc; apply binds_app_3; apply binds_cons_3; exact Hc
        | exact Heq ].
  - (* var_skl : the entry itself, or below *)
    inversion Hwf as [ | | | xz Pz Θz Hx Hsc Hwf0 | | ]; subst.
    apply binds_app_1 in Hb as [Hb | Hb];
      [ exfalso; eapply a_suffix_no_var_skl; eassumption | ].
    apply binds_app_1 in Hb as [Hb | Hb].
    + destruct Hb as [Hp | []]. inversion Hp; subst.
      eexists. split; [ unfold binds; simpl; left; reflexivity | ].
      eapply a_pskl_tyequiv_weaken;
        [ intros y c Hc; apply binds_app_3; apply binds_cons_3; exact Hc
        | exact H ].
    + destruct (IHHinc Hwf0 Hb) as [P1 [Hb0 Heq]].
      exists P1. split; [ apply binds_cons_3; exact Hb0 | ].
      eapply a_pskl_tyequiv_weaken;
        [ intros y c Hc; apply binds_app_3; apply binds_cons_3; exact Hc
        | exact Heq ].
  - (* tvar *)
    inversion Hwf as [ | | | | | αz Θz Hα Hwf0 ]; subst.
    apply binds_app_1 in Hb as [Hb | Hb];
      [ exfalso; eapply a_suffix_no_var_skl; eassumption | ].
    apply binds_app_1 in Hb as [Hb | Hb].
    + destruct Hb as [Hp | []]. inversion Hp.
    + destruct (IHHinc Hwf0 Hb) as [P0 [Hb0 Heq]].
      exists P0. split; [ apply binds_cons_3; exact Hb0 | ].
      eapply a_pskl_tyequiv_weaken;
        [ intros y c Hc; apply binds_app_3; apply binds_cons_3; exact Hc
        | exact Heq ].
Qed.

(** The type-entry mirror, at [≡ᵗ]. *)
Lemma a_inc_binds_var_typ_rev : forall Θ0 κ Θ x (A : ptyp),
  κ ∷ Θ0 ⊑ Θ ->
  a_wf_aenv Θ0 ->
  binds x (abind_var_typ A) Θ ->
  exists A0,
    binds x (abind_var_typ A0) Θ0 /\
    Θ ⊢ A ≡ᵗ (msubst_ptyp κ A0).
Proof.
  intros Θ0 κ Θ x A Hinc; induction Hinc; intros Hwf Hb.
  - exfalso; eapply a_suffix_no_var_typ; eassumption.
  - (* flex *)
    inversion Hwf as [ | αz Θz Hα Hwf0 | | | | ]; subst.
    destruct (IHHinc Hwf0 Hb) as [A0 [Hb0 Heq]].
    exists A0. split; [ apply binds_cons_3; exact Hb0 | ].
    assert (Hfr : α `notin` ftvar_in_ptyp A0).
    { pose proof (@a_wf_aenv_binds_var_typ_ftv _ _ _ Hwf0 Hb0) as Hs.
      clear - Hs Hα. fsetdec. }
    rewrite msubst_ptyp_cons_notin; [ exact Heq | exact Hfr ].
  - (* flex_def *)
    inversion Hwf as [ | | αz τz Θz Hα Hwfτ Hmz Hwf0 | | | ]; subst.
    destruct (IHHinc Hwf0 Hb) as [A0 [Hb0 Heq]].
    exists A0. split; [ apply binds_cons_3; exact Hb0 | ].
    assert (Hfr : α `notin` ftvar_in_ptyp A0).
    { pose proof (@a_wf_aenv_binds_var_typ_ftv _ _ _ Hwf0 Hb0) as Hs.
      clear - Hs Hα. fsetdec. }
    rewrite msubst_ptyp_cons_notin; [ exact Heq | exact Hfr ].
  - (* var (type entry) : the entry itself, or below *)
    inversion Hwf as [ | | | | xz Az Θz Hx HwfA Hwf0 | ]; subst.
    apply binds_app_1 in Hb as [Hb | Hb];
      [ exfalso; eapply a_suffix_no_var_typ; eassumption | ].
    apply binds_app_1 in Hb as [Hb | Hb].
    + destruct Hb as [Hp | []]. inversion Hp; subst.
      eexists. split; [ unfold binds; simpl; left; reflexivity | ].
      eapply a_tyequiv_weaken;
        [ intros y c Hc; apply binds_app_3; apply binds_cons_3; exact Hc
        | exact H ].
    + destruct (IHHinc Hwf0 Hb) as [A1 [Hb0 Heq]].
      exists A1. split; [ apply binds_cons_3; exact Hb0 | ].
      eapply a_tyequiv_weaken;
        [ intros y c Hc; apply binds_app_3; apply binds_cons_3; exact Hc
        | exact Heq ].
  - (* var_skl : wrong sort at the entry, or below *)
    inversion Hwf as [ | | | xz Pz Θz Hx Hsc Hwf0 | | ]; subst.
    apply binds_app_1 in Hb as [Hb | Hb];
      [ exfalso; eapply a_suffix_no_var_typ; eassumption | ].
    apply binds_app_1 in Hb as [Hb | Hb].
    + destruct Hb as [Hp | []]. inversion Hp.
    + destruct (IHHinc Hwf0 Hb) as [A0 [Hb0 Heq]].
      exists A0. split; [ apply binds_cons_3; exact Hb0 | ].
      eapply a_tyequiv_weaken;
        [ intros y c Hc; apply binds_app_3; apply binds_cons_3; exact Hc
        | exact Heq ].
  - (* tvar *)
    inversion Hwf as [ | | | | | αz Θz Hα Hwf0 ]; subst.
    apply binds_app_1 in Hb as [Hb | Hb];
      [ exfalso; eapply a_suffix_no_var_typ; eassumption | ].
    apply binds_app_1 in Hb as [Hb | Hb].
    + destruct Hb as [Hp | []]. inversion Hp.
    + destruct (IHHinc Hwf0 Hb) as [A0 [Hb0 Heq]].
      exists A0. split; [ apply binds_cons_3; exact Hb0 | ].
      eapply a_tyequiv_weaken;
        [ intros y c Hc; apply binds_app_3; apply binds_cons_3; exact Hc
        | exact Heq ].
Qed.

(* ===================================================================== *)
(*  K3a — the ≡ˢ→≡ᵘ painting bridge (the Var case's slack subject)        *)
(* ===================================================================== *)

(** K3a — a skeleton equivalence between two pskls lifts to their
    synthesised paintings.  The flex-def retrieval row lands in [≡ᵘ]'s one
    semantic row ([__mono] — a variable IS the painting of a mono type). *)
Lemma a_pskl_tyequiv_to_uskl : forall Θ P Q,
  Θ ⊢ P ≡ˢ Q ->
  a_wf_aenv Θ ->
  Θ ⊢ (pskl_to_uskl P) ≡ᵘ (pskl_to_uskl Q).
Proof.
  intros Θ P Q H; induction H; intros Hwf.
  - (* refl *)
    apply a_uskl_tyequiv_refl. apply pskl_to_uskl_lc. exact H.
  - (* sym *)
    apply a_uskl_tyequiv_sym. auto.
  - (* trans *)
    eapply a_uskl_tyequiv_trans; auto.
  - (* flex_def : α ≡ˢ ⌊τ⌋, i.e. two mono paintings *)
    assert (Hm : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; eassumption).
    change (pskl_to_uskl (pskl_var_f α))
      with (ptyp_to_uskl_syn (ptyp_var_f α)).
    rewrite pskl_to_uskl_ptyp.
    apply a_uskl_tyequiv__mono;
      [ apply mono_ptyp__var
      | exact Hm
      | apply a_wf_ptyp__var; right; right; eauto
      | eapply a_wf_aenv_binds_def_wf; eassumption
      | apply a_tyequiv__flex_def; exact H ].
  - (* arrow *)
    simpl. apply a_uskl_tyequiv__arrow; auto.
  - (* all *)
    simpl. apply a_uskl_tyequiv__all_syn with (L := L).
    intros α Hα.
    rewrite <- !pskl_to_uskl_open_var.
    apply H0; [ exact Hα | exact Hwf ].
  - (* tophole *)
    simpl. apply a_uskl_tyequiv__tophole. auto.
Qed.

(* ===================================================================== *)
(*  K3b — the three BASE rows' SLACK premises.                           *)
(*                                                                       *)
(*  [a_sub_complete_thm] takes its subject up to [≡ᵘ] slack              *)
(*  ([Θ ⊢ R' ≡ᵘ κ⌈P⌉ᵘ], prop_completeness_sub.v) precisely because the    *)
(*  QUESTION context's entry and the SOLUTION context's are related only  *)
(*  semantically.  Here are the three instances theorem 3 needs:          *)
(*                                                                       *)
(*  - [P-Unit]: reflexive (a constant is a metasubstitution fixpoint).    *)
(*  - [P-Var]: K2's entry equivalence IS the slack — no side condition.   *)
(*  - [P-Anno]: ⭐ reflexive TOO, but for a reason worth stating: an      *)
(*    annotation is SOURCE syntax, so its free type variables are RIGID,  *)
(*    and [a_inc]'s domain is exactly the source context's FLEXIBLES      *)
(*    ([a_inc_dom_flex]) — so the metasubstitution cannot touch it.       *)
(*    That rigidity is the paper's own reading of an annotation and the   *)
(*    ONE side condition theorem 3 carries about the term.                *)
(* ===================================================================== *)

(* --- the painting / metasubstitution commutes ------------------------- *)

Lemma msubst_pskl_to_uskl : forall κ P,
  pskl_to_uskl (msubst_pskl κ P) = msubst_uskl_syn κ (pskl_to_uskl P).
Proof.
  intros κ P; induction P; simpl; f_equal; auto.
  apply pskl_to_uskl_ptyp.
Qed.

Lemma msubst_ptyp_to_uskl_syn : forall κ A,
  ptyp_to_uskl_syn (msubst_ptyp κ A) = msubst_uskl_syn κ (ptyp_to_uskl_syn A).
Proof.
  intros κ A.
  rewrite <- !pskl_to_uskl_ptyp, <- msubst_pskl_to_uskl.
  f_equal. induction A; simpl; f_equal; auto.
Qed.

(* --- ≡ᵗ lifts to the paintings (the ptyp twin of [a_pskl_tyequiv_to_uskl]) *)

(** The painting's two structural equations, folded (the composite
    [bskl_to_uskl ∘ pskl_to_bskl_syn ∘ ptyp_to_pskl] is structural, so both
    hold by [reflexivity] — they exist only to keep [ptyp_to_uskl_syn]
    FOLDED, which is what the [_open] rewrite matches on). *)
Lemma ptyp_to_uskl_syn_arrow : forall A B,
  ptyp_to_uskl_syn (ptyp_arrow A B)
  = uskl_arrow (ptyp_to_uskl_syn A) (ptyp_to_uskl_syn B).
Proof. reflexivity. Qed.

Lemma ptyp_to_uskl_syn_all : forall A,
  ptyp_to_uskl_syn (ptyp_all A) = uskl_all_syn (ptyp_to_uskl_syn A).
Proof. reflexivity. Qed.

Lemma a_tyequiv_to_uskl : forall Θ A B,
  Θ ⊢ A ≡ᵗ B ->
  a_wf_aenv Θ ->
  Θ ⊢ (ptyp_to_uskl_syn A) ≡ᵘ (ptyp_to_uskl_syn B).
Proof.
  intros Θ A B H; induction H; intros Hwf.
  - (* refl *)
    apply a_uskl_tyequiv_refl.
    rewrite <- pskl_to_uskl_ptyp. apply pskl_to_uskl_lc.
    apply lc_ptyp_to_pskl. exact H.
  - (* sym *) apply a_uskl_tyequiv_sym; auto.
  - (* trans *) eapply a_uskl_tyequiv_trans; auto.
  - (* flex_def : a variable against its MONO definition *)
    assert (Hm : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; eassumption).
    apply a_uskl_tyequiv__mono;
      [ apply mono_ptyp__var
      | exact Hm
      | apply a_wf_ptyp__var; right; right; eauto
      | eapply a_wf_aenv_binds_def_wf; eassumption
      | apply a_tyequiv__flex_def; exact H ].
  - (* arrow *)
    rewrite !ptyp_to_uskl_syn_arrow.
    apply a_uskl_tyequiv__arrow; auto.
  - (* all *)
    rewrite !ptyp_to_uskl_syn_all.
    apply a_uskl_tyequiv__all_syn with (L := L).
    intros α Hα.
    rewrite <- !ptyp_to_uskl_syn_open.
    apply H0; [ exact Hα | exact Hwf ].
Qed.

(* --- the three base rows' SLACK premises ------------------------------ *)

(** ⭐ A RIGID variable of the question context is untouched by any
    solution's metasubstitution: [a_inc]'s domain is exactly the source's
    FLEXIBLES ([a_inc_dom_flex]). *)
Lemma a_inc_rigid_notin_dom : forall Θ0 κ Θ α,
  κ ∷ Θ0 ⊑ Θ ->
  a_wf_aenv Θ0 ->
  binds α abind_tvar Θ0 ->
  α `notin` dom κ.
Proof.
  intros Θ0 κ Θ α Hinc Hwf Hb Hin.
  destruct (a_inc_dom_flex Hinc Hin) as [Hf | [τ Hf]];
    pose proof (binds_unique _ _ _ _ _ Hb Hf (a_wf_aenv_uniq Hwf)) as Hc;
    discriminate Hc.
Qed.

(** …hence a type all of whose free variables are rigid is a FIXPOINT of
    the metasubstitution.  This is what makes [P-Anno]'s slack REFLEXIVE:
    an annotation is SOURCE syntax, so it cannot mention a flexible the
    algorithm invented (docs/PAPER-GAPS.md). *)
Lemma msubst_ptyp_rigid_id : forall Θ0 κ Θ A,
  κ ∷ Θ0 ⊑ Θ ->
  a_wf_aenv Θ0 ->
  (forall α, α `in` ftvar_in_ptyp A -> binds α abind_tvar Θ0) ->
  msubst_ptyp κ A = A.
Proof.
  intros Θ0 κ Θ A Hinc Hwf Hrig.
  apply msubst_ptyp_notin. intros α Hα.
  eapply a_inc_rigid_notin_dom; [ exact Hinc | exact Hwf | apply Hrig; exact Hα ].
Qed.

(** [P-Unit]'s slack. *)
Lemma slack_unit : forall Θ κ,
  Θ ⊢ uskl_unit ≡ᵘ (msubst_uskl_syn κ (pskl_to_uskl pskl_unit)).
Proof. intros. simpl. apply a_uskl_tyequiv__unit. Qed.

(** [P-Anno]'s slack — reflexive, by the fixpoint above.  [lc_ptyp A] comes
    from the declarative rule's own [a_wf_ptyp Θ A]. *)
Lemma slack_anno : forall Θ0 κ Θ A,
  κ ∷ Θ0 ⊑ Θ ->
  a_wf_aenv Θ0 ->
  lc_ptyp A ->
  (forall α, α `in` ftvar_in_ptyp A -> binds α abind_tvar Θ0) ->
  Θ ⊢ (ptyp_to_uskl_syn A)
    ≡ᵘ (msubst_uskl_syn κ (pskl_to_uskl (ptyp_to_pskl A))).
Proof.
  intros Θ0 κ Θ A Hinc Hwf Hlc Hrig.
  rewrite pskl_to_uskl_ptyp, <- msubst_ptyp_to_uskl_syn.
  rewrite (@msubst_ptyp_rigid_id Θ0 κ Θ A Hinc Hwf Hrig).
  apply a_uskl_tyequiv_refl.
  rewrite <- pskl_to_uskl_ptyp. apply pskl_to_uskl_lc.
  apply lc_ptyp_to_pskl. exact Hlc.
Qed.

(** ⭐ [P-Var]'s slack — NO side condition: the entry's own equivalence,
    handed over by K2, IS the slack.  The two [abind] term forms are
    unified through [abind_to_pskl], as in the rule. *)
Lemma slack_var : forall Θ0 κ Θ x (b : abind) (P : pskl),
  κ ∷ Θ0 ⊑ Θ ->
  a_wf_aenv Θ0 -> a_wf_aenv Θ ->
  binds x b Θ ->
  abind_to_pskl b = Some P ->
  exists (b0 : abind) (P0 : pskl),
    binds x b0 Θ0 /\ abind_to_pskl b0 = Some P0 /\
    Θ ⊢ (pskl_to_uskl P) ≡ᵘ (msubst_uskl_syn κ (pskl_to_uskl P0)).
Proof.
  intros Θ0 κ Θ x b P Hinc Hwf0 HwfΘ Hb HP.
  destruct b; simpl in HP; try discriminate HP.
  - (* type entry *)
    inversion HP; subst.
    destruct (@a_inc_binds_var_typ_rev Θ0 κ Θ x _ Hinc Hwf0 Hb) as [A0 [Hb0 Heq]].
    exists (abind_var_typ A0), (ptyp_to_pskl A0).
    split; [ exact Hb0 | ]. split; [ reflexivity | ].
    rewrite !pskl_to_uskl_ptyp, <- msubst_ptyp_to_uskl_syn.
    apply a_tyequiv_to_uskl; [ exact Heq | exact HwfΘ ].
  - (* skeleton entry *)
    inversion HP; subst.
    destruct (@a_inc_binds_var_skl_rev Θ0 κ Θ x _ Hinc Hwf0 Hb) as [P0 [Hb0 Heq]].
    exists (abind_var_skl P0), P0.
    split; [ exact Hb0 | ]. split; [ reflexivity | ].
    rewrite <- msubst_pskl_to_uskl.
    apply a_pskl_tyequiv_to_uskl; [ exact Heq | exact HwfΘ ].
Qed.
