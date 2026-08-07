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
Require Import src.frost.algo.prop_swap.
Require Import src.frost.algo.prop_completeness_sub.
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

(* ===================================================================== *)
(*  K4 — erasing a term entry from BOTH sides of an increase (the paper's *)
(*  "by erasing the term variable from ⓒ and ⓕ": the four binder rows     *)
(*  apply the IH at a context extended by the binder on both sides, and   *)
(*  the conclusion needs it gone from both).                              *)
(* ===================================================================== *)

(** Stripping a TERM entry never disturbs a type's well-formedness — the
    entry is not [a_binds_tvar]. *)
Lemma a_wf_ptyp_strip_tm_head : forall x (b : abind) Θ A,
  ~ abind_is_ty b ->
  a_wf_ptyp ((x ~ b) ++ Θ) A ->
  a_wf_ptyp Θ A.
Proof.
  intros x b Θ A Hty Hwa.
  eapply a_wf_ptyp_mono;
    [ exact Hwa | apply (@aenv_tbinds_le_strip_tm nil x b Θ); exact Hty ].
Qed.

(** ⭐ K4 — the paper's "by erasing the term variable from ⓒ and ⓕ"
    (proofs.tex, the Abs / AbsCheck / AbsAnno / AbsAnnoCheck cases).  The
    IH is applied at a context extended by the binder on BOTH sides; the
    conclusion needs it gone from both.

    The suffix [Ξ] the run deposits is what makes this an induction rather
    than an inversion: its flexible DECLARATIONS re-attach above the
    stripped entry (their images stay well-formed because a term entry is
    never a type variable), and its DEFINITIONS additionally re-attach an
    equational premise, strengthened across the entry by
    [a_tyequiv_strengthen_mono_mid]. *)
Lemma a_inc_strip_tm_head : forall Ξ x (b b' : abind) Θ1 κ Θ,
  a_suffix Ξ ->
  ~ abind_is_ty b -> ~ abind_is_ty b' ->
  a_wf_aenv (Ξ ++ (x ~ b) ++ Θ1) ->
  a_wf_aenv ((x ~ b') ++ Θ) ->
  κ ∷ (Ξ ++ (x ~ b) ++ Θ1) ⊑ ((x ~ b') ++ Θ) ->
  κ ∷ (Ξ ++ Θ1) ⊑ Θ.
Proof.
  induction Ξ as [ | [α bΞ] Ξ' IH ];
    intros x b b' Θ1 κ Θ Hsuf Htm Htm' HwfS HwfT Hinc; simpl_env in *.
  - (* no suffix : the increase's head rule IS the entry's *)
    destruct b; simpl in Htm; try solve [ exfalso; apply Htm; exact I ].
    + (* type entry *)
      destruct (a_inc_var_inv Hinc) as [Ξ2 [A' [Θ2 [Heq [Heqv [Hsuf2 Hrest]]]]]].
      destruct Ξ2 as [ | [y c] Ξ2' ]; simpl_env in Heq.
      * inversion Heq; subst. exact Hrest.
      * (* a suffix entry cannot be the target's TERM head *)
        exfalso. inversion Heq; subst.
        inversion Hsuf2 as [ | ? ? ? ? Hbind ]; subst.
        apply Htm'. destruct Hbind; exact I.
    + (* skeleton entry *)
      destruct (a_inc_var_skl_inv Hinc)
        as [Ξ2 [P' [Θ2 [Heq [Heqv [Hsuf2 Hrest]]]]]].
      destruct Ξ2 as [ | [y c] Ξ2' ]; simpl_env in Heq.
      * inversion Heq; subst. exact Hrest.
      * exfalso. inversion Heq; subst.
        inversion Hsuf2 as [ | ? ? ? ? Hbind ]; subst.
        apply Htm'. destruct Hbind; exact I.
  - (* a suffix entry : re-attach it above the stripped target *)
    inversion Hsuf as [ | ? ? ? Hsuf' Hbind ]; subst.
    (* the suffix's binding is FLEXIBLE — split on that first, so the two
       [inversion]s below face a known head shape *)
    destruct Hbind as [ | τz ].
    + (* flexible declaration *)
      inversion HwfS as [ | αz Θz HαS HwfS' | | | | ]; subst.
      inversion Hinc as [ | Θq κq Θtq αq τq Hrest Hwfτ Hmτ
                        | | | | ]; subst.
      apply a_inc__flex;
        [ eapply IH;
            [ exact Hsuf' | exact Htm | exact Htm' | exact HwfS' | exact HwfT
            | exact Hrest ]
        | eapply a_wf_ptyp_strip_tm_head; [ exact Htm' | exact Hwfτ ]
        | exact Hmτ ].
    + (* flexible definition *)
      inversion HwfS as [ | | αz τw Θz HαS HwfτS HmτS HwfS' | | | ]; subst.
      inversion Hinc as [ | | Θq κq Θtq αq τq τ'q Hrest Hwfτ' Hmτ' Heqv
                        | | | ]; subst.
      assert (Hrec : κq ∷ (Ξ' ++ Θ1) ⊑ Θ)
        by (eapply IH;
              [ exact Hsuf' | exact Htm | exact Htm' | exact HwfS' | exact HwfT
              | exact Hrest ]).
      assert (Hwfτ0 : a_wf_ptyp (Ξ' ++ Θ1) τz).
      { eapply a_wf_ptyp_mono;
          [ exact HwfτS
          | apply (@aenv_tbinds_le_strip_tm Ξ' x b Θ1); exact Htm ]. }
      apply a_inc__flex_def;
        [ exact Hrec
        | eapply a_wf_ptyp_strip_tm_head; [ exact Htm' | exact Hwfτ' ]
        | exact Hmτ'
        | ].
      (* the equational premise, strengthened across the stripped entry *)
      eapply (@a_tyequiv_strengthen_mono_mid nil x b' Θ);
        [ simpl_env; exact HwfT
        | eapply a_wf_ptyp_strip_tm_head; [ exact Htm' | exact Hwfτ' ]
        | exact Hmτ'
        | eapply a_wf_ptyp_msubst;
            [ exact Hwfτ0 | eapply a_wf_aenv_strip_tm_mid; [ exact Htm | exact HwfS' ]
            | exact Hrec ]
        | apply msubst_ptyp_mono_pointwise;
            [ intros β; eapply a_inc_lookup_mono; exact Hrec | exact HmτS ]
        | simpl_env; exact Heqv ].
Qed.

(** The identity-increase companion: [⊴] loses a term entry the same way.
    ([a_isub] is [a_inc] at an identity witness plus the definition-
    preservation component, which a strip cannot disturb.) *)
Lemma a_isub_strip_tm_head : forall Ξ x (b b' : abind) Θ1 Θ,
  a_suffix Ξ ->
  ~ abind_is_ty b -> ~ abind_is_ty b' ->
  a_wf_aenv (Ξ ++ (x ~ b) ++ Θ1) ->
  a_wf_aenv ((x ~ b') ++ Θ) ->
  (Ξ ++ (x ~ b) ++ Θ1) ⊴ ((x ~ b') ++ Θ) ->
  (Ξ ++ Θ1) ⊴ Θ.
Proof.
  intros Ξ x b b' Θ1 Θ Hsuf Htm Htm' HwfS HwfT [[κ [Hid Hinc]] Hdefs].
  split.
  - exists κ. split; [ exact Hid | ].
    eapply (@a_inc_strip_tm_head Ξ x b b' Θ1 κ Θ); assumption.
  - intros α τ Hb.
    assert (Hb' : binds α (abind_flex_mono_def τ) (Ξ ++ (x ~ b) ++ Θ1))
      by (apply binds_app_1 in Hb as [Hb | Hb];
          [ apply binds_app_2; exact Hb
          | apply binds_app_3; apply binds_cons_3; exact Hb ]).
    pose proof (Hdefs α τ Hb') as Hbt.
    destruct (binds_cons_1 _ _ _ _ _ _ Hbt) as [[_ Heq] | Hbt'];
      [ subst; exfalso; apply Htm'; exact I | exact Hbt' ].
Qed.

(* ===================================================================== *)
(*  THEOREM 3, the THREE BASE ROWS.                                      *)
(*                                                                       *)
(*  ⭐ The mech FUSED the paper's [P-Sub] into these rows, so each is     *)
(*  exactly ONE invocation of thm:complete-subtyping at the row's own     *)
(*  subject — no separate Sub case, and no lexicographic measure (every   *)
(*  recursive premise of the remaining rows is at a strict subterm).      *)
(*  What each needs beyond the run: the counterpart's wf, which the rule  *)
(*  now CARRIES (hand-off §5), and the subject slack, which is K3b.       *)
(* ===================================================================== *)

(** Erasing a metasubstituted painting is the metasubstitution of the
    erasure — the bridge between [a_sub_complete_thm]'s bskl-shaped
    precision conclusion and the pskl-shaped one theorem 3 carries. *)
Lemma msubst_bskl_syn_erase : forall ζ P,
  bskl_to_pskl (msubst_bskl ζ (pskl_to_bskl_syn P)) = msubst_pskl ζ P.
Proof.
  intros ζ P; induction P; simpl; f_equal; auto.
  apply bskl_to_pskl_pskl_to_bskl_syn.
Qed.

(** Building [a_wf_ptyp] from local closure and tvar-ish free variables —
    the direction the annotation's RIGIDITY hypothesis gives (the algo twin
    of decl's [d_wf_ptyp_of_lc_ftvar]). *)
Lemma a_wf_ptyp_of_lc_tvarish : forall Θ A,
  lc_ptyp A ->
  (forall α, α `in` ftvar_in_ptyp A -> a_binds_tvar α Θ) ->
  a_wf_ptyp Θ A.
Proof.
  intros Θ A Hlc; revert Θ; induction Hlc; intros Θ Hftv; simpl in Hftv.
  - apply a_wf_ptyp__unit.
  - apply a_wf_ptyp__var. apply Hftv. clear; fsetdec.
  - apply a_wf_ptyp__arrow.
    + apply IHHlc1. intros α Hα; apply Hftv; clear - Hα; fsetdec.
    + apply IHHlc2. intros α Hα; apply Hftv; clear - Hα; fsetdec.
  - apply a_wf_ptyp__all with (L := dom Θ `union` ftvar_in_ptyp A).
    intros α Hα. apply H0.
    intros β Hβ.
    pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper A (ptyp_var_f α)) as Hup.
    simpl in Hup.
    destruct (β == α) as [->|Hne];
      [ left; unfold binds; simpl; left; reflexivity | ].
    apply a_binds_tvar_weaken_cons.
    apply Hftv. clear - Hβ Hup Hne. fsetdec.
Qed.

(** Theorem 3's conclusion, factored (the shape of [a_sub_complete_thm]'s:
    the run, and for EVERY identity increase out of the question context a
    composing witness that is equivalent to the given solution and whose
    image is more precise than the declarative target). *)
Definition pat_complete_concl (M : mode) (Θ0 : aenv) (P0 : pskl) (e : exp)
    (κ : metasubst) (Θ : aenv) (Q : bskl) : Prop :=
  exists P1 Θ1,
    a_pat M Θ0 P0 e P1 Θ1 /\
    (forall κ1, is_id_msubst κ1 -> κ1 ∷ Θ0 ⊑ Θ1 ->
       exists ζ,
         ζ ∷ Θ1 ⊑ Θ /\
         a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ /\
         Θ ⨟ empty ⊢ₚᵣᵃ (msubst_pskl ζ P1) ⊑ (bskl_to_pskl Q)).

(* ===================================================================== *)
(*  The three BASE rows.  The mech FUSED the paper's [P-Sub] into them,   *)
(*  so each is exactly one invocation of thm:complete-subtyping at the    *)
(*  row's own subject, with K3b's slack.                                  *)
(* ===================================================================== *)

Lemma a_pat_complete_unit : forall M Θ0 P0 κ Θ Q,
  a_wf_aenv Θ0 -> a_wf_aenv Θ ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  a_sk_mode_compat M P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  Θ ⊢ᵃ[ M ] exp_unit ⇨ Q ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q ->
  pat_complete_concl M Θ0 P0 exp_unit κ Θ Q.
Proof.
  intros M Θ0 P0 κ Θ Q Hwf0 HwfΘ HwfP0 Hmod Hinc Hd Href.
  inversion Hd; subst.
  (* ⚙ name the two premises by SHAPE — an inversion pattern cannot
     destructure the fuel-forgotten join's existential *)
  match goal with
  | H : ad_pat_sub_v _ _ _ _ _ _ |- _ => destruct H as [njoin Hjoin]
  end.
  match goal with
  | H : _ ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl _) |- _ => rename H into HwfQ
  end.
  (* ⚙ pin the instantiation: the two mode-compat arguments discriminate on
     [NM], which is still an evar if it is left to unify positionally *)
  destruct (@a_sub_complete_thm njoin a_sub_mode_sk M Θ0 P0
              pskl_unit uskl_unit Θ κ Q
              Hwf0 HwfΘ HwfP0
              ltac:(apply a_wf_pskl__unit)
              ltac:(intros _; exact Hmod)
              ltac:(intros Hd0; discriminate)
              Hinc
              (slack_unit Θ κ)
              Hjoin Href HwfQ
              ltac:(intros Hd0; discriminate))
    as [P1 [Θ1 [Hrun Hopt]]].
  exists P1, Θ1. split; [ apply a_pat__unit; exact Hrun | ].
  intros κ1 Hid Hinc1.
  destruct (Hopt κ1 Hid Hinc1) as [ζ [Hζ [Heqv Hprec]]].
  exists ζ. split; [ exact Hζ | ]. split; [ exact Heqv | ].
  rewrite <- msubst_bskl_syn_erase. exact Hprec.
Qed.

Lemma a_pat_complete_var : forall M Θ0 P0 x κ Θ Q,
  a_wf_aenv Θ0 -> a_wf_aenv Θ ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  a_sk_mode_compat M P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ0 -> Θ0 ⨟ empty ⊢ₚₛᵃ Ps) ->
  Θ ⊢ᵃ[ M ] (exp_var_f x) ⇨ Q ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q ->
  pat_complete_concl M Θ0 P0 (exp_var_f x) κ Θ Q.
Proof.
  intros M Θ0 P0 x κ Θ Q Hwf0 HwfΘ HwfP0 Hmod Hinc Hskl Hd Href.
  inversion Hd; subst.
  match goal with
  | H : ad_pat_sub_v _ _ _ _ _ _ |- _ => destruct H as [njoin Hjoin]
  end.
  match goal with
  | H : _ ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl _) |- _ => rename H into HwfQ
  end.
  (* K2 : the SOLUTION context's entry comes from a QUESTION context one,
     and its equivalence IS thm:complete-subtyping's subject slack (K3b) *)
  match goal with
  | Hb : binds x ?b Θ, He : abind_to_pskl ?b = Some ?P |- _ =>
      destruct (@slack_var Θ0 κ Θ x b P Hinc Hwf0 HwfΘ Hb He)
        as [b0 [P0' [Hb0 [He0 Hslack]]]]
  end.
  (* the question-side subject is well-formed: a type entry by [a_wf_aenv],
     a skeleton entry by the theorem's disciplined-entry hypothesis *)
  assert (HwfP0' : Θ0 ⨟ empty ⊢ₚₛᵃ P0').
  { destruct b0; simpl in He0; try discriminate He0; inversion He0; subst.
    - apply a_wf_ptyp_to_wf_pskl.
      eapply a_wf_aenv_binds_var_typ_wf; [ exact Hwf0 | exact Hb0 ].
    - eapply Hskl; exact Hb0. }
  rewrite pskl_to_uskl_via_bskl_syn in Hjoin.
  destruct (@a_sub_complete_thm njoin a_sub_mode_sk M Θ0 P0
              P0' (pskl_to_uskl P) Θ κ Q
              Hwf0 HwfΘ HwfP0 HwfP0'
              ltac:(intros _; exact Hmod)
              ltac:(intros Hd0; discriminate)
              Hinc Hslack Hjoin Href HwfQ
              ltac:(intros Hd0; discriminate))
    as [P1 [Θ1 [Hrun Hopt]]].
  exists P1, Θ1. split.
  { destruct b0; simpl in He0; try discriminate He0; inversion He0; subst.
    - eapply a_pat__var; [ exact Hb0 | exact Hrun ].
    - eapply a_pat__var_skl; [ exact Hb0 | exact Hrun ]. }
  intros κ1 Hid Hinc1.
  destruct (Hopt κ1 Hid Hinc1) as [ζ [Hζ [Heqv Hprec]]].
  exists ζ. split; [ exact Hζ | ]. split; [ exact Heqv | ].
  rewrite <- msubst_bskl_syn_erase. exact Hprec.
Qed.

Lemma a_pat_complete_anno : forall M Θ0 P0 e A κ Θ Q,
  a_wf_aenv Θ0 -> a_wf_aenv Θ ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  a_sk_mode_compat M P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (* ⭐ the ONE side condition theorem 3 carries about the term: an
     annotation is SOURCE syntax, so its type variables are RIGID *)
  (forall α, α `in` ftvar_in_ptyp A -> binds α abind_tvar Θ0) ->
  Θ ⊢ᵃ[ M ] (exp_anno e A) ⇨ Q ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q ->
  pat_complete_concl M Θ0 P0 (exp_anno e A) κ Θ Q.
Proof.
  intros M Θ0 P0 e A κ Θ Q Hwf0 HwfΘ HwfP0 Hmod Hinc Hrig Hd Href.
  inversion Hd; subst.
  match goal with
  | H : ad_pat_sub_v _ _ _ _ _ _ |- _ => destruct H as [njoin Hjoin]
  end.
  match goal with
  | H : _ ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl _) |- _ => rename H into HwfQ
  end.
  match goal with
  | H : a_wf_ptyp Θ A |- _ => rename H into HwfA
  end.
  assert (HwfpA : Θ0 ⨟ empty ⊢ₚₛᵃ (ptyp_to_pskl A)).
  { apply a_wf_ptyp_to_wf_pskl. apply a_wf_ptyp_of_lc_tvarish;
      [ eapply a_wf_ptyp_lc; exact HwfA
      | intros α Hα; left; apply Hrig; exact Hα ]. }
  rewrite pskl_to_uskl_via_bskl_syn in Hjoin.
  destruct (@a_sub_complete_thm njoin a_sub_mode_sk M Θ0 P0
              (ptyp_to_pskl A) (ptyp_to_uskl_syn A) Θ κ Q
              Hwf0 HwfΘ HwfP0 HwfpA
              ltac:(intros _; exact Hmod)
              ltac:(intros Hd0; discriminate)
              Hinc
              (@slack_anno Θ0 κ Θ A Hinc Hwf0
                 ltac:(eapply a_wf_ptyp_lc; exact HwfA) Hrig)
              ltac:(rewrite pskl_to_uskl_ptyp in Hjoin; exact Hjoin)
              Href HwfQ
              ltac:(intros Hd0; discriminate))
    as [P1 [Θ1 [Hrun Hopt]]].
  exists P1, Θ1. split; [ eapply a_pat__anno; exact Hrun | ].
  intros κ1 Hid Hinc1.
  destruct (Hopt κ1 Hid Hinc1) as [ζ [Hζ [Heqv Hprec]]].
  exists ζ. split; [ exact Hζ | ]. split; [ exact Heqv | ].
  rewrite <- msubst_bskl_syn_erase. exact Hprec.
Qed.

(* ===================================================================== *)
(*  K5 — splitting is COMPLETE at a mode-compatible input (the four       *)
(*  binder rows' first step).                                            *)
(* ===================================================================== *)

(** ⭐ K5 — the four binder rows need a split of the input skeleton, and at
    a mode-compatible input one always exists WITHOUT touching the context.

    ⭐⭐ The flexible row [a_split__flex] — the only one that extends the
    context, and the only one whose premise is a consistency run — is
    UNREACHABLE here: [a_sk_mode_compat] leaves exactly two shapes, the
    ghost (at TI/TC) and a SYNTACTIC arrow (at FN).  That is what spares
    theorem 3 the split's own completeness obligation.

    The disjunction is what the caller inverts the solution's refinement
    along ([msubst_pskl] is structural, so it commutes with both shapes). *)
Lemma a_split_complete : forall M Θ0 P0,
  a_sk_mode_compat M P0 ->
  M <> mode_tc ->
  exists P1 Q1,
    (Θ0 ⊲ P0 ▹ P1 ⇢ Q1 ⊣ Θ0) /\
    a_sk_mode_compat (decr_mode M) Q1 /\
    ((P0 = pskl_hole /\ P1 = pskl_hole /\ Q1 = pskl_hole)
     \/ P0 = pskl_arrow P1 Q1).
Proof.
  intros M Θ0 P0 Hmod Hne; destruct Hmod.
  - (* TI at the ghost *)
    exists pskl_hole, pskl_hole.
    split; [ apply a_split__hole | ].
    split; [ apply a_sk_mode_compat__ti | ].
    left; repeat split; reflexivity.
  - (* TC : excluded by the rule's own [m <> TC] *)
    exfalso; apply Hne; reflexivity.
  - (* FN at a syntactic arrow *)
    exists P, Q.
    split; [ apply a_split__arrow | ].
    split; [ simpl; exact Hmod | ].
    right; reflexivity.
Qed.

(* ===================================================================== *)
(*  The remaining rows, as STEP LEMMAS: each takes its induction          *)
(*  hypothesis as an explicit premise, so the final induction is pure     *)
(*  glue (the P7 development's own factoring — cf.                        *)
(*  [sub_complete_arrow_holds], prop_completeness_sub.v).                 *)
(*                                                                       *)
(*  ⛔ THE FOUR BINDER ROWS NEED A KIT PIECE THAT DOES NOT EXIST YET      *)
(*  (K6, found 2026-08-07 when the induction reached them).  The          *)
(*  ALGORITHM's binder rules are COFINITE in the term variable and share  *)
(*  their outputs [Ξ]/[Θ1]/[Q] across the family, while the induction     *)
(*  hypothesis delivers ONE instance at one fresh [x] — so completeness   *)
(*  must generate the family from an instance, i.e. it needs the          *)
(*  ALGORITHMIC twin of [ad_pat_rename_tm] / [ad_pat_subst_tm]            *)
(*  (prop_soundness_pat.v §4, which theorem 1 built for the DECLARATIVE   *)
(*  judgement only).  Route: equivariance, per the standing directive —   *)
(*  [prop_swap.v] already has [a_sub_sub_flex_swap] (:1303),              *)
(*  [a_assign_unify_consis_swap] (:1078) and [a_guess_mono_swap] (:435),  *)
(*  so [a_pat_swap] mirrors them row by row and the renaming follows from *)
(*  equivariance plus freshness.  ⚙ Note the walk's own [Flex-SkipTmVar]  *)
(*  rows traverse term entries, so they must transport too — they do,     *)
(*  since the entry is skipped regardless of its name.                    *)
(* ===================================================================== *)

(** [P-Freeze] — the mode drops from TC to TI at the SAME ghost input, so
    the row is pure transport: the solution's refinement is literally the
    IH's, and the run re-wraps by [AP-Freeze]. *)
Lemma a_pat_complete_freeze : forall Θ0 e κ Θ Q,
  (forall Q', Θ ⊢ᵃ[ mode_ti ] e ⇨ Q' ->
     Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ pskl_hole)) ⊳ Q' ->
     pat_complete_concl mode_ti Θ0 pskl_hole e κ Θ Q') ->
  Θ ⊢ᵃ[ mode_tc ] (exp_freeze e) ⇨ Q ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ pskl_hole)) ⊳ Q ->
  pat_complete_concl mode_tc Θ0 pskl_hole (exp_freeze e) κ Θ Q.
Proof.
  intros Θ0 e κ Θ Q IH Hd Href.
  inversion Hd; subst.
  destruct (IH _ ltac:(eassumption) Href) as [P1 [Θ1 [Hrun Hopt]]].
  exists P1, Θ1. split; [ apply a_pat__freeze; exact Hrun | exact Hopt ].
Qed.

(* ===================================================================== *)
(*  K6 — TERM-VARIABLE RENAMING for the cofinite binder rows.            *)
(*                                                                       *)
(*  ⭐ The route is the standing directive's: EQUIVARIANCE is the one     *)
(*  renaming primitive.  prop_swap.v already proves it for the whole      *)
(*  algorithmic tower; what was missing is the bridge that turns a SWAP   *)
(*  of two atoms into the RENAMING of a term binder — which it is        *)
(*  exactly when both atoms are fresh for everything else in sight        *)
(*  ([swap_aenv_tm_head] below).  [a_sub_rename_tm] is the first          *)
(*  consumer; the same three lines give the consistency walk's and,       *)
(*  above them, [a_pat]'s own.                                           *)
(* ===================================================================== *)

(** A binding the two swapped atoms do not occur in is untouched. *)
Lemma swap_abind_fresh_eq : forall x y (b : abind),
  x `notin` ftvar_in_abind b ->
  y `notin` ftvar_in_abind b ->
  swap_abind x y b = b.
Proof.
  intros x y b Hx Hy; destruct b; simpl in *; try reflexivity; f_equal;
    first [ apply swap_ptyp_fresh_id | apply swap_pskl_fresh_id ];
    assumption.
Qed.

(** …hence a whole context the two atoms are fresh for. *)
Lemma swap_aenv_fresh_eq : forall x y Θ,
  x `notin` (dom Θ `union` ftvar_in_aenv Θ) ->
  y `notin` (dom Θ `union` ftvar_in_aenv Θ) ->
  swap_aenv x y Θ = Θ.
Proof.
  induction Θ as [ | [z c] Θ' IH ]; intros Hx Hy; simpl in *;
    [ reflexivity | ].
  f_equal.
  - f_equal.
    + unfold swap_atom.
      destruct (z == x) as [->|Hzx]; [ exfalso; clear - Hx; fsetdec | ].
      destruct (z == y) as [->|Hzy]; [ exfalso; clear - Hy; fsetdec | ].
      reflexivity.
    + apply swap_abind_fresh_eq; [ clear - Hx; fsetdec | clear - Hy; fsetdec ].
  - apply IH; [ clear - Hx; fsetdec | clear - Hy; fsetdec ].
Qed.

(** ⭐ THE BRIDGE.  Swapping a TERM binder's name with a fresh one renames
    exactly that entry: the tail is untouched (both atoms are fresh for it)
    and the payload is untouched (a term entry's payload is a TYPE, and the
    two atoms are term variables). *)
Lemma swap_aenv_tm_head : forall x y (b : abind) Θ,
  x `notin` (dom Θ `union` ftvar_in_aenv Θ `union` ftvar_in_abind b) ->
  y `notin` (dom Θ `union` ftvar_in_aenv Θ `union` ftvar_in_abind b) ->
  swap_aenv x y ((x ~ b) ++ Θ) = (y ~ b) ++ Θ.
Proof.
  intros x y b Θ Hx Hy. simpl. f_equal.
  - f_equal.
    + unfold swap_atom. destruct (x == x) as [_|Hc];
        [ reflexivity | exfalso; apply Hc; reflexivity ].
    + apply swap_abind_fresh_eq; [ clear - Hx; fsetdec | clear - Hy; fsetdec ].
  - apply swap_aenv_fresh_eq; [ clear - Hx; fsetdec | clear - Hy; fsetdec ].
Qed.

(** ⭐ K6's payload for the binder rows: the ALGORITHMIC subtyping walk is
    stable under renaming a TERM binder.  Equivariance does the work
    ([a_sub_sub_flex_swap]); the bridge above turns the swapped contexts
    back into the renamed ones, and the type-level data is untouched
    because both atoms are fresh for it. *)
Lemma a_sub_rename_tm : forall NM M P0 Θ0 P Q Ξ Θ1 x y (b : abind),
  a_sub NM M P0 ((x ~ b) ++ Θ0) P Q (Ξ ++ (x ~ b) ++ Θ1) ->
  x `notin` (dom Θ0 `union` ftvar_in_aenv Θ0 `union` ftvar_in_abind b
             `union` dom Θ1 `union` ftvar_in_aenv Θ1
             `union` dom Ξ `union` ftvar_in_aenv Ξ
             `union` ftvar_in_pskl P0 `union` ftvar_in_pskl P
             `union` ftvar_in_pskl Q) ->
  y `notin` (dom Θ0 `union` ftvar_in_aenv Θ0 `union` ftvar_in_abind b
             `union` dom Θ1 `union` ftvar_in_aenv Θ1
             `union` dom Ξ `union` ftvar_in_aenv Ξ
             `union` ftvar_in_pskl P0 `union` ftvar_in_pskl P
             `union` ftvar_in_pskl Q) ->
  a_sub NM M P0 ((y ~ b) ++ Θ0) P Q (Ξ ++ (y ~ b) ++ Θ1).
Proof.
  intros NM M P0 Θ0 P Q Ξ Θ1 x y b Hrun Hx Hy.
  pose proof ((proj1 (a_sub_sub_flex_swap x y)) _ _ _ _ _ _ _ Hrun) as Hsw.
  rewrite (@swap_aenv_tm_head x y b Θ0
             ltac:(clear - Hx; fsetdec) ltac:(clear - Hy; fsetdec)) in Hsw.
  rewrite swap_aenv_app in Hsw.
  rewrite (@swap_aenv_tm_head x y b Θ1
             ltac:(clear - Hx; fsetdec) ltac:(clear - Hy; fsetdec)) in Hsw.
  rewrite (@swap_aenv_fresh_eq x y Ξ
             ltac:(clear - Hx; fsetdec) ltac:(clear - Hy; fsetdec)) in Hsw.
  rewrite !swap_pskl_fresh_id in Hsw;
    try solve [ clear - Hx; fsetdec | clear - Hy; fsetdec ].
  exact Hsw.
Qed.

(** The consistency walk's term renaming — the same three lines as
    [a_sub_rename_tm], off [a_assign_unify_consis_swap].  This is what
    [AP-AbsAnno]'s [a_consis_chk] premise needs. *)
Lemma a_consis_rename_tm : forall Θ0 P0 P Q Ξ Θ1 x y (b : abind),
  a_consis empty empty ((x ~ b) ++ Θ0) P0 P Q (Ξ ++ (x ~ b) ++ Θ1) ->
  x `notin` (dom Θ0 `union` ftvar_in_aenv Θ0 `union` ftvar_in_abind b
             `union` dom Θ1 `union` ftvar_in_aenv Θ1
             `union` dom Ξ `union` ftvar_in_aenv Ξ
             `union` ftvar_in_pskl P0 `union` ftvar_in_pskl P
             `union` ftvar_in_pskl Q) ->
  y `notin` (dom Θ0 `union` ftvar_in_aenv Θ0 `union` ftvar_in_abind b
             `union` dom Θ1 `union` ftvar_in_aenv Θ1
             `union` dom Ξ `union` ftvar_in_aenv Ξ
             `union` ftvar_in_pskl P0 `union` ftvar_in_pskl P
             `union` ftvar_in_pskl Q) ->
  a_consis empty empty ((y ~ b) ++ Θ0) P0 P Q (Ξ ++ (y ~ b) ++ Θ1).
Proof.
  intros Θ0 P0 P Q Ξ Θ1 x y b Hrun Hx Hy.
  pose proof ((proj2 (proj2 (a_assign_unify_consis_swap x y)))
                _ _ _ _ _ _ _ Hrun empty empty
                (empty_eq_swap_atoms_empty x y)
                (empty_eq_swap_atoms_empty x y)) as Hsw.
  rewrite (@swap_aenv_tm_head x y b Θ0
             ltac:(clear - Hx; fsetdec) ltac:(clear - Hy; fsetdec)) in Hsw.
  rewrite swap_aenv_app in Hsw.
  rewrite (@swap_aenv_tm_head x y b Θ1
             ltac:(clear - Hx; fsetdec) ltac:(clear - Hy; fsetdec)) in Hsw.
  rewrite (@swap_aenv_fresh_eq x y Ξ
             ltac:(clear - Hx; fsetdec) ltac:(clear - Hy; fsetdec)) in Hsw.
  rewrite !swap_pskl_fresh_id in Hsw;
    try solve [ clear - Hx; fsetdec | clear - Hy; fsetdec ].
  exact Hsw.
Qed.

(** …in the output-suppressed form the rule states. *)
Corollary a_consis_chk_rename_tm : forall Θ0 P P0 Ξ Θ1 x y (b : abind),
  (forall Q, a_consis empty empty ((x ~ b) ++ Θ0) P0 P Q (Ξ ++ (x ~ b) ++ Θ1) ->
     x `notin` ftvar_in_pskl Q /\ y `notin` ftvar_in_pskl Q) ->
  a_consis_chk ((x ~ b) ++ Θ0) P P0 (Ξ ++ (x ~ b) ++ Θ1) ->
  x `notin` (dom Θ0 `union` ftvar_in_aenv Θ0 `union` ftvar_in_abind b
             `union` dom Θ1 `union` ftvar_in_aenv Θ1
             `union` dom Ξ `union` ftvar_in_aenv Ξ
             `union` ftvar_in_pskl P0 `union` ftvar_in_pskl P) ->
  y `notin` (dom Θ0 `union` ftvar_in_aenv Θ0 `union` ftvar_in_abind b
             `union` dom Θ1 `union` ftvar_in_aenv Θ1
             `union` dom Ξ `union` ftvar_in_aenv Ξ
             `union` ftvar_in_pskl P0 `union` ftvar_in_pskl P) ->
  a_consis_chk ((y ~ b) ++ Θ0) P P0 (Ξ ++ (y ~ b) ++ Θ1).
Proof.
  intros Θ0 P P0 Ξ Θ1 x y b HQ [Q Hrun] Hx Hy.
  destruct (HQ Q Hrun) as [HxQ HyQ].
  exists Q. eapply a_consis_rename_tm;
    [ exact Hrun
    | clear - Hx HxQ; fsetdec
    | clear - Hy HyQ; fsetdec ].
Qed.
(** Splitting is equivariant — three rows, the flexible one reusing the
    consistency walk's own equivariance. *)
Lemma a_split_swap : forall a b Θ0 P0 P Q Θ1,
  Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 ->
  (swap_aenv a b Θ0) ⊲ (swap_pskl a b P0) ▹ (swap_pskl a b P)
    ⇢ (swap_pskl a b Q) ⊣ (swap_aenv a b Θ1).
Proof.
  intros a b Θ0 P0 P Q Θ1 H; induction H; simpl.
  - apply a_split__arrow.
  - apply a_split__hole.
  - (* flexible : the invented pair is swapped along *)
    eapply a_split__flex with (β := swap_atom a b β) (α1 := swap_atom a b α1).
    + apply swap_aenv_ftvar_notin. exact H.
    + (* [α1 ∉ add β (ftv Θ0)] transports pointwise through the swap *)
      apply notin_add_3;
        [ intros Hc; apply swap_atom_inj in Hc; subst;
          clear - H0; fsetdec
        | apply swap_aenv_ftvar_notin; clear - H0; fsetdec ].
    + pose proof ((proj2 (proj2 (a_assign_unify_consis_swap a b)))
                    _ _ _ _ _ _ _ H1 empty empty
                    (empty_eq_swap_atoms_empty a b)
                    (empty_eq_swap_atoms_empty a b)) as Hsw.
      simpl in Hsw. exact Hsw.
Qed.

(** …hence splitting's term renaming, by the bridge. *)
Lemma a_split_rename_tm : forall Θ0 P0 P Q Ξ Θ1 x y (b : abind),
  ((x ~ b) ++ Θ0) ⊲ P0 ▹ P ⇢ Q ⊣ (Ξ ++ (x ~ b) ++ Θ1) ->
  x `notin` (dom Θ0 `union` ftvar_in_aenv Θ0 `union` ftvar_in_abind b
             `union` dom Θ1 `union` ftvar_in_aenv Θ1
             `union` dom Ξ `union` ftvar_in_aenv Ξ
             `union` ftvar_in_pskl P0 `union` ftvar_in_pskl P
             `union` ftvar_in_pskl Q) ->
  y `notin` (dom Θ0 `union` ftvar_in_aenv Θ0 `union` ftvar_in_abind b
             `union` dom Θ1 `union` ftvar_in_aenv Θ1
             `union` dom Ξ `union` ftvar_in_aenv Ξ
             `union` ftvar_in_pskl P0 `union` ftvar_in_pskl P
             `union` ftvar_in_pskl Q) ->
  ((y ~ b) ++ Θ0) ⊲ P0 ▹ P ⇢ Q ⊣ (Ξ ++ (y ~ b) ++ Θ1).
Proof.
  intros Θ0 P0 P Q Ξ Θ1 x y b Hrun Hx Hy.
  pose proof (a_split_swap x y Hrun) as Hsw.
  rewrite (@swap_aenv_tm_head x y b Θ0
             ltac:(clear - Hx; fsetdec) ltac:(clear - Hy; fsetdec)) in Hsw.
  rewrite swap_aenv_app in Hsw.
  rewrite (@swap_aenv_tm_head x y b Θ1
             ltac:(clear - Hx; fsetdec) ltac:(clear - Hy; fsetdec)) in Hsw.
  rewrite (@swap_aenv_fresh_eq x y Ξ
             ltac:(clear - Hx; fsetdec) ltac:(clear - Hy; fsetdec)) in Hsw.
  rewrite !swap_pskl_fresh_id in Hsw;
    try solve [ clear - Hx; fsetdec | clear - Hy; fsetdec ].
  exact Hsw.
Qed.
(* ===================================================================== *)
(*  K6, LAST PIECE — [a_pat]'s own term renaming.  DESIGN SETTLED, proof  *)
(*  not yet written (2026-08-07).                                        *)
(*                                                                       *)
(*  ⚠️ The obvious statement — substitute the term variable, keep         *)
(*  everything else, assume x,y fresh for it — CANNOT be proved: the      *)
(*  [AP-App] row's intermediate skeleton (the argument's OUTPUT, [P0] of  *)
(*  the function premise) is EXISTENTIAL, so no freshness for it can be   *)
(*  carried from the statement's hypotheses.                             *)
(*                                                                       *)
(*  ⭐ The statement that works is the HYBRID: SWAP the type-level data   *)
(*  (contexts and both skeletons — so nothing needs to be fresh for it,   *)
(*  exactly as in the equivariance lemmas this file already consumes) and *)
(*  SUBSTITUTE in the term, whose only freshness obligation is about      *)
(*  ANNOTATIONS and therefore shrinks with the term:                     *)
(*                                                                       *)
(*    Lemma a_pat_rename_tm : forall a b m Θ0 P0 e P Θ1,                 *)
(*      Θ0 ⊢ₐ[ m ; P0 ] e ⇨ P ⊣ Θ1 ->                                    *)
(*      a `notin` ftvar_in_exp e -> b `notin` ftvar_in_exp e ->          *)
(*      a_pat m (swap_aenv a b Θ0) (swap_pskl a b P0)                    *)
(*        (subst_exp_in_exp (exp_var_f b) a e) (swap_pskl a b P)         *)
(*        (swap_aenv a b Θ1).                                            *)
(*                                                                       *)
(*  This is why no [swap_exp] is needed (prop_swap.v has none, and adding *)
(*  one would have to swap ANNOTATION types too).  The ten rows transport *)
(*  by [a_sub_sub_flex_swap], [a_assign_unify_consis_swap] and            *)
(*  [a_split_swap] — the SWAP forms directly, not the renaming corollaries*)
(*  above, which are for the CONSUMERS.  The binder rows follow           *)
(*  [ad_pat_subst_tm]'s cofinite dance (prop_soundness_pat.v §4).         *)
(*  Consumers read the conclusion back with [swap_aenv_tm_head] /         *)
(*  [swap_aenv_fresh_eq] / [swap_pskl_fresh_id].                         *)
(* ===================================================================== *)
