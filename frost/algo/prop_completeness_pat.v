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
