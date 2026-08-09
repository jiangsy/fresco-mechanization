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
Require Import Coq.micromega.Lia.
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
Require Import src.frost.algo.sub.prop_sub_msubst_equiv.
Require Import src.frost.algo.prop_swap.
Require Import src.frost.algo.sub.prop_completeness_sub_gen.
Require Import src.frost.algo.sub.prop_completeness_sub.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.consis.prop_completeness_consis.
Require Import src.frost.algo.prop_precise.
Require Import src.frost.algo.consis.prop_consis_rename.
Require Import src.frost.algo.consis.prop_soundness_consis.
Require Import src.frost.algo.prop_wf_preservation.
Require Import src.frost.algo.sub.prop_soundness_sub.
Require Import src.frost.algo.pat.prop_soundness_pat.
Require Import src.frost.algo.typing.prop_soundness_typing.
Require Import src.frost.algo.prop_suffix_erase.
Require Import src.frost.algo.prop_precise_sub.

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
    pose proof (H3 x ltac:(clear - Hx; solve_notin_auto) Hwfx) as HwfQ.
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
    pose proof (H4 x ltac:(clear - Hx; solve_notin_auto) Hwfx) as HwfQ.
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
    pose proof (H0 x ltac:(clear - Hx; solve_notin_auto) Hwfx) as HwfQ.
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
    pose proof (H1 x ltac:(clear - Hx; solve_notin_auto) Hwfx) as HwfQ.
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
(** A skeleton entry's payload is scoped in the WHOLE context (its own
    tail suffices, so a fortiori). *)
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
(*  [a_sub_complete] takes its subject up to [≡ᵘ] slack              *)
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
    erasure — the bridge between [a_sub_complete]'s bskl-shaped
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

(** Theorem 3's conclusion, factored (the shape of [a_sub_complete]'s:
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
  destruct (@a_sub_complete njoin a_sub_mode_sk M Θ0 P0
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
  destruct (@a_sub_complete njoin a_sub_mode_sk M Θ0 P0
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
  destruct (@a_sub_complete njoin a_sub_mode_sk M Θ0 P0
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

(* ⚙ K6 — TERM-VARIABLE RENAMING for the cofinite binder rows: MOVED
   2026-08-09 to algo/prop_swap.v §6 (cleanup audit §1.2).  It is the
   term-variable half of the swap kit — [swap_abind_fresh_eq],
   [swap_aenv_fresh_eq], [swap_aenv_tm_head], [swap_aenv_one],
   [a_split_swap], and the four [*_rename_tm] bridges for
   [a_sub] / [a_consis] / [a_consis_chk] / [a_split], plus [a_pat_rename_tm]
   itself.  This file imports prop_swap.v, so the rows below are unchanged.

   ⚠️ The block exists at all because [a_pat]'s four binder rows are still
   COFINITE while [a_typing]'s six are EXISTS-FRESH (cleanup audit §3): the
   IH hands back one instance and the rule wants the whole family.  Converting
   [a_pat] would retire it. *)


(* ===================================================================== *)
(*  K8 — the binder rows' support: freshness of a TERM atom for the       *)
(*  run's type-level data, identity-witness uniqueness, and the           *)
(*  equivalence's term-entry strip.                                       *)
(* ===================================================================== *)

(** A term-bound atom is never type-level bound (the kind discipline). *)
Lemma a_binds_tvar_tm_absurd : forall Θ x (b : abind),
  uniq Θ ->
  binds x b Θ ->
  abind_is_tm b ->
  a_binds_tvar x Θ ->
  False.
Proof.
  intros Θ x b Hu Hb Htm [Hb' | [Hb' | [τ Hb']]];
    pose proof (binds_unique _ _ _ _ _ Hb Hb' Hu) as ->; exact Htm.
Qed.

(** …so a wf skeleton cannot mention it as a free type variable. *)
Lemma a_wf_pskl_notin_ftv_tm : forall Θ x (b : abind) P,
  Θ ⨟ empty ⊢ₚₛᵃ P ->
  uniq Θ ->
  binds x b Θ ->
  abind_is_tm b ->
  x `notin` ftvar_in_pskl P.
Proof.
  intros Θ x b P Hwf Hu Hb Htm Hin.
  destruct (a_wf_pskl_ftv_tvarish Hwf Hin) as [Hd | Htv];
    [ clear - Hd; fsetdec
    | eapply a_binds_tvar_tm_absurd; eassumption ].
Qed.

(** The run's pending suffix cannot mention the walked binder either: its
    declarations carry no payload and its definitions are wf in a tail
    that term-binds the atom. *)
Lemma a_wf_aenv_notin_ftv_tm_prefix : forall Ξ x (b : abind) Θ,
  a_suffix Ξ ->
  a_wf_aenv (Ξ ++ (x ~ b) ++ Θ) ->
  abind_is_tm b ->
  x `notin` (dom Ξ `union` ftvar_in_aenv Ξ).
Proof.
  induction Ξ as [ | [α bΞ] Ξ' IH ]; intros x b Θ Hsuf Hwf Htm;
    [ simpl; clear; fsetdec | ].
  inversion Hsuf as [ | ? ? ? Hsuf' Hsb ]; subst.
  assert (Hx : binds x b (Ξ' ++ (x ~ b) ++ Θ))
    by (apply binds_app_3; apply binds_app_2; unfold binds; simpl; auto).
  destruct Hsb as [ | τ ].
  - (* flexible declaration *)
    inversion Hwf as [ | ? ? Hα Hwf' | | | | ]; subst.
    assert (Hαx : α <> x)
      by (intros ->; apply binds_In in Hx; clear - Hα Hx; fsetdec).
    pose proof (IH _ _ _ Hsuf' Hwf' Htm) as Hrec.
    simpl. clear - Hαx Hrec; fsetdec.
  - (* flexible definition: the payload is wf in the term-binding tail *)
    inversion Hwf as [ | | ? ? ? Hα Hτ Hm Hwf' | | | ]; subst.
    assert (Hαx : α <> x)
      by (intros ->; apply binds_In in Hx; clear - Hα Hx; fsetdec).
    pose proof (IH _ _ _ Hsuf' Hwf' Htm) as Hrec.
    assert (Hxτ : x `notin` ftvar_in_ptyp τ).
    { intros Hin.
      pose proof (a_wf_ptyp_ftv_tvarish Hτ Hin) as Htv.
      eapply a_binds_tvar_tm_absurd with (x := x);
        [ apply a_wf_aenv_uniq; exact Hwf' | exact Hx | exact Htm | exact Htv ]. }
    simpl. clear - Hαx Hrec Hxτ; fsetdec.
Qed.

(** A term-bound atom is fresh for the wf tail BELOW its own entry. *)
Lemma a_wf_aenv_notin_ftv_tm_below : forall Ξ x (b : abind) Θ,
  a_wf_aenv (Ξ ++ (x ~ b) ++ Θ) ->
  x `notin` (dom Θ `union` ftvar_in_aenv Θ).
Proof.
  intros Ξ x b Θ Hwf.
  assert (HwfT : a_wf_aenv Θ)
    by (eapply a_wf_aenv_app_r with (Θp := Ξ ++ (x ~ b)); simpl_env; exact Hwf).
  assert (Hu : uniq (Ξ ++ (x ~ b) ++ Θ)) by (apply a_wf_aenv_uniq; exact Hwf).
  assert (Hd : x `notin` dom Θ)
    by (clear - Hu; simpl_env in Hu; destruct_uniq;
        unfold disjoint in *; simpl_env in *; fsetdec).
  pose proof (a_wf_aenv_ftv_dom HwfT) as Hsub.
  clear - Hd Hsub; fsetdec.
Qed.

(** ⭐ K8 — an IDENTITY witness is determined by its source: [a_inc]'s flex
    rows cons one entry per flexible, the other rows pass the substitution
    through, and identity pins every image.  Hence any two identity
    increases out of the same question context carry the SAME list — which
    is what lets a binder row hand the caller's witness to the IH at the
    binder-extended contexts. *)
Lemma a_inc_id_msubst_unique : forall Θ0 κ Θ κ' Θ',
  κ ∷ Θ0 ⊑ Θ ->
  κ' ∷ Θ0 ⊑ Θ' ->
  is_id_msubst κ -> is_id_msubst κ' ->
  κ = κ'.
Proof.
  intros Θ0 κ Θ κ' Θ' H; revert κ' Θ'.
  induction H; intros κ' Θ'' Hinc' Hid Hid'.
  - (* empty *)
    inversion Hinc'; subst; reflexivity.
  - (* flex *)
    inversion Hinc'; subst.
    destruct (is_id_msubst_inv Hid) as [-> Hid2].
    destruct (is_id_msubst_inv Hid') as [-> Hid2'].
    f_equal. eapply IHa_inc; eassumption.
  - (* flex_def *)
    inversion Hinc'; subst.
    destruct (is_id_msubst_inv Hid) as [-> Hid2].
    destruct (is_id_msubst_inv Hid') as [-> Hid2'].
    f_equal. eapply IHa_inc; eassumption.
  - (* var *)
    inversion Hinc'; subst. eapply IHa_inc; eassumption.
  - (* var_skl *)
    inversion Hinc'; subst. eapply IHa_inc; eassumption.
  - (* tvar *)
    inversion Hinc'; subst. eapply IHa_inc; eassumption.
Qed.

(** The equivalence loses a term entry from both ends (the head of each):
    only the matching semantic row can have built it, and a pending suffix
    cannot supply the target's TERM head. *)
Lemma a_inc_equiv_strip_var_skl_head : forall x (P : pskl) Θ0 κ1 κ2 (b' : abind) Θ,
  a_inc_equiv ((x ~ abind_var_skl P) ++ Θ0) κ1 κ2 ((x ~ b') ++ Θ) ->
  abind_is_tm b' ->
  a_inc_equiv Θ0 κ1 κ2 Θ.
Proof.
  intros x P Θ0 κ1 κ2 b' Θ Hie Htm.
  inversion Hie; subst.
  match goal with
  | Hsuf : a_suffix ?ΞS, HeqT : ?l = ?r |- _ =>
      first [ constr_eq l ((x ~ b') ++ Θ); symmetry in HeqT | idtac ];
      destruct ΞS as [ | [z bz] Ξ' ]; simpl_env in HeqT;
      [ inversion HeqT; subst; assumption
      | inversion HeqT; subst;
        inversion Hsuf as [ | ? ? ? ? Hsb ]; subst;
        exfalso; destruct Hsb; exact Htm ]
  end.
Qed.

Lemma a_inc_equiv_strip_var_typ_head : forall x (A : ptyp) Θ0 κ1 κ2 (b' : abind) Θ,
  a_inc_equiv ((x ~ abind_var_typ A) ++ Θ0) κ1 κ2 ((x ~ b') ++ Θ) ->
  abind_is_tm b' ->
  a_inc_equiv Θ0 κ1 κ2 Θ.
Proof.
  intros x A Θ0 κ1 κ2 b' Θ Hie Htm.
  inversion Hie; subst.
  match goal with
  | Hsuf : a_suffix ?ΞS, HeqT : ?l = ?r |- _ =>
      first [ constr_eq l ((x ~ b') ++ Θ); symmetry in HeqT | idtac ];
      destruct ΞS as [ | [z bz] Ξ' ]; simpl_env in HeqT;
      [ inversion HeqT; subst; assumption
      | inversion HeqT; subst;
        inversion Hsuf as [ | ? ? ? ? Hsb ]; subst;
        exfalso; destruct Hsb; exact Htm ]
  end.
Qed.

(** The term side condition supplies theorem 1's [a_wf_exp]: an annotation
    whose type variables are all RIGID is wf, and nothing else in the
    judgement reads the context. *)
Lemma a_wf_exp_of_tvarish : forall Θ e,
  lc_exp e ->
  (forall α, α `in` ftvar_in_exp e -> a_binds_tvar α Θ) ->
  a_wf_exp Θ e.
Proof.
  intros Θ e Hlc; induction Hlc; intros Hftv; simpl in Hftv.
  - apply a_wf_exp__unit.
  - apply a_wf_exp__var.
  - apply a_wf_exp__abs with (L := empty).
    intros x _. apply H0.
    intros α Hα.
    pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Hup.
    simpl in Hup. apply Hftv. clear - Hα Hup; fsetdec.
  - apply a_wf_exp__abs_anno with (L := empty).
    + apply a_wf_ptyp_of_lc_tvarish;
        [ assumption
        | intros α Hα; apply Hftv; clear - Hα; fsetdec ].
    + intros x _. apply H1.
      intros α Hα.
      pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Hup.
      simpl in Hup. apply Hftv. clear - Hα Hup; fsetdec.
  - apply a_wf_exp__app;
      [ apply IHHlc1 | apply IHHlc2 ];
      intros α Hα; apply Hftv; clear - Hα; fsetdec.
  - apply a_wf_exp__anno.
    + apply a_wf_ptyp_of_lc_tvarish;
        [ assumption
        | intros α Hα; apply Hftv; clear - Hα; fsetdec ].
    + apply IHHlc. intros α Hα; apply Hftv; clear - Hα; fsetdec.
  - apply a_wf_exp__freeze.
    apply IHHlc. intros α Hα; apply Hftv; exact Hα.
Qed.

(* ===================================================================== *)
(*  P-AbsCheck, the step lemma.                                           *)
(* ===================================================================== *)

Lemma a_pat_complete_abs_check : forall Θ0 e κ Θ Q,
  a_wf_aenv Θ0 -> a_wf_aenv Θ ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_abs e) -> binds α abind_tvar Θ0) ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ0 -> Θ0 ⨟ empty ⊢ₚₛᵃ Ps) ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ -> Θ ⨟ empty ⊢ₚₛᵃ Ps) ->
  lc_exp (exp_abs e) ->
  (forall x M' Θ0' P0' κ' Θ' Q',
     a_wf_aenv Θ0' -> a_wf_aenv Θ' ->
     Θ0' ⨟ empty ⊢ₚₛᵃ P0' ->
     a_sk_mode_compat M' P0' ->
     κ' ∷ Θ0' ⊑ Θ' ->
     (forall α, α `in` ftvar_in_exp (open_exp_wrt_exp e (exp_var_f x)) ->
        binds α abind_tvar Θ0') ->
     (forall y Ps, binds y (abind_var_skl Ps) Θ0' -> Θ0' ⨟ empty ⊢ₚₛᵃ Ps) ->
     (forall y Ps, binds y (abind_var_skl Ps) Θ' -> Θ' ⨟ empty ⊢ₚₛᵃ Ps) ->
     lc_exp (open_exp_wrt_exp e (exp_var_f x)) ->
     Θ' ⊢ᵃ[ M' ] (open_exp_wrt_exp e (exp_var_f x)) ⇨ Q' ->
     Θ' ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ' P0')) ⊳ Q' ->
     pat_complete_concl M' Θ0' P0' (open_exp_wrt_exp e (exp_var_f x)) κ' Θ' Q') ->
  Θ ⊢ᵃ[ mode_tc ] (exp_abs e) ⇨ Q ->
  pat_complete_concl mode_tc Θ0 pskl_hole (exp_abs e) κ Θ Q.
Proof.
  intros Θ0 e κ Θ Q Hwf0 HwfΘ Hinc Hrig Hskl HsklT Hlc IH Hd.
  inversion Hd; subst; [ exfalso; auto | ].
  match goal with
  | H : forall x, x `notin` ?L0 -> _ ⊢ᵃ[ _ ] _ ⇨ _ |- _ =>
      rename H into Hbody; rename L0 into L
  end.
  simpl in Hrig.
  (* ---- 1. one fresh binder ---- *)
  destruct (atom_fresh (L `union` dom Θ0 `union` ftvar_in_aenv Θ0
                          `union` dom Θ `union` ftvar_in_aenv Θ
                          `union` fvar_in_exp e `union` ftvar_in_exp e
                          `union` ftvar_in_pskl P)) as [x Hx].
  set (bx := abind_var_skl pskl_hole).
  assert (Hwf0x : a_wf_aenv ((x ~ bx) ++ Θ0))
    by (apply a_wf_aenv__var;
        [ clear - Hx; fsetdec | apply a_scope_pskl__hole | exact Hwf0 ]).
  assert (HwfΘx : a_wf_aenv ((x ~ bx) ++ Θ))
    by (apply a_wf_aenv__var;
        [ clear - Hx; fsetdec | apply a_scope_pskl__hole | exact HwfΘ ]).
  assert (Hincx : κ ∷ ((x ~ bx) ++ Θ0) ⊑ ((x ~ bx) ++ Θ)).
  { apply (@a_inc__var_skl Θ0 κ Θ nil x pskl_hole pskl_hole);
      [ exact Hinc
      | apply a_pskl_tyequiv__refl; apply lc_pskl_hole
      | apply a_suffix__nil ]. }
  assert (Hlcbody : lc_exp (open_exp_wrt_exp e (exp_var_f x)))
    by (inversion Hlc; auto).
  assert (Hrigx : forall α,
             α `in` ftvar_in_exp (open_exp_wrt_exp e (exp_var_f x)) ->
             binds α abind_tvar ((x ~ bx) ++ Θ0)).
  { intros α Hα.
    pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Hup.
    simpl in Hup.
    apply binds_cons_3. apply Hrig. clear - Hα Hup; fsetdec. }
  assert (Hsklx : forall y Ps, binds y (abind_var_skl Ps) ((x ~ bx) ++ Θ0) ->
             ((x ~ bx) ++ Θ0) ⨟ empty ⊢ₚₛᵃ Ps).
  { intros y Ps Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> Heq] | Hb'].
    - inversion Heq; subst. apply a_wf_pskl__hole.
    - eapply a_wf_pskl_mono; [ eapply Hskl; exact Hb' | ].
      intros α c _ Hc. apply binds_cons_3. exact Hc. }
  assert (HsklTx : forall y Ps, binds y (abind_var_skl Ps) ((x ~ bx) ++ Θ) ->
             ((x ~ bx) ++ Θ) ⨟ empty ⊢ₚₛᵃ Ps).
  { intros y Ps Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> Heq] | Hb'].
    - inversion Heq; subst. apply a_wf_pskl__hole.
    - eapply a_wf_pskl_mono; [ eapply HsklT; exact Hb' | ].
      intros α c _ Hc. apply binds_cons_3. exact Hc. }
  (* the body target is wf at the extended contexts (K1) *)
  assert (HwfP : ((x ~ bx) ++ Θ) ⨟ empty ⊢ₚₛᵃ P).
  { pose proof (ad_pat_target_wf (Hbody x ltac:(clear - Hx; solve_notin_auto)) HwfΘx)
      as Hw.
    rewrite bskl_to_pskl_pskl_to_bskl_syn in Hw. exact Hw. }
  (* ---- 2. the IH, once ---- *)
  destruct (IH x mode_tc ((x ~ bx) ++ Θ0) pskl_hole κ ((x ~ bx) ++ Θ)
              (pskl_to_bskl_syn P)
              Hwf0x HwfΘx
              ltac:(apply a_wf_pskl__hole)
              ltac:(apply a_sk_mode_compat__tc)
              Hincx Hrigx Hsklx HsklTx Hlcbody
              (Hbody x ltac:(clear - Hx; solve_notin_auto))
              ltac:(apply ad_refine_syn__hole; exact HwfP))
    as [Q' [Θ1' [Hrun Hopt]]].
  (* ---- 3. the run's identity increase shapes the output ---- *)
  assert (Hexpx : a_wf_exp ((x ~ bx) ++ Θ0) (open_exp_wrt_exp e (exp_var_f x))).
  { apply a_wf_exp_of_tvarish; [ exact Hlcbody | ].
    intros α Hα. left. apply Hrigx. exact Hα. }
  destruct (a_pat_sound Hrun Hwf0x Hsklx
              ltac:(apply a_wf_pskl__hole)
              ltac:(apply a_sk_mode_compat__tc)
              Hexpx)
    as [Hle [Hwf1' _]].
  destruct Hle as [[κid [Hidκ Hincid]] _].
  destruct (a_inc_var_skl_inv Hincid) as [Ξ [P'' [Θ2 [-> [_ [Hsuf Hincid']]]]]].
  assert (Hu1' : uniq (Ξ ++ (x ~ abind_var_skl P'') ++ Θ2))
    by (apply a_wf_aenv_uniq; exact Hwf1').
  (* the algorithm never rewrites a term entry: the walked binder's payload
     is VERBATIM the input's *)
  assert (Hbx1 : binds x bx (Ξ ++ (x ~ abind_var_skl P'') ++ Θ2))
    by (eapply a_pat_tm_le;
        [ exact Hrun | exact I | unfold binds; simpl; auto ]).
  assert (HP'' : bx = abind_var_skl P'')
    by (eapply binds_mid_eq; [ exact Hbx1 | exact Hu1' ]).
  unfold bx in HP''. inversion HP''; subst P''.
  (* ---- 4. the freshness pack for the family generation ---- *)
  assert (HxΞ : x `notin` (dom Ξ `union` ftvar_in_aenv Ξ))
    by (eapply a_wf_aenv_notin_ftv_tm_prefix;
        [ exact Hsuf | exact Hwf1' | exact I ]).
  assert (HxΘ2 : x `notin` (dom Θ2 `union` ftvar_in_aenv Θ2))
    by (eapply a_wf_aenv_notin_ftv_tm_below; exact Hwf1').
  assert (HwfQ' : (Ξ ++ (x ~ bx) ++ Θ2) ⨟ empty ⊢ₚₛᵃ Q')
    by (eapply a_pat_output_wf;
        [ exact Hrun | exact Hwf0x | exact Hsklx
        | apply a_wf_pskl__hole | apply a_sk_mode_compat__tc | exact Hexpx ]).
  assert (HxQ' : x `notin` ftvar_in_pskl Q')
    by (eapply a_wf_pskl_notin_ftv_tm;
        [ exact HwfQ' | exact Hu1' | exact Hbx1 | exact I ]).
  (* ---- 5. the run ---- *)
  exists (pskl_tophole (pskl_arrow pskl_hole Q')), (Ξ ++ Θ2).
  split.
  { apply a_pat__abs_check
      with (L := dom Θ0 `union` ftvar_in_aenv Θ0
                 `union` dom Ξ `union` ftvar_in_aenv Ξ
                 `union` dom Θ2 `union` ftvar_in_aenv Θ2
                 `union` ftvar_in_pskl Q'
                 `union` fvar_in_exp e `union` ftvar_in_exp e
                 `union` singleton x);
      [ exact Hsuf | ].
    intros z Hz.
    pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Hup.
    pose proof (fvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Hvup.
    simpl in Hup, Hvup.
    pose proof (@a_pat_rename_tm x z _ _ _ _ _ _ Hrun
                  ltac:(clear - Hx Hup; solve_notin_auto)
                  ltac:(clear - Hz Hup; solve_notin_auto)
                  ltac:(clear - Hz Hvup; solve_notin_auto)) as Hsw.
    rewrite (@swap_aenv_tm_head x z bx Θ0
               ltac:(simpl; clear - Hx; solve_notin_auto)
               ltac:(simpl; clear - Hz; solve_notin_auto)) in Hsw.
    rewrite swap_aenv_app in Hsw.
    rewrite (@swap_aenv_tm_head x z (abind_var_skl pskl_hole) Θ2
               ltac:(simpl; clear - HxΘ2; solve_notin_auto)
               ltac:(simpl; clear - Hz; solve_notin_auto)) in Hsw.
    rewrite (@swap_aenv_fresh_eq x z Ξ
               ltac:(clear - HxΞ; solve_notin_auto)
               ltac:(clear - Hz; solve_notin_auto)) in Hsw.
    rewrite (@swap_pskl_fresh_id x z Q'
               ltac:(clear - HxQ'; solve_notin_auto)
               ltac:(clear - Hz; solve_notin_auto)) in Hsw.
    rewrite <- (@subst_exp_in_exp_intro x e (exp_var_f z)
                  ltac:(clear - Hx; solve_notin_auto)) in Hsw.
    exact Hsw. }
  (* ---- 6. optimality ---- *)
  intros κ1 Hid1 Hinc1.
  (* the caller's identity witness IS the run's own (identity witnesses are
     source-determined), so it extends across the binder by the rule *)
  assert (Heqκ : κ1 = κid)
    by (eapply a_inc_id_msubst_unique;
        [ exact Hinc1 | exact Hincid' | exact Hid1 | exact Hidκ ]).
  assert (Hinc1x : κ1 ∷ ((x ~ bx) ++ Θ0) ⊑ (Ξ ++ (x ~ bx) ++ Θ2)).
  { apply (@a_inc__var_skl Θ0 κ1 Θ2 Ξ x pskl_hole pskl_hole);
      [ rewrite Heqκ; exact Hincid'
      | apply a_pskl_tyequiv__refl; apply lc_pskl_hole
      | exact Hsuf ]. }
  destruct (Hopt κ1 Hid1 Hinc1x) as [ζ [Hζ [Heqv Hprec]]].
  exists ζ.
  split.
  { exact (@a_inc_strip_tm_head Ξ x (abind_var_skl pskl_hole)
             (abind_var_skl pskl_hole) Θ2 ζ Θ Hsuf
             (fun h : abind_is_ty (abind_var_skl pskl_hole) => h)
             (fun h : abind_is_ty (abind_var_skl pskl_hole) => h)
             Hwf1' HwfΘx Hζ). }
  split.
  { eapply a_inc_equiv_strip_var_skl_head; [ exact Heqv | exact I ]. }
  { (* the precision, rebuilt through ⊤(◇ → ·) *)
    unfold ad_precise in Hprec |- *.
    rewrite bskl_to_pskl_pskl_to_bskl_syn in Hprec.
    cbn [msubst_pskl bskl_to_pskl pskl_to_bskl_inh].
    rewrite bskl_to_pskl_pskl_to_bskl_syn.
    apply ad_refine_syn__tophole_keep.
    { apply guarded_bskl__arrow;
        [ apply lc_bskl_hole
        | apply lc_pskl_to_bskl_inh; eapply a_wf_pskl_lc; exact HwfP ]. }
    apply ad_refine_syn__arrow.
    - apply (@ad_refine_syn__hole Θ empty pskl_hole).
      apply a_wf_pskl__hole.
    - eapply ad_refine_syn_mono;
        [ exact Hprec
        | apply (@aenv_tbinds_le_strip_tm nil x bx Θ); intros h; exact h ]. }
Qed.

(* ===================================================================== *)
(*  P-AbsAnnoCheck, the step lemma.                                       *)
(* ===================================================================== *)

Lemma a_pat_complete_abs_anno_check : forall Θ0 A e κ Θ Q,
  a_wf_aenv Θ0 -> a_wf_aenv Θ ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_abs_anno A e) -> binds α abind_tvar Θ0) ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ0 -> Θ0 ⨟ empty ⊢ₚₛᵃ Ps) ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ -> Θ ⨟ empty ⊢ₚₛᵃ Ps) ->
  lc_exp (exp_abs_anno A e) ->
  (forall x M' Θ0' P0' κ' Θ' Q',
     a_wf_aenv Θ0' -> a_wf_aenv Θ' ->
     Θ0' ⨟ empty ⊢ₚₛᵃ P0' ->
     a_sk_mode_compat M' P0' ->
     κ' ∷ Θ0' ⊑ Θ' ->
     (forall α, α `in` ftvar_in_exp (open_exp_wrt_exp e (exp_var_f x)) ->
        binds α abind_tvar Θ0') ->
     (forall y Ps, binds y (abind_var_skl Ps) Θ0' -> Θ0' ⨟ empty ⊢ₚₛᵃ Ps) ->
     (forall y Ps, binds y (abind_var_skl Ps) Θ' -> Θ' ⨟ empty ⊢ₚₛᵃ Ps) ->
     lc_exp (open_exp_wrt_exp e (exp_var_f x)) ->
     Θ' ⊢ᵃ[ M' ] (open_exp_wrt_exp e (exp_var_f x)) ⇨ Q' ->
     Θ' ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ' P0')) ⊳ Q' ->
     pat_complete_concl M' Θ0' P0' (open_exp_wrt_exp e (exp_var_f x)) κ' Θ' Q') ->
  Θ ⊢ᵃ[ mode_tc ] (exp_abs_anno A e) ⇨ Q ->
  pat_complete_concl mode_tc Θ0 pskl_hole (exp_abs_anno A e) κ Θ Q.
Proof.
  intros Θ0 A e κ Θ Q Hwf0 HwfΘ Hinc Hrig Hskl HsklT Hlc IH Hd.
  inversion Hd; subst; [ exfalso; auto | ].
  match goal with
  | H : forall x, x `notin` ?L0 -> _ ⊢ᵃ[ _ ] _ ⇨ _ |- _ =>
      rename H into Hbody; rename L0 into L
  end.
  match goal with
  | H : a_wf_ptyp Θ A |- _ => rename H into HwfA
  end.
  simpl in Hrig.
  assert (HrigA : forall α, α `in` ftvar_in_ptyp A -> binds α abind_tvar Θ0)
    by (intros α Hα; apply Hrig; clear - Hα; fsetdec).
  assert (HlcA : lc_ptyp A) by (inversion Hlc; assumption).
  assert (HwfA0 : a_wf_ptyp Θ0 A)
    by (apply a_wf_ptyp_of_lc_tvarish;
        [ exact HlcA | intros α Hα; left; apply HrigA; exact Hα ]).
  assert (HmsA : msubst_ptyp κ A = A)
    by (eapply msubst_ptyp_rigid_id;
        [ exact Hinc | exact Hwf0 | exact HrigA ]).
  (* ---- 1. one fresh binder ---- *)
  destruct (atom_fresh (L `union` dom Θ0 `union` ftvar_in_aenv Θ0
                          `union` dom Θ `union` ftvar_in_aenv Θ
                          `union` fvar_in_exp e `union` ftvar_in_exp e
                          `union` ftvar_in_ptyp A
                          `union` ftvar_in_pskl P)) as [x Hx].
  set (bx := abind_var_typ A).
  assert (Hwf0x : a_wf_aenv ((x ~ bx) ++ Θ0))
    by (apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact HwfA0 | exact Hwf0 ]).
  assert (HwfΘx : a_wf_aenv ((x ~ bx) ++ Θ))
    by (apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact HwfA | exact HwfΘ ]).
  assert (Hincx : κ ∷ ((x ~ bx) ++ Θ0) ⊑ ((x ~ bx) ++ Θ)).
  { apply (@a_inc__var Θ0 κ Θ nil x A A);
      [ exact Hinc
      | rewrite HmsA; apply a_tyequiv__refl; exact HlcA
      | apply a_suffix__nil ]. }
  assert (Hlcbody : lc_exp (open_exp_wrt_exp e (exp_var_f x)))
    by (inversion Hlc; auto).
  assert (Hrigx : forall α,
             α `in` ftvar_in_exp (open_exp_wrt_exp e (exp_var_f x)) ->
             binds α abind_tvar ((x ~ bx) ++ Θ0)).
  { intros α Hα.
    pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Hup.
    simpl in Hup.
    apply binds_cons_3. apply Hrig. clear - Hα Hup; fsetdec. }
  assert (Hsklx : forall y Ps, binds y (abind_var_skl Ps) ((x ~ bx) ++ Θ0) ->
             ((x ~ bx) ++ Θ0) ⨟ empty ⊢ₚₛᵃ Ps).
  { intros y Ps Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> Heq] | Hb'];
      [ discriminate Heq | ].
    eapply a_wf_pskl_mono; [ eapply Hskl; exact Hb' | ].
    intros α c _ Hc. apply binds_cons_3. exact Hc. }
  assert (HsklTx : forall y Ps, binds y (abind_var_skl Ps) ((x ~ bx) ++ Θ) ->
             ((x ~ bx) ++ Θ) ⨟ empty ⊢ₚₛᵃ Ps).
  { intros y Ps Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> Heq] | Hb'];
      [ discriminate Heq | ].
    eapply a_wf_pskl_mono; [ eapply HsklT; exact Hb' | ].
    intros α c _ Hc. apply binds_cons_3. exact Hc. }
  assert (HwfP : ((x ~ bx) ++ Θ) ⨟ empty ⊢ₚₛᵃ P).
  { pose proof (ad_pat_target_wf (Hbody x ltac:(clear - Hx; solve_notin_auto)) HwfΘx)
      as Hw.
    rewrite bskl_to_pskl_pskl_to_bskl_syn in Hw. exact Hw. }
  (* ---- 2. the IH, once ---- *)
  destruct (IH x mode_tc ((x ~ bx) ++ Θ0) pskl_hole κ ((x ~ bx) ++ Θ)
              (pskl_to_bskl_syn P)
              Hwf0x HwfΘx
              ltac:(apply a_wf_pskl__hole)
              ltac:(apply a_sk_mode_compat__tc)
              Hincx Hrigx Hsklx HsklTx Hlcbody
              (Hbody x ltac:(clear - Hx; solve_notin_auto))
              ltac:(apply ad_refine_syn__hole; exact HwfP))
    as [Q' [Θ1' [Hrun Hopt]]].
  (* ---- 3. the run's identity increase shapes the output ---- *)
  assert (Hexpx : a_wf_exp ((x ~ bx) ++ Θ0) (open_exp_wrt_exp e (exp_var_f x))).
  { apply a_wf_exp_of_tvarish; [ exact Hlcbody | ].
    intros α Hα. left. apply Hrigx. exact Hα. }
  destruct (a_pat_sound Hrun Hwf0x Hsklx
              ltac:(apply a_wf_pskl__hole)
              ltac:(apply a_sk_mode_compat__tc)
              Hexpx)
    as [Hle [Hwf1' _]].
  destruct Hle as [[κid [Hidκ Hincid]] _].
  destruct (a_inc_var_inv Hincid) as [Ξ [A'' [Θ2 [-> [_ [Hsuf Hincid']]]]]].
  assert (Hu1' : uniq (Ξ ++ (x ~ abind_var_typ A'') ++ Θ2))
    by (apply a_wf_aenv_uniq; exact Hwf1').
  assert (Hbx1 : binds x bx (Ξ ++ (x ~ abind_var_typ A'') ++ Θ2))
    by (eapply a_pat_tm_le;
        [ exact Hrun | exact I | unfold binds; simpl; auto ]).
  assert (HA'' : bx = abind_var_typ A'')
    by (eapply binds_mid_eq; [ exact Hbx1 | exact Hu1' ]).
  unfold bx in HA''. inversion HA''; subst A''.
  (* ---- 4. the freshness pack ---- *)
  assert (HxΞ : x `notin` (dom Ξ `union` ftvar_in_aenv Ξ))
    by (eapply a_wf_aenv_notin_ftv_tm_prefix;
        [ exact Hsuf | exact Hwf1' | exact I ]).
  assert (HxΘ2 : x `notin` (dom Θ2 `union` ftvar_in_aenv Θ2))
    by (eapply a_wf_aenv_notin_ftv_tm_below; exact Hwf1').
  assert (HwfQ' : (Ξ ++ (x ~ bx) ++ Θ2) ⨟ empty ⊢ₚₛᵃ Q')
    by (eapply a_pat_output_wf;
        [ exact Hrun | exact Hwf0x | exact Hsklx
        | apply a_wf_pskl__hole | apply a_sk_mode_compat__tc | exact Hexpx ]).
  assert (HxQ' : x `notin` ftvar_in_pskl Q')
    by (eapply a_wf_pskl_notin_ftv_tm;
        [ exact HwfQ' | exact Hu1' | exact Hbx1 | exact I ]).
  (* ---- 5. the run ---- *)
  exists (pskl_tophole (pskl_arrow (ptyp_to_pskl A) Q')), (Ξ ++ Θ2).
  split.
  { apply a_pat__abs_anno_check
      with (L := dom Θ0 `union` ftvar_in_aenv Θ0
                 `union` dom Ξ `union` ftvar_in_aenv Ξ
                 `union` dom Θ2 `union` ftvar_in_aenv Θ2
                 `union` ftvar_in_pskl Q'
                 `union` fvar_in_exp e `union` ftvar_in_exp e
                 `union` ftvar_in_ptyp A
                 `union` singleton x);
      [ exact Hsuf | ].
    intros z Hz.
    pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Hup.
    pose proof (fvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Hvup.
    simpl in Hup, Hvup.
    pose proof (@a_pat_rename_tm x z _ _ _ _ _ _ Hrun
                  ltac:(clear - Hx Hup; solve_notin_auto)
                  ltac:(clear - Hz Hup; solve_notin_auto)
                  ltac:(clear - Hz Hvup; solve_notin_auto)) as Hsw.
    rewrite (@swap_aenv_tm_head x z bx Θ0
               ltac:(simpl; clear - Hx; solve_notin_auto)
               ltac:(simpl; clear - Hz; solve_notin_auto)) in Hsw.
    rewrite swap_aenv_app in Hsw.
    rewrite (@swap_aenv_tm_head x z (abind_var_typ A) Θ2
               ltac:(simpl; clear - HxΘ2 Hx; solve_notin_auto)
               ltac:(simpl; clear - Hz; solve_notin_auto)) in Hsw.
    rewrite (@swap_aenv_fresh_eq x z Ξ
               ltac:(clear - HxΞ; solve_notin_auto)
               ltac:(clear - Hz; solve_notin_auto)) in Hsw.
    rewrite (@swap_pskl_fresh_id x z Q'
               ltac:(clear - HxQ'; solve_notin_auto)
               ltac:(clear - Hz; solve_notin_auto)) in Hsw.
    rewrite <- (@subst_exp_in_exp_intro x e (exp_var_f z)
                  ltac:(clear - Hx; solve_notin_auto)) in Hsw.
    exact Hsw. }
  (* ---- 6. optimality ---- *)
  intros κ1 Hid1 Hinc1.
  assert (Heqκ : κ1 = κid)
    by (eapply a_inc_id_msubst_unique;
        [ exact Hinc1 | exact Hincid' | exact Hid1 | exact Hidκ ]).
  assert (HmsA1 : msubst_ptyp κ1 A = A)
    by (eapply msubst_ptyp_rigid_id;
        [ exact Hinc1 | exact Hwf0 | exact HrigA ]).
  assert (Hinc1x : κ1 ∷ ((x ~ bx) ++ Θ0) ⊑ (Ξ ++ (x ~ bx) ++ Θ2)).
  { apply (@a_inc__var Θ0 κ1 Θ2 Ξ x A A);
      [ rewrite Heqκ; exact Hincid'
      | rewrite HmsA1; apply a_tyequiv__refl; exact HlcA
      | exact Hsuf ]. }
  destruct (Hopt κ1 Hid1 Hinc1x) as [ζ [Hζ [Heqv Hprec]]].
  assert (Hζs : ζ ∷ (Ξ ++ Θ2) ⊑ Θ).
  { exact (@a_inc_strip_tm_head Ξ x (abind_var_typ A)
             (abind_var_typ A) Θ2 ζ Θ Hsuf
             (fun h : abind_is_ty (abind_var_typ A) => h)
             (fun h : abind_is_ty (abind_var_typ A) => h)
             Hwf1' HwfΘx Hζ). }
  exists ζ.
  split; [ exact Hζs | ].
  split.
  { eapply a_inc_equiv_strip_var_typ_head; [ exact Heqv | exact I ]. }
  { (* the precision, rebuilt through ⊤(⌈A⌉ → ·) *)
    unfold ad_precise in Hprec |- *.
    rewrite bskl_to_pskl_pskl_to_bskl_syn in Hprec.
    cbn [msubst_pskl bskl_to_pskl pskl_to_bskl_inh].
    rewrite btyp_to_bskl_ptyp_to_btyp_syn.
    rewrite !bskl_to_pskl_pskl_to_bskl_syn.
    rewrite msubst_pskl_embed_ptyp.
    assert (HmsAζ : msubst_ptyp ζ A = A).
    { eapply msubst_ptyp_rigid_id with (Θ0 := Ξ ++ Θ2);
        [ exact Hζs
        | exact (@a_wf_aenv_strip_tm_mid Ξ x (abind_var_typ A) Θ2
                   (fun h : abind_is_ty (abind_var_typ A) => h) Hwf1')
        | intros α Hα; apply binds_app_3;
          eapply a_inc_binds_tvar;
            [ exact Hincid' | apply HrigA; exact Hα ] ]. }
    rewrite HmsAζ.
    apply ad_refine_syn__tophole_keep.
    { apply guarded_bskl__arrow;
        [ apply lc_pskl_to_bskl_inh; apply lc_ptyp_to_pskl; exact HlcA
        | apply lc_pskl_to_bskl_inh; eapply a_wf_pskl_lc; exact HwfP ]. }
    apply ad_refine_syn__arrow.
    - apply ad_precise_refl.
      apply a_wf_ptyp_to_wf_pskl. exact HwfA.
    - eapply ad_refine_syn_mono;
        [ exact Hprec
        | apply (@aenv_tbinds_le_strip_tm nil x bx Θ); intros h; exact h ]. }
Qed.

(* ===================================================================== *)
(*  Context precision is REFLEXIVE on a paper-wf context.  [a_wf_aenv]    *)
(*  deliberately under-approximates the paper's [Θ ⊢ ctx] at skeleton     *)
(*  term entries (scope only), so the payload-wf DISCIPLINE is a          *)
(*  hypothesis — the WF-SIDE-CONDITIONS pattern, exactly as theorem 1     *)
(*  carries it.                                                           *)
(* ===================================================================== *)

Lemma ad_ctx_precise_refl : forall Θ,
  a_wf_aenv Θ ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ -> Θ ⨟ empty ⊢ₚₛᵃ Ps) ->
  Θ ⪯ᶜᵗˣ Θ.
Proof.
  intros Θ Hwf; induction Hwf; intros Hd.
  - apply ad_ctx_precise__nil.
  - apply ad_ctx_precise__copy; [ intros h; exact h | ].
    apply IHHwf. intros y Ps Hb.
    eapply a_wf_pskl_strengthen with (Θ := (α ~ abind_flex_mono) ++ Θ);
      [ eapply Hd; apply binds_cons_3; exact Hb
      | constructor; [ apply a_wf_aenv_uniq; exact Hwf | exact H ]
      | intros z Hz; clear - Hz; fsetdec
      | intros z b Hb'; apply binds_cons_3; exact Hb'
      | intros β Hβ; right;
        assert (Hsub : ftvar_in_pskl Ps [<=] dom Θ) by (eapply a_wf_aenv_binds_var_skl_ftv; eassumption);
        clear - Hβ Hsub; fsetdec ].
  - apply ad_ctx_precise__copy; [ intros h; exact h | ].
    apply IHHwf. intros y Ps Hb.
    eapply a_wf_pskl_strengthen with (Θ := (α ~ abind_flex_mono_def τ) ++ Θ);
      [ eapply Hd; apply binds_cons_3; exact Hb
      | constructor; [ apply a_wf_aenv_uniq; exact Hwf | exact H ]
      | intros z Hz; clear - Hz; fsetdec
      | intros z b Hb'; apply binds_cons_3; exact Hb'
      | intros β Hβ; right;
        assert (Hsub : ftvar_in_pskl Ps [<=] dom Θ) by (eapply a_wf_aenv_binds_var_skl_ftv; eassumption);
        clear - Hβ Hsub; fsetdec ].
  - (* skeleton term entry: the discipline supplies the tail wf *)
    eapply ad_ctx_precise__tm with (P' := P) (P := P);
      [ simpl; reflexivity | simpl; reflexivity | | ].
    + apply ad_precise_refl.
      eapply a_wf_pskl_strengthen with (Θ := (x ~ abind_var_skl P) ++ Θ);
        [ eapply Hd; unfold binds; simpl; left; reflexivity
        | constructor; [ apply a_wf_aenv_uniq; exact Hwf | exact H ]
        | intros z Hz; clear - Hz; fsetdec
        | intros z b Hb'; apply binds_cons_3; exact Hb'
        | intros β Hβ; right;
          pose proof (a_scope_pskl_ftv_dom' H0) as Hsub;
          clear - Hβ Hsub; fsetdec ].
    + apply IHHwf. intros y Ps Hb.
      eapply a_wf_pskl_strengthen with (Θ := (x ~ abind_var_skl P) ++ Θ);
        [ eapply Hd; apply binds_cons_3; exact Hb
        | constructor; [ apply a_wf_aenv_uniq; exact Hwf | exact H ]
        | intros z Hz; clear - Hz; fsetdec
        | intros z b Hb'; apply binds_cons_3; exact Hb'
        | intros β Hβ; right;
          assert (Hsub : ftvar_in_pskl Ps [<=] dom Θ) by (eapply a_wf_aenv_binds_var_skl_ftv; eassumption);
          clear - Hβ Hsub; fsetdec ].
  - (* type term entry: its wf is ON the wf-aenv rule *)
    eapply ad_ctx_precise__tm
      with (P' := ptyp_to_pskl A) (P := ptyp_to_pskl A);
      [ simpl; reflexivity | simpl; reflexivity | | ].
    + apply ad_precise_refl. apply a_wf_ptyp_to_wf_pskl. exact H0.
    + apply IHHwf. intros y Ps Hb.
      eapply a_wf_pskl_strengthen with (Θ := (x ~ abind_var_typ A) ++ Θ);
        [ eapply Hd; apply binds_cons_3; exact Hb
        | constructor; [ apply a_wf_aenv_uniq; exact Hwf | exact H ]
        | intros z Hz; clear - Hz; fsetdec
        | intros z b Hb'; apply binds_cons_3; exact Hb'
        | intros β Hβ; right;
          assert (Hsub : ftvar_in_pskl Ps [<=] dom Θ) by (eapply a_wf_aenv_binds_var_skl_ftv; eassumption);
          clear - Hβ Hsub; fsetdec ].
  - apply ad_ctx_precise__copy; [ intros h; exact h | ].
    apply IHHwf. intros y Ps Hb.
    eapply a_wf_pskl_strengthen with (Θ := (α ~ abind_tvar) ++ Θ);
      [ eapply Hd; apply binds_cons_3; exact Hb
      | constructor; [ apply a_wf_aenv_uniq; exact Hwf | exact H ]
      | intros z Hz; clear - Hz; fsetdec
      | intros z b Hb'; apply binds_cons_3; exact Hb'
      | intros β Hβ; right;
        assert (Hsub : ftvar_in_pskl Ps [<=] dom Θ) by (eapply a_wf_aenv_binds_var_skl_ftv; eassumption);
        clear - Hβ Hsub; fsetdec ].
Qed.

(* ===================================================================== *)
(*  P-Abs, the step lemma.                                                *)
(* ===================================================================== *)

Lemma a_pat_complete_abs : forall M Θ0 P0 e κ Θ Q,
  a_wf_aenv Θ0 -> a_wf_aenv Θ ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  a_sk_mode_compat M P0 ->
  M <> mode_tc ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_abs e) -> binds α abind_tvar Θ0) ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ0 -> Θ0 ⨟ empty ⊢ₚₛᵃ Ps) ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ -> Θ ⨟ empty ⊢ₚₛᵃ Ps) ->
  lc_exp (exp_abs e) ->
  (forall x M' Θ0' P0' κ' Θ' Q',
     a_wf_aenv Θ0' -> a_wf_aenv Θ' ->
     Θ0' ⨟ empty ⊢ₚₛᵃ P0' ->
     a_sk_mode_compat M' P0' ->
     κ' ∷ Θ0' ⊑ Θ' ->
     (forall α, α `in` ftvar_in_exp (open_exp_wrt_exp e (exp_var_f x)) ->
        binds α abind_tvar Θ0') ->
     (forall y Ps, binds y (abind_var_skl Ps) Θ0' -> Θ0' ⨟ empty ⊢ₚₛᵃ Ps) ->
     (forall y Ps, binds y (abind_var_skl Ps) Θ' -> Θ' ⨟ empty ⊢ₚₛᵃ Ps) ->
     lc_exp (open_exp_wrt_exp e (exp_var_f x)) ->
     Θ' ⊢ᵃ[ M' ] (open_exp_wrt_exp e (exp_var_f x)) ⇨ Q' ->
     Θ' ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ' P0')) ⊳ Q' ->
     pat_complete_concl M' Θ0' P0' (open_exp_wrt_exp e (exp_var_f x)) κ' Θ' Q') ->
  Θ ⊢ᵃ[ M ] (exp_abs e) ⇨ Q ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q ->
  pat_complete_concl M Θ0 P0 (exp_abs e) κ Θ Q.
Proof.
  intros M Θ0 P0 e κ Θ Q Hwf0 HwfΘ HwfP0 Hmod HMne Hinc Hrig Hskl HsklT
         Hlc IH Hd Href.
  inversion Hd; subst; [ | exfalso; auto ].
  match goal with
  | H : forall x, x `notin` ?L0 -> _ ⊢ᵃ[ _ ] _ ⇨ _ |- _ =>
      rename H into Hbody; rename L0 into L
  end.
  match goal with
  | H : Θ ⨟ empty ⊢ₚₛᵃ ?PP |- _ => rename H into HwfPrule; rename PP into P
  end.
  match goal with
  | H : _ ⊢ᵃ[ M ] exp_abs e ⇨ _ |- _ => clear H
  end.
  simpl in Hrig.
  (* ---- 1. K5: split the question input ---- *)
  destruct (a_split_complete Θ0 Hmod HMne)
    as [P1 [Q1 [Hsplit [HmodQ1 Hshape]]]].
  (* ---- 2. the solution's refinement, inverted along the split ---- *)
  assert (Hpieces :
      (Θ ⨟ empty ⊢ₚᵣᵃ (msubst_pskl κ P1) ⊑ P) /\
      (Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ Q1)) ⊳ Q0) /\
      (Θ0 ⨟ empty ⊢ₚₛᵃ P1) /\ (Θ0 ⨟ empty ⊢ₚₛᵃ Q1)).
  { destruct Hshape as [[-> [-> ->]] | ->].
    - (* ◇ ▹ ◇ ⇢ ◇ : the solution's refinement is a hole-fill *)
      cbn [msubst_pskl pskl_to_bskl_inh] in Href.
      inversion Href; subst.
      match goal with
      | Hp : pskl_to_bskl_syn ?PF = _, Hw : _ ⨟ empty ⊢ₚₛᵃ ?PF |- _ =>
          destruct PF; simpl in Hp; try discriminate;
          inversion Hp; subst; inversion Hw; subst
      end.
      repeat split.
      + unfold ad_precise. cbn [msubst_pskl pskl_to_bskl_inh].
        match goal with
        | Hpa : pskl_to_bskl_syn ?Pa = pskl_to_bskl_inh P |- _ =>
            rewrite <- Hpa
        end.
        apply ad_refine_syn__hole. assumption.
      + cbn [msubst_pskl pskl_to_bskl_inh].
        apply ad_refine_syn__hole. assumption.
      + apply a_wf_pskl__hole.
      + apply a_wf_pskl__hole.
    - (* the arrow shape : structural inversion *)
      cbn [msubst_pskl pskl_to_bskl_inh] in Href.
      inversion Href; subst.
      inversion HwfP0; subst.
      repeat split; assumption. }
  destruct Hpieces as [Hprec13 [Href14 [HwfP1 HwfQ1]]].
  assert (HwfP1κ : Θ ⨟ empty ⊢ₚₛᵃ (msubst_pskl κ P1))
    by (eapply a_wf_pskl_msubst_inc;
        [ exact Hinc | exact Hwf0 | exact HwfP1
        | intros α Hα; clear - Hα; fsetdec ]).
  (* ---- 3. one fresh binder ---- *)
  destruct (atom_fresh (L `union` dom Θ0 `union` ftvar_in_aenv Θ0
                          `union` dom Θ `union` ftvar_in_aenv Θ
                          `union` fvar_in_exp e `union` ftvar_in_exp e
                          `union` ftvar_in_pskl P1 `union` ftvar_in_pskl Q1
                          `union` ftvar_in_pskl P)) as [x Hx].
  set (bq := abind_var_skl P1).
  set (bs := abind_var_skl (msubst_pskl κ P1)).
  assert (Hwf0x : a_wf_aenv ((x ~ bq) ++ Θ0)).
  { apply a_wf_aenv__var;
      [ clear - Hx; fsetdec
      | eapply a_wf_pskl_to_a_scope_pskl;
          [ exact HwfP1 | intros z b Hb; exact Hb
          | intros α Hα; clear - Hα; fsetdec ]
      | exact Hwf0 ]. }
  assert (HwfΘx : a_wf_aenv ((x ~ bs) ++ Θ)).
  { apply a_wf_aenv__var;
      [ clear - Hx; fsetdec
      | eapply a_wf_pskl_to_a_scope_pskl;
          [ exact HwfP1κ | intros z b Hb; exact Hb
          | intros α Hα; clear - Hα; fsetdec ]
      | exact HwfΘ ]. }
  assert (HwfΘxP : a_wf_aenv ((x ~ abind_var_skl P) ++ Θ)).
  { apply a_wf_aenv__var;
      [ clear - Hx; fsetdec
      | eapply a_wf_pskl_to_a_scope_pskl;
          [ exact HwfPrule | intros z b Hb; exact Hb
          | intros α Hα; clear - Hα; fsetdec ]
      | exact HwfΘ ]. }
  assert (Hincx : κ ∷ ((x ~ bq) ++ Θ0) ⊑ ((x ~ bs) ++ Θ)).
  { apply (@a_inc__var_skl Θ0 κ Θ nil x P1 (msubst_pskl κ P1));
      [ exact Hinc
      | apply a_pskl_tyequiv__refl; eapply a_wf_pskl_lc; exact HwfP1κ
      | apply a_suffix__nil ]. }
  assert (Hlcbody : lc_exp (open_exp_wrt_exp e (exp_var_f x)))
    by (inversion Hlc; auto).
  assert (Hrigx : forall α,
             α `in` ftvar_in_exp (open_exp_wrt_exp e (exp_var_f x)) ->
             binds α abind_tvar ((x ~ bq) ++ Θ0)).
  { intros α Hα.
    pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Hup.
    simpl in Hup.
    apply binds_cons_3. apply Hrig. clear - Hα Hup; fsetdec. }
  assert (Hsklx : forall y Ps, binds y (abind_var_skl Ps) ((x ~ bq) ++ Θ0) ->
             ((x ~ bq) ++ Θ0) ⨟ empty ⊢ₚₛᵃ Ps).
  { intros y Ps Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> Heq] | Hb'].
    - inversion Heq; subst.
      eapply a_wf_pskl_mono; [ exact HwfP1 | ].
      intros α c _ Hc. apply binds_cons_3. exact Hc.
    - eapply a_wf_pskl_mono; [ eapply Hskl; exact Hb' | ].
      intros α c _ Hc. apply binds_cons_3. exact Hc. }
  assert (HsklTx : forall y Ps, binds y (abind_var_skl Ps) ((x ~ bs) ++ Θ) ->
             ((x ~ bs) ++ Θ) ⨟ empty ⊢ₚₛᵃ Ps).
  { intros y Ps Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> Heq] | Hb'].
    - inversion Heq; subst.
      eapply a_wf_pskl_mono; [ exact HwfP1κ | ].
      intros α c _ Hc. apply binds_cons_3. exact Hc.
    - eapply a_wf_pskl_mono; [ eapply HsklT; exact Hb' | ].
      intros α c _ Hc. apply binds_cons_3. exact Hc. }
  (* ---- 4. move the body derivation to the precise context (§5) ---- *)
  assert (Hctx : ((x ~ bs) ++ Θ) ⪯ᶜᵗˣ ((x ~ abind_var_skl P) ++ Θ)).
  { eapply ad_ctx_precise__tm
      with (P' := msubst_pskl κ P1) (P := P);
      [ simpl; reflexivity | simpl; reflexivity
      | exact Hprec13
      | apply ad_ctx_precise_refl; [ exact HwfΘ | exact HsklT ] ]. }
  pose proof (ad_ctx_precise_pat (Hbody x ltac:(clear - Hx; solve_notin_auto))
                Hctx HwfΘxP HwfΘx) as Hbodyx.
  (* ---- 5. the IH, once ---- *)
  destruct (IH x (decr_mode M) ((x ~ bq) ++ Θ0) Q1 κ ((x ~ bs) ++ Θ) Q0
              Hwf0x HwfΘx
              ltac:(eapply a_wf_pskl_mono;
                    [ exact HwfQ1
                    | intros α c _ Hc; apply binds_cons_3; exact Hc ])
              HmodQ1 Hincx Hrigx Hsklx HsklTx Hlcbody Hbodyx
              ltac:(eapply ad_refine_syn_mono;
                    [ exact Href14
                    | intros α c Hty Hc; apply binds_cons_3; exact Hc ]))
    as [Q' [Θ1' [Hrun Hopt]]].
  (* ---- 6. the run's identity increase shapes the output ---- *)
  assert (Hexpx : a_wf_exp ((x ~ bq) ++ Θ0) (open_exp_wrt_exp e (exp_var_f x))).
  { apply a_wf_exp_of_tvarish; [ exact Hlcbody | ].
    intros α Hα. left. apply Hrigx. exact Hα. }
  assert (HwfQ1x : ((x ~ bq) ++ Θ0) ⨟ empty ⊢ₚₛᵃ Q1)
    by (eapply a_wf_pskl_mono;
        [ exact HwfQ1
        | intros α c _ Hc; apply binds_cons_3; exact Hc ]).
  destruct (a_pat_sound Hrun Hwf0x Hsklx HwfQ1x HmodQ1 Hexpx)
    as [Hle [Hwf1' _]].
  destruct Hle as [[κid [Hidκ Hincid]] _].
  destruct (a_inc_var_skl_inv Hincid) as [Ξ [P'' [Θ2 [-> [_ [Hsuf Hincid']]]]]].
  assert (Hu1' : uniq (Ξ ++ (x ~ abind_var_skl P'') ++ Θ2))
    by (apply a_wf_aenv_uniq; exact Hwf1').
  assert (Hbx1 : binds x bq (Ξ ++ (x ~ abind_var_skl P'') ++ Θ2))
    by (eapply a_pat_tm_le;
        [ exact Hrun | exact I | unfold binds; simpl; auto ]).
  assert (HP'' : bq = abind_var_skl P'')
    by (eapply binds_mid_eq; [ exact Hbx1 | exact Hu1' ]).
  unfold bq in HP''. inversion HP''; subst P''.
  (* ---- 7. the freshness pack ---- *)
  assert (HxΞ : x `notin` (dom Ξ `union` ftvar_in_aenv Ξ))
    by (eapply a_wf_aenv_notin_ftv_tm_prefix;
        [ exact Hsuf | exact Hwf1' | exact I ]).
  assert (HxΘ2 : x `notin` (dom Θ2 `union` ftvar_in_aenv Θ2))
    by (eapply a_wf_aenv_notin_ftv_tm_below; exact Hwf1').
  assert (HwfQ' : (Ξ ++ (x ~ bq) ++ Θ2) ⨟ empty ⊢ₚₛᵃ Q')
    by (eapply a_pat_output_wf;
        [ exact Hrun | exact Hwf0x | exact Hsklx
        | exact HwfQ1x | exact HmodQ1 | exact Hexpx ]).
  assert (HxQ' : x `notin` ftvar_in_pskl Q')
    by (eapply a_wf_pskl_notin_ftv_tm;
        [ exact HwfQ' | exact Hu1' | exact Hbx1 | exact I ]).
  (* ---- 8. the run ---- *)
  exists (pskl_arrow P1 Q'), (Ξ ++ Θ2).
  split.
  { eapply a_pat__abs
      with (L := dom Θ0 `union` ftvar_in_aenv Θ0
                 `union` dom Ξ `union` ftvar_in_aenv Ξ
                 `union` dom Θ2 `union` ftvar_in_aenv Θ2
                 `union` ftvar_in_pskl Q'
                 `union` ftvar_in_pskl P1 `union` ftvar_in_pskl Q1
                 `union` fvar_in_exp e `union` ftvar_in_exp e
                 `union` singleton x);
      [ exact HMne | exact Hsplit | exact Hsuf | ].
    intros z Hz.
    pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Hup.
    pose proof (fvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Hvup.
    simpl in Hup, Hvup.
    pose proof (@a_pat_rename_tm x z _ _ _ _ _ _ Hrun
                  ltac:(clear - Hx Hup; solve_notin_auto)
                  ltac:(clear - Hz Hup; solve_notin_auto)
                  ltac:(clear - Hz Hvup; solve_notin_auto)) as Hsw.
    rewrite (@swap_aenv_tm_head x z bq Θ0
               ltac:(simpl; clear - Hx; solve_notin_auto)
               ltac:(simpl; clear - Hz; solve_notin_auto)) in Hsw.
    rewrite swap_aenv_app in Hsw.
    rewrite (@swap_aenv_tm_head x z (abind_var_skl P1) Θ2
               ltac:(simpl; clear - HxΘ2 Hx; solve_notin_auto)
               ltac:(simpl; clear - Hz; solve_notin_auto)) in Hsw.
    rewrite (@swap_aenv_fresh_eq x z Ξ
               ltac:(clear - HxΞ; solve_notin_auto)
               ltac:(clear - Hz; solve_notin_auto)) in Hsw.
    rewrite (@swap_pskl_fresh_id x z Q'
               ltac:(clear - HxQ'; solve_notin_auto)
               ltac:(clear - Hz; solve_notin_auto)) in Hsw.
    rewrite (@swap_pskl_fresh_id x z Q1
               ltac:(clear - Hx; solve_notin_auto)
               ltac:(clear - Hz; solve_notin_auto)) in Hsw.
    rewrite <- (@subst_exp_in_exp_intro x e (exp_var_f z)
                  ltac:(clear - Hx; solve_notin_auto)) in Hsw.
    exact Hsw. }
  (* ---- 9. optimality ---- *)
  intros κ1 Hid1 Hinc1.
  assert (Heqκ : κ1 = κid)
    by (eapply a_inc_id_msubst_unique;
        [ exact Hinc1 | exact Hincid' | exact Hid1 | exact Hidκ ]).
  assert (Hinc1x : κ1 ∷ ((x ~ bq) ++ Θ0) ⊑ (Ξ ++ (x ~ bq) ++ Θ2)).
  { apply (@a_inc__var_skl Θ0 κ1 Θ2 Ξ x P1 P1);
      [ rewrite Heqκ; exact Hincid'
      | rewrite (msubst_pskl_id P1 Hid1);
        apply a_pskl_tyequiv__refl; eapply a_wf_pskl_lc; exact HwfP1
      | exact Hsuf ]. }
  destruct (Hopt κ1 Hid1 Hinc1x) as [ζ [Hζ [Heqv Hprec]]].
  assert (Hζs : ζ ∷ (Ξ ++ Θ2) ⊑ Θ).
  { exact (@a_inc_strip_tm_head Ξ x bq bs Θ2 ζ Θ Hsuf
             (fun h : abind_is_ty bq => h)
             (fun h : abind_is_ty bs => h)
             Hwf1' HwfΘx Hζ). }
  assert (Heqvs : a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ)
    by (eapply a_inc_equiv_strip_var_skl_head; [ exact Heqv | exact I ]).
  exists ζ.
  split; [ exact Hζs | ].
  split; [ exact Heqvs | ].
  { (* the precision: the domain along the equivalence, the codomain from
       the IH *)
    assert (Hwfmid : a_wf_aenv (Ξ ++ Θ2))
      by (exact (@a_wf_aenv_strip_tm_mid Ξ x bq Θ2
                   (fun h : abind_is_ty bq => h) Hwf1')).
    assert (Hσ : msubst_compose ζ κ1 ∷ Θ0 ⊑ Θ)
      by (eapply a_inc_compose;
          [ exact Hinc1 | exact Hwf0 | exact Hwfmid | exact Hζs ]).
    assert (Hpp : Θ ⨟ empty ⊢ₚᵣᵃ
                    (msubst_pskl (msubst_compose ζ κ1) P1) ⊑ (msubst_pskl κ P1)).
    { eapply a_inc_equiv_precise_msubst_flip with (Θ0 := Θ0) (Δ0 := empty);
        [ exact HwfP1 | exact Hwf0 | exact HwfΘ | exact Hinc | exact Hσ
        | exact Heqvs | clear; fsetdec ]. }
    assert (Hdom : Θ ⨟ empty ⊢ᵣᵃ
                     (pskl_to_bskl_inh (msubst_pskl (msubst_compose ζ κ1) P1))
                     ⊳ (pskl_to_bskl_inh P)).
    { eapply ad_precise_preserves_refine;
        [ exact Hpp
        | exact Hprec13
        | exact HwfΘ
        | intros α Hα; clear - Hα; fsetdec
        | rewrite bskl_to_pskl_pskl_to_bskl_inh; exact HwfPrule ]. }
    assert (Hms : msubst_pskl (msubst_compose ζ κ1) P1 = msubst_pskl ζ P1).
    { rewrite msubst_pskl_compose.
      - rewrite (msubst_pskl_id P1 Hid1). reflexivity.
      - intros α Hα.
        destruct (a_wf_pskl_ftv_tvarish HwfP1 Hα) as [HΔ | Htv];
          [ exfalso; clear - HΔ; fsetdec | ].
        destruct Htv as [Hb | [Hb | [τ Hb]]].
        + right.
          eapply a_inc_rigid_notin_dom;
            [ exact Hζs | exact Hwfmid
            | apply binds_app_3; eapply a_inc_binds_tvar;
                [ exact Hincid' | exact Hb ] ].
        + left. eapply a_inc_flex_dom;
            [ exact Hinc1 | exact Hwf0 | left; exact Hb ].
        + left. eapply a_inc_flex_dom;
            [ exact Hinc1 | exact Hwf0 | right; exists τ; exact Hb ]. }
    unfold ad_precise in Hprec |- *.
    cbn [msubst_pskl bskl_to_pskl pskl_to_bskl_inh].
    rewrite bskl_to_pskl_pskl_to_bskl_inh.
    apply ad_refine_syn__arrow.
    - rewrite <- Hms. exact Hdom.
    - eapply ad_refine_syn_mono;
        [ exact Hprec
        | apply (@aenv_tbinds_le_strip_tm nil x bs Θ); intros h; exact h ]. }
Qed.

(* ===================================================================== *)
(*  A type's SYN painting is consistent with any of its BID paintings —   *)
(*  the fact the paper invokes as "consistency of syn{A} with bid{A}"     *)
(*  (thm:complete-skeleton-inference, AbsAnno).                           *)
(* ===================================================================== *)

Lemma ad_pat_consis_syn_bid : forall Θ A,
  a_wf_ptyp Θ A ->
  forall B : btyp, btyp_to_ptyp B = A ->
  empty ⨟ Θ ⊢ₛᵃ (ptyp_to_uskl_syn A) ∼ (btyp_to_bskl B).
Proof.
  intros Θ A Hwf; induction Hwf; intros B HB.
  - destruct B; simpl in HB; try discriminate.
    apply ad_pat_consis__unit. clear; fsetdec.
  - destruct B; simpl in HB; try discriminate.
    inversion HB; subst.
    apply ad_pat_consis__var; [ clear; fsetdec | assumption ].
  - destruct B; simpl in HB; try discriminate.
    inversion HB; subst.
    eapply ad_pat_consis__arrow with (Ψ1 := empty) (Ψ2 := empty);
      [ apply IHHwf1; reflexivity
      | apply IHHwf2; reflexivity
      | clear; fsetdec ].
  - destruct B as [ | | | | B0 | B0 ]; simpl in HB; try discriminate;
      inversion HB; subst.
    + (* syn ∀ against syn ∀ *)
      apply ad_pat_consis__forall_syn
        with (L := L) (R := ptyp_to_uskl_syn (btyp_to_ptyp B0)).
      intros α Hα.
      rewrite <- ptyp_to_uskl_syn_open.
      change (bskl_var_f α) with (btyp_to_bskl (btyp_var_f α)).
      rewrite <- btyp_to_bskl_open.
      apply H0; [ exact Hα | ].
      rewrite btyp_to_ptyp_open_var. reflexivity.
    + (* syn ∀ against inh ∀ *)
      apply ad_pat_consis__forall_inh_untagged
        with (L := L) (R := ptyp_to_uskl_syn (btyp_to_ptyp B0)).
      intros α Hα.
      rewrite <- ptyp_to_uskl_syn_open.
      change (bskl_var_f α) with (btyp_to_bskl (btyp_var_f α)).
      rewrite <- btyp_to_bskl_open.
      apply H0; [ exact Hα | ].
      rewrite btyp_to_ptyp_open_var. reflexivity.
Qed.

(* ===================================================================== *)
(*  P-AbsAnno, the step lemma.  TWO composed stages — the annotation's    *)
(*  consistency run advances the question context BEFORE the body runs — *)
(*  so the optimality glues the two factorings ([a_inc_equiv_glue],       *)
(*  exactly the consistency Arrow node's own composition).                *)
(* ===================================================================== *)

Lemma a_pat_complete_abs_anno : forall M Θ0 P0 A e κ Θ Q,
  a_wf_aenv Θ0 -> a_wf_aenv Θ ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  a_sk_mode_compat M P0 ->
  M <> mode_tc ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_abs_anno A e) -> binds α abind_tvar Θ0) ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ0 -> Θ0 ⨟ empty ⊢ₚₛᵃ Ps) ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ -> Θ ⨟ empty ⊢ₚₛᵃ Ps) ->
  lc_exp (exp_abs_anno A e) ->
  (forall x M' Θ0' P0' κ' Θ' Q',
     a_wf_aenv Θ0' -> a_wf_aenv Θ' ->
     Θ0' ⨟ empty ⊢ₚₛᵃ P0' ->
     a_sk_mode_compat M' P0' ->
     κ' ∷ Θ0' ⊑ Θ' ->
     (forall α, α `in` ftvar_in_exp (open_exp_wrt_exp e (exp_var_f x)) ->
        binds α abind_tvar Θ0') ->
     (forall y Ps, binds y (abind_var_skl Ps) Θ0' -> Θ0' ⨟ empty ⊢ₚₛᵃ Ps) ->
     (forall y Ps, binds y (abind_var_skl Ps) Θ' -> Θ' ⨟ empty ⊢ₚₛᵃ Ps) ->
     lc_exp (open_exp_wrt_exp e (exp_var_f x)) ->
     Θ' ⊢ᵃ[ M' ] (open_exp_wrt_exp e (exp_var_f x)) ⇨ Q' ->
     Θ' ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ' P0')) ⊳ Q' ->
     pat_complete_concl M' Θ0' P0' (open_exp_wrt_exp e (exp_var_f x)) κ' Θ' Q') ->
  Θ ⊢ᵃ[ M ] (exp_abs_anno A e) ⇨ Q ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q ->
  pat_complete_concl M Θ0 P0 (exp_abs_anno A e) κ Θ Q.
Proof.
  intros M Θ0 P0 A e κ Θ Q Hwf0 HwfΘ HwfP0 Hmod HMne Hinc Hrig Hskl HsklT
         Hlc IH Hd Href.
  inversion Hd; subst; [ | exfalso; auto ].
  match goal with
  | H : forall x, x `notin` ?L0 -> _ ⊢ᵃ[ _ ] _ ⇨ _ |- _ =>
      rename H into Hbody; rename L0 into L
  end.
  (* ⚙ [subst] consumed the rule's [btyp_to_ptyp B = A] equation and the
     lemma's [A] with it — rebind both from the goal (type-directed rename
     preamble). *)
  match goal with
  | |- pat_complete_concl _ _ _ (exp_abs_anno (btyp_to_ptyp ?BB) _) _ _ _ =>
      try rename BB into B
  end.
  set (A := btyp_to_ptyp B) in *.
  assert (HBA : btyp_to_ptyp B = A) by reflexivity.
  match goal with
  | H : a_wf_ptyp Θ A |- _ => rename H into HwfA
  end.
  simpl in Hrig.
  assert (HrigA : forall α, α `in` ftvar_in_ptyp A -> binds α abind_tvar Θ0)
    by (intros α Hα; apply Hrig; clear - Hα; fsetdec).
  assert (HlcA : lc_ptyp A) by (inversion Hlc; assumption).
  assert (HwfA0 : a_wf_ptyp Θ0 A)
    by (apply a_wf_ptyp_of_lc_tvarish;
        [ exact HlcA | intros α Hα; left; apply HrigA; exact Hα ]).
  assert (HmsA : msubst_ptyp κ A = A)
    by (eapply msubst_ptyp_rigid_id;
        [ exact Hinc | exact Hwf0 | exact HrigA ]).
  (* ---- 1. K5: split the question input ---- *)
  destruct (a_split_complete Θ0 Hmod HMne)
    as [P1 [Q1 [Hsplit [HmodQ1 Hshape]]]].
  (* ---- 2. the solution's refinement, inverted along the split ---- *)
  assert (Hpieces :
      (Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P1))
         ⊳ (btyp_to_bskl B)) /\
      (Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ Q1)) ⊳ Q0) /\
      (Θ0 ⨟ empty ⊢ₚₛᵃ P1) /\ (Θ0 ⨟ empty ⊢ₚₛᵃ Q1)).
  { destruct Hshape as [[-> [-> ->]] | ->].
    - cbn [msubst_pskl pskl_to_bskl_inh] in Href.
      inversion Href; subst.
      match goal with
      | Hp : pskl_to_bskl_syn ?PF = _, Hw : _ ⨟ empty ⊢ₚₛᵃ ?PF |- _ =>
          destruct PF; simpl in Hp; try discriminate;
          inversion Hp; subst; inversion Hw; subst
      end.
      repeat split.
      + cbn [msubst_pskl pskl_to_bskl_inh].
        first
          [ apply ad_refine_syn__hole; assumption
          | match goal with
            | Hpa : pskl_to_bskl_syn _ = btyp_to_bskl _ |- _ =>
                rewrite <- Hpa; apply ad_refine_syn__hole; assumption
            | Hpa : btyp_to_bskl _ = pskl_to_bskl_syn _ |- _ =>
                rewrite Hpa; apply ad_refine_syn__hole; assumption
            end ].
      + cbn [msubst_pskl pskl_to_bskl_inh].
        apply ad_refine_syn__hole. assumption.
      + apply a_wf_pskl__hole.
      + apply a_wf_pskl__hole.
    - cbn [msubst_pskl pskl_to_bskl_inh] in Href.
      inversion Href; subst.
      inversion HwfP0; subst.
      repeat split; assumption. }
  destruct Hpieces as [Href13 [Href14 [HwfP1 HwfQ1]]].
  assert (HwfpA0 : Θ0 ⨟ empty ⊢ₚₛᵃ (ptyp_to_pskl A))
    by (apply a_wf_ptyp_to_wf_pskl; exact HwfA0).
  (* ---- 3. the annotation's consistency stage (thm:complete-consistency) *)
  assert (Hjoin : empty ⨟ Θ ⊢ₛᵃ
                    (pskl_to_uskl (msubst_pskl κ (ptyp_to_pskl A)))
                    ∼ (btyp_to_bskl B)).
  { rewrite msubst_pskl_embed_ptyp, HmsA, pskl_to_uskl_ptyp.
    apply (ad_pat_consis_syn_bid HwfA B HBA). }
  assert (Hrs : ad_refine_syn_f empty Θ empty
                  (pskl_to_bskl_inh (msubst_pskl κ P1)) (btyp_to_bskl B))
    by (apply ad_refine_syn_f_of_plain; exact Href13).
  assert (Hrp : ad_refine_pskl_f empty Θ empty
                  (msubst_pskl κ (ptyp_to_pskl A))
                  (bskl_to_pskl (btyp_to_bskl B))).
  { rewrite msubst_pskl_embed_ptyp, HmsA.
    rewrite bskl_to_pskl_btyp_to_bskl, HBA.
    apply ad_refine_pskl_f_of_plain.
    apply ad_refine_pskl_refl.
    apply a_wf_ptyp_to_wf_pskl; exact HwfA. }
  destruct (a_consis_complete Hwf0 HwfP1 HwfpA0 Hinc HwfΘ Hjoin Hrs Hrp)
    as [Ac [Θmid [HcRun HoptC]]].
  destruct (a_consis_isub_wf_nil HcRun Hwf0 HwfP1 HwfpA0) as [Hlec Hwfmid].
  destruct Hlec as [[κc [Hidc Hincc]] _].
  destruct (HoptC κc Hidc Hincc) as [ζc0 [Hζc0 [Heqvc _]]].
  (* ---- 4. one fresh binder ---- *)
  destruct (atom_fresh (L `union` dom Θ0 `union` ftvar_in_aenv Θ0
                          `union` dom Θ `union` ftvar_in_aenv Θ
                          `union` dom Θmid `union` ftvar_in_aenv Θmid
                          `union` fvar_in_exp e `union` ftvar_in_exp e
                          `union` ftvar_in_ptyp A
                          `union` ftvar_in_pskl P1 `union` ftvar_in_pskl Q1))
    as [x Hx].
  set (bA := abind_var_typ A).
  assert (HrigMid : forall α, α `in` ftvar_in_ptyp A ->
             binds α abind_tvar Θmid)
    by (intros α Hα; eapply a_inc_binds_tvar;
        [ exact Hincc | apply HrigA; exact Hα ]).
  assert (HwfAmid : a_wf_ptyp Θmid A)
    by (apply a_wf_ptyp_of_lc_tvarish;
        [ exact HlcA | intros α Hα; left; apply HrigMid; exact Hα ]).
  assert (Hwf0x : a_wf_aenv ((x ~ bA) ++ Θmid))
    by (apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact HwfAmid | exact Hwfmid ]).
  assert (HwfΘx : a_wf_aenv ((x ~ bA) ++ Θ))
    by (apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact HwfA | exact HwfΘ ]).
  assert (HmsAζc : msubst_ptyp ζc0 A = A)
    by (eapply msubst_ptyp_rigid_id;
        [ exact Hζc0 | exact Hwfmid | exact HrigMid ]).
  assert (Hincx : ζc0 ∷ ((x ~ bA) ++ Θmid) ⊑ ((x ~ bA) ++ Θ)).
  { apply (@a_inc__var Θmid ζc0 Θ nil x A A);
      [ exact Hζc0
      | rewrite HmsAζc; apply a_tyequiv__refl; exact HlcA
      | apply a_suffix__nil ]. }
  assert (Hlcbody : lc_exp (open_exp_wrt_exp e (exp_var_f x)))
    by (inversion Hlc; auto).
  (* ---- 5. transport the codomain refinement to the composed κ' ---- *)
  assert (HwfQb : Θ ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q0)).
  { pose proof (ad_pat_target_wf (Hbody x ltac:(clear - Hx; solve_notin_auto)) HwfΘx)
      as Hw.
    eapply a_wf_pskl_mono;
      [ exact Hw
      | apply (@aenv_tbinds_le_strip_tm nil x bA Θ); intros h; exact h ]. }
  assert (Hσc : msubst_compose ζc0 κc ∷ Θ0 ⊑ Θ)
    by (eapply a_inc_compose;
        [ exact Hincc | exact Hwf0 | exact Hwfmid | exact Hζc0 ]).
  assert (Hpp : Θ ⨟ empty ⊢ₚᵣᵃ
                  (msubst_pskl (msubst_compose ζc0 κc) Q1) ⊑ (msubst_pskl κ Q1)).
  { eapply a_inc_equiv_precise_msubst_flip with (Θ0 := Θ0) (Δ0 := empty);
      [ exact HwfQ1 | exact Hwf0 | exact HwfΘ | exact Hinc | exact Hσc
      | exact Heqvc | clear; fsetdec ]. }
  assert (Href14σ : Θ ⨟ empty ⊢ᵣᵃ
                      (pskl_to_bskl_inh (msubst_pskl (msubst_compose ζc0 κc) Q1))
                      ⊳ Q0).
  { eapply ad_precise_preserves_refine;
      [ exact Hpp | exact Href14 | exact HwfΘ
      | intros α Hα; clear - Hα; fsetdec | exact HwfQb ]. }
  assert (Hmsc : msubst_pskl (msubst_compose ζc0 κc) Q1 = msubst_pskl ζc0 Q1).
  { eapply msubst_compose_id_pskl;
      [ exact Hwf0 | exact Hwfmid | exact Hidc | exact Hincc | exact Hζc0
      | eapply a_wf_pskl_to_a_scope_pskl;
          [ exact HwfQ1 | intros z b Hb; exact Hb
          | intros α Hα; clear - Hα; fsetdec ] ]. }
  rewrite Hmsc in Href14σ.
  (* ---- 6. the extended side data and the IH ---- *)
  assert (Hrigx : forall α,
             α `in` ftvar_in_exp (open_exp_wrt_exp e (exp_var_f x)) ->
             binds α abind_tvar ((x ~ bA) ++ Θmid)).
  { intros α Hα.
    pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Hup.
    simpl in Hup.
    apply binds_cons_3. eapply a_inc_binds_tvar;
      [ exact Hincc | apply Hrig; clear - Hα Hup; fsetdec ]. }
  assert (Hsklmid : forall y Ps, binds y (abind_var_skl Ps) Θmid ->
             Θmid ⨟ empty ⊢ₚₛᵃ Ps).
  { intros y Ps Hb.
    assert (Hb0 : binds y (abind_var_skl Ps) Θ0)
      by (eapply a_consis_tm_ge; [ exact HcRun | exact I | exact Hb ]).
    pose proof (a_wf_pskl_msubst_inc Hincc Hwf0 (Hskl _ _ Hb0)
                  ltac:(intros α Hα; clear - Hα; solve_notin_auto)) as Hw.
    rewrite (msubst_pskl_id Ps Hidc) in Hw. exact Hw. }
  assert (Hsklx : forall y Ps, binds y (abind_var_skl Ps) ((x ~ bA) ++ Θmid) ->
             ((x ~ bA) ++ Θmid) ⨟ empty ⊢ₚₛᵃ Ps).
  { intros y Ps Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> Heq] | Hb'];
      [ discriminate Heq | ].
    eapply a_wf_pskl_mono; [ eapply Hsklmid; exact Hb' | ].
    intros α c _ Hc. apply binds_cons_3. exact Hc. }
  assert (HsklTx : forall y Ps, binds y (abind_var_skl Ps) ((x ~ bA) ++ Θ) ->
             ((x ~ bA) ++ Θ) ⨟ empty ⊢ₚₛᵃ Ps).
  { intros y Ps Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> Heq] | Hb'];
      [ discriminate Heq | ].
    eapply a_wf_pskl_mono; [ eapply HsklT; exact Hb' | ].
    intros α c _ Hc. apply binds_cons_3. exact Hc. }
  assert (HwfQ1mid : Θmid ⨟ empty ⊢ₚₛᵃ Q1).
  { pose proof (a_wf_pskl_msubst_inc Hincc Hwf0 HwfQ1
                  ltac:(intros α Hα; clear - Hα; solve_notin_auto)) as Hw.
    rewrite (msubst_pskl_id Q1 Hidc) in Hw. exact Hw. }
  destruct (IH x (decr_mode M) ((x ~ bA) ++ Θmid) Q1 ζc0 ((x ~ bA) ++ Θ) Q0
              Hwf0x HwfΘx
              ltac:(eapply a_wf_pskl_mono;
                    [ exact HwfQ1mid
                    | intros α c _ Hc; apply binds_cons_3; exact Hc ])
              HmodQ1 Hincx Hrigx Hsklx HsklTx Hlcbody
              (Hbody x ltac:(clear - Hx; solve_notin_auto))
              ltac:(eapply ad_refine_syn_mono;
                    [ exact Href14σ
                    | intros α c Hty Hc; apply binds_cons_3; exact Hc ]))
    as [Q' [Θ1' [HrunB HoptB]]].
  (* ---- 7. the body run's identity increase shapes the output ---- *)
  assert (Hexpx : a_wf_exp ((x ~ bA) ++ Θmid) (open_exp_wrt_exp e (exp_var_f x))).
  { apply a_wf_exp_of_tvarish; [ exact Hlcbody | ].
    intros α Hα. left. apply Hrigx. exact Hα. }
  assert (HwfQ1midx : ((x ~ bA) ++ Θmid) ⨟ empty ⊢ₚₛᵃ Q1)
    by (eapply a_wf_pskl_mono;
        [ exact HwfQ1mid
        | intros α c _ Hc; apply binds_cons_3; exact Hc ]).
  destruct (a_pat_sound HrunB Hwf0x Hsklx HwfQ1midx HmodQ1 Hexpx)
    as [HleB [HwfB' _]].
  destruct HleB as [[κb [Hidb Hincb]] _].
  destruct (a_inc_var_inv Hincb) as [Ξ [A'' [Θ3 [-> [_ [Hsuf Hincb']]]]]].
  assert (HuB' : uniq (Ξ ++ (x ~ abind_var_typ A'') ++ Θ3))
    by (apply a_wf_aenv_uniq; exact HwfB').
  assert (Hbx1 : binds x bA (Ξ ++ (x ~ abind_var_typ A'') ++ Θ3))
    by (eapply a_pat_tm_le;
        [ exact HrunB | exact I | unfold binds; simpl; auto ]).
  assert (HA'' : bA = abind_var_typ A'')
    by (eapply binds_mid_eq; [ exact Hbx1 | exact HuB' ]).
  unfold bA in HA''. inversion HA''; subst A''.
  (* ---- 8. the freshness pack ---- *)
  assert (HxΞ : x `notin` (dom Ξ `union` ftvar_in_aenv Ξ))
    by (eapply a_wf_aenv_notin_ftv_tm_prefix;
        [ exact Hsuf | exact HwfB' | exact I ]).
  assert (HxΘ3 : x `notin` (dom Θ3 `union` ftvar_in_aenv Θ3))
    by (eapply a_wf_aenv_notin_ftv_tm_below; exact HwfB').
  assert (HwfQ' : (Ξ ++ (x ~ bA) ++ Θ3) ⨟ empty ⊢ₚₛᵃ Q')
    by (eapply a_pat_output_wf;
        [ exact HrunB | exact Hwf0x | exact Hsklx
        | exact HwfQ1midx | exact HmodQ1 | exact Hexpx ]).
  assert (HxQ' : x `notin` ftvar_in_pskl Q')
    by (eapply a_wf_pskl_notin_ftv_tm;
        [ exact HwfQ' | exact HuB' | exact Hbx1 | exact I ]).
  (* ---- 9. the run ---- *)
  exists (pskl_arrow (ptyp_to_pskl A) Q'), (Ξ ++ Θ3).
  split.
  { eapply a_pat__abs_anno
      with (L := dom Θ0 `union` ftvar_in_aenv Θ0
                 `union` dom Θmid `union` ftvar_in_aenv Θmid
                 `union` dom Ξ `union` ftvar_in_aenv Ξ
                 `union` dom Θ3 `union` ftvar_in_aenv Θ3
                 `union` ftvar_in_pskl Q'
                 `union` ftvar_in_ptyp A `union` ftvar_in_pskl Q1
                 `union` fvar_in_exp e `union` ftvar_in_exp e
                 `union` singleton x);
      [ exact HMne | exact Hsplit | exists Ac; exact HcRun | exact Hsuf | ].
    intros z Hz.
    pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Hup.
    pose proof (fvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Hvup.
    simpl in Hup, Hvup.
    pose proof (@a_pat_rename_tm x z _ _ _ _ _ _ HrunB
                  ltac:(clear - Hx Hup; solve_notin_auto)
                  ltac:(clear - Hz Hup; solve_notin_auto)
                  ltac:(clear - Hz Hvup; solve_notin_auto)) as Hsw.
    rewrite (@swap_aenv_tm_head x z bA Θmid
               ltac:(simpl; clear - Hx; solve_notin_auto)
               ltac:(simpl; clear - Hz; solve_notin_auto)) in Hsw.
    rewrite swap_aenv_app in Hsw.
    rewrite (@swap_aenv_tm_head x z (abind_var_typ A) Θ3
               ltac:(simpl; clear - HxΘ3 Hx; solve_notin_auto)
               ltac:(simpl; clear - Hz; solve_notin_auto)) in Hsw.
    rewrite (@swap_aenv_fresh_eq x z Ξ
               ltac:(clear - HxΞ; solve_notin_auto)
               ltac:(clear - Hz; solve_notin_auto)) in Hsw.
    rewrite (@swap_pskl_fresh_id x z Q'
               ltac:(clear - HxQ'; solve_notin_auto)
               ltac:(clear - Hz; solve_notin_auto)) in Hsw.
    rewrite (@swap_pskl_fresh_id x z Q1
               ltac:(clear - Hx; solve_notin_auto)
               ltac:(clear - Hz; solve_notin_auto)) in Hsw.
    rewrite <- (@subst_exp_in_exp_intro x e (exp_var_f z)
                  ltac:(clear - Hx; solve_notin_auto)) in Hsw.
    exact Hsw. }
  (* ---- 10. optimality: glue the two stages ---- *)
  intros κ1 Hid1 Hinc1.
  assert (Heqκc : κ1 = κc)
    by (eapply a_inc_id_msubst_unique;
        [ exact Hinc1 | exact Hincc | exact Hid1 | exact Hidc ]).
  assert (Hinc1b : κb ∷ ((x ~ bA) ++ Θmid) ⊑ (Ξ ++ (x ~ bA) ++ Θ3)).
  { apply (@a_inc__var Θmid κb Θ3 Ξ x A A);
      [ exact Hincb'
      | rewrite (msubst_ptyp_id A Hidb);
        apply a_tyequiv__refl; exact HlcA
      | exact Hsuf ]. }
  destruct (HoptB κb Hidb Hinc1b) as [ζb [Hζb [Heqvb Hprecb]]].
  assert (Hζbs : ζb ∷ (Ξ ++ Θ3) ⊑ Θ).
  { exact (@a_inc_strip_tm_head Ξ x bA bA Θ3 ζb Θ Hsuf
             (fun h : abind_is_ty bA => h)
             (fun h : abind_is_ty bA => h)
             HwfB' HwfΘx Hζb). }
  assert (Heqvbs : a_inc_equiv Θmid ζc0 (msubst_compose ζb κb) Θ)
    by (eapply a_inc_equiv_strip_var_typ_head; [ exact Heqvb | exact I ]).
  assert (Hwffin : a_wf_aenv (Ξ ++ Θ3))
    by (exact (@a_wf_aenv_strip_tm_mid Ξ x bA Θ3
                 (fun h : abind_is_ty bA => h) HwfB')).
  (* the body's witness, target-weakened across the suffix *)
  assert (Hlcfin : lc_aenv Θ3)
    by (apply a_wf_aenv_lc_aenv; eapply a_wf_aenv_app_r with (Θp := Ξ ++ (x ~ bA));
        simpl_env; exact HwfB').
  destruct (a_inc_weaken_suffix_target Hincb' Hidb Hlcfin Hsuf)
    as [κb2 [Hidb2 Hincb2]].
  assert (Heqκb : κb2 = κb)
    by (eapply a_inc_id_msubst_unique;
        [ exact Hincb2 | exact Hincb' | exact Hidb2 | exact Hidb ]).
  subst κb2.
  exists ζb.
  split; [ exact Hζbs | ].
  split.
  { (* the equivalence, glued across the two stages *)
    assert (Hglue : a_inc_equiv Θ0 κ (msubst_compose ζb κc) Θ).
    { eapply a_inc_equiv_glue with
        (Θmid := Θmid) (Θfin := Ξ ++ Θ3) (κ1b := κb) (ζ1 := ζc0);
        [ exact Hwf0 | exact Hwfmid | exact Hwffin | exact HwfΘ
        | exact Hidc | exact Hidb
        | (* dom κc ⊆ dom κb : Θ0's flexes stay flexible through the run *)
          intros α Hα;
          pose proof (a_inc_dom_flex Hincc Hα) as Hfα;
          eapply a_inc_flex_dom;
            [ exact Hincb2 | exact Hwfmid
            | eapply (proj2 (proj2 a_assign_unify_consis_flex_preserve));
                [ exact HcRun | exact Hfα ] ]
        | exact Hincc | exact Hincb2 | exact Hζc0 | exact Hζbs
        | exact Heqvc | exact Heqvbs ]. }
    rewrite Heqκc. exact Hglue. }
  { (* the precision: the domain is the RIGID annotation, the codomain is
       the body's *)
    unfold ad_precise in Hprecb |- *.
    cbn [msubst_pskl bskl_to_pskl pskl_to_bskl_inh].
    rewrite bskl_to_pskl_btyp_to_bskl, HBA.
    rewrite msubst_pskl_embed_ptyp.
    assert (HmsAζb : msubst_ptyp ζb A = A).
    { eapply msubst_ptyp_rigid_id with (Θ0 := Ξ ++ Θ3);
        [ exact Hζbs | exact Hwffin
        | intros α Hα; apply binds_app_3;
          eapply a_inc_binds_tvar;
            [ exact Hincb' | apply HrigMid; exact Hα ] ]. }
    rewrite HmsAζb.
    apply ad_refine_syn__arrow.
    - apply ad_precise_refl.
      apply a_wf_ptyp_to_wf_pskl. exact HwfA.
    - eapply ad_refine_syn_mono;
        [ exact Hprecb
        | apply (@aenv_tbinds_le_strip_tm nil x bA Θ); intros h; exact h ]. }
Qed.

(* ===================================================================== *)
(*  An IDENTITY increase preserves flexibility: the peeled flexible's     *)
(*  image is the variable itself, whose wf pins a type-level entry in     *)
(*  the target, and a RIGID one would have had to come from the source    *)
(*  ([a_inc_binds_tvar_rev]) where the atom is already flexible.          *)
(* ===================================================================== *)

Lemma a_inc_id_flex_preserve : forall Θ0 κ Θ1 α,
  κ ∷ Θ0 ⊑ Θ1 ->
  is_id_msubst κ ->
  a_wf_aenv Θ0 ->
  a_flex_tvar Θ0 α ->
  a_flex_tvar Θ1 α.
Proof.
  intros Θ0 κ Θ1 α Hinc; induction Hinc; intros Hid Hwf Hflex.
  - (* empty *)
    exfalso. destruct Hflex as [Hb | [τ' Hb]]; inversion Hb.
  - (* flex declaration *)
    destruct (is_id_msubst_inv Hid) as [-> Hid'].
    inversion Hwf; subst.
    destruct Hflex as [Hb | [τ' Hb]];
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> Heq] | Hb'];
      try discriminate Heq;
      try solve [ apply IHHinc;
                  [ assumption | assumption
                  | unfold a_flex_tvar;
                    first [ left; exact Hb' | right; eexists; exact Hb' ] ] ].
    (* the peeled head itself: its image [var α] is wf in the target *)
    match goal with
    | Hwfv : a_wf_ptyp ?T (ptyp_var_f ?a) |- a_flex_tvar ?T ?a =>
        inversion Hwfv; subst;
        match goal with
        | Htv : a_binds_tvar a T |- _ =>
            destruct Htv as [Hb1 | [Hb1 | [τ1 Hb1]]];
              [ exfalso;
                match goal with
                | Hincr : _ ∷ _ ⊑ T |- _ =>
                    pose proof (@a_inc_binds_tvar_rev _ _ _ _ Hincr Hb1) as Hb0;
                    apply binds_In in Hb0;
                    match goal with
                    | Hfr : a `notin` dom _ |- _ => clear - Hfr Hb0; fsetdec
                    end
                end
              | unfold a_flex_tvar; left; exact Hb1
              | unfold a_flex_tvar; right; exists τ1; exact Hb1 ]
        end
    end.
  - (* flex definition *)
    destruct (is_id_msubst_inv Hid) as [-> Hid'].
    inversion Hwf; subst.
    destruct Hflex as [Hb | [τ' Hb]];
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> Heq] | Hb'];
      try discriminate Heq;
      try solve [ apply IHHinc;
                  [ assumption | assumption
                  | unfold a_flex_tvar;
                    first [ left; exact Hb' | right; eexists; exact Hb' ] ] ].
    match goal with
    | Hwfv : a_wf_ptyp ?T (ptyp_var_f ?a) |- a_flex_tvar ?T ?a =>
        inversion Hwfv; subst;
        match goal with
        | Htv : a_binds_tvar a T |- _ =>
            destruct Htv as [Hb1 | [Hb1 | [τ1 Hb1]]];
              [ exfalso;
                match goal with
                | Hincr : _ ∷ _ ⊑ T |- _ =>
                    pose proof (@a_inc_binds_tvar_rev _ _ _ _ Hincr Hb1) as Hb0;
                    apply binds_In in Hb0;
                    match goal with
                    | Hfr : a `notin` dom _ |- _ => clear - Hfr Hb0; fsetdec
                    end
                end
              | unfold a_flex_tvar; left; exact Hb1
              | unfold a_flex_tvar; right; exists τ1; exact Hb1 ]
        end
    end.
  - (* type term entry *)
    inversion Hwf; subst.
    assert (Hflex' : a_flex_tvar Θ α).
    { unfold a_flex_tvar;
        destruct Hflex as [Hb | [τ' Hb]];
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> Heq] | Hb'];
        try discriminate Heq;
        [ left; exact Hb' | right; exists τ'; exact Hb' ]. }
    destruct (IHHinc Hid ltac:(assumption) Hflex') as [Hb1 | [τ1 Hb1]];
      unfold a_flex_tvar;
      [ left | right; exists τ1 ];
      apply binds_app_3; apply binds_cons_3; exact Hb1.
  - (* skeleton term entry *)
    inversion Hwf; subst.
    assert (Hflex' : a_flex_tvar Θ α).
    { unfold a_flex_tvar;
        destruct Hflex as [Hb | [τ' Hb]];
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> Heq] | Hb'];
        try discriminate Heq;
        [ left; exact Hb' | right; exists τ'; exact Hb' ]. }
    destruct (IHHinc Hid ltac:(assumption) Hflex') as [Hb1 | [τ1 Hb1]];
      unfold a_flex_tvar;
      [ left | right; exists τ1 ];
      apply binds_app_3; apply binds_cons_3; exact Hb1.
  - (* rigid entry *)
    inversion Hwf; subst.
    assert (Hflex' : a_flex_tvar Θ α).
    { unfold a_flex_tvar;
        destruct Hflex as [Hb | [τ' Hb]];
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> Heq] | Hb'];
        try discriminate Heq;
        [ left; exact Hb' | right; exists τ'; exact Hb' ]. }
    destruct (IHHinc Hid ltac:(assumption) Hflex') as [Hb1 | [τ1 Hb1]];
      unfold a_flex_tvar;
      [ left | right; exists τ1 ];
      apply binds_app_3; apply binds_cons_3; exact Hb1.
Qed.

(* ===================================================================== *)
(*  P-App, the step lemma.  No binder and no renaming — but two composed  *)
(*  runs, glued exactly like AbsAnno's two stages.                        *)
(* ===================================================================== *)

Lemma a_pat_complete_app : forall M Θ0 P0 e1 e2 κ Θ Q,
  a_wf_aenv Θ0 -> a_wf_aenv Θ ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  a_sk_mode_compat M P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_app e1 e2) -> binds α abind_tvar Θ0) ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ0 -> Θ0 ⨟ empty ⊢ₚₛᵃ Ps) ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ -> Θ ⨟ empty ⊢ₚₛᵃ Ps) ->
  lc_exp (exp_app e1 e2) ->
  (forall M' Θ0' P0' κ' Θ' Q',
     a_wf_aenv Θ0' -> a_wf_aenv Θ' ->
     Θ0' ⨟ empty ⊢ₚₛᵃ P0' ->
     a_sk_mode_compat M' P0' ->
     κ' ∷ Θ0' ⊑ Θ' ->
     (forall α, α `in` ftvar_in_exp e2 -> binds α abind_tvar Θ0') ->
     (forall y Ps, binds y (abind_var_skl Ps) Θ0' -> Θ0' ⨟ empty ⊢ₚₛᵃ Ps) ->
     (forall y Ps, binds y (abind_var_skl Ps) Θ' -> Θ' ⨟ empty ⊢ₚₛᵃ Ps) ->
     lc_exp e2 ->
     Θ' ⊢ᵃ[ M' ] e2 ⇨ Q' ->
     Θ' ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ' P0')) ⊳ Q' ->
     pat_complete_concl M' Θ0' P0' e2 κ' Θ' Q') ->
  (forall M' Θ0' P0' κ' Θ' Q',
     a_wf_aenv Θ0' -> a_wf_aenv Θ' ->
     Θ0' ⨟ empty ⊢ₚₛᵃ P0' ->
     a_sk_mode_compat M' P0' ->
     κ' ∷ Θ0' ⊑ Θ' ->
     (forall α, α `in` ftvar_in_exp e1 -> binds α abind_tvar Θ0') ->
     (forall y Ps, binds y (abind_var_skl Ps) Θ0' -> Θ0' ⨟ empty ⊢ₚₛᵃ Ps) ->
     (forall y Ps, binds y (abind_var_skl Ps) Θ' -> Θ' ⨟ empty ⊢ₚₛᵃ Ps) ->
     lc_exp e1 ->
     Θ' ⊢ᵃ[ M' ] e1 ⇨ Q' ->
     Θ' ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ' P0')) ⊳ Q' ->
     pat_complete_concl M' Θ0' P0' e1 κ' Θ' Q') ->
  Θ ⊢ᵃ[ M ] (exp_app e1 e2) ⇨ Q ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q ->
  pat_complete_concl M Θ0 P0 (exp_app e1 e2) κ Θ Q.
Proof.
  intros M Θ0 P0 e1 e2 κ Θ Q Hwf0 HwfΘ HwfP0 Hmod Hinc Hrig Hskl HsklT
         Hlc IH2 IH1 Hd Href.
  inversion Hd; subst.
  match goal with
  | H : Θ ⊢ᵃ[ mode_tc ] e2 ⇨ pskl_to_bskl_syn ?PP |- _ =>
      rename H into Hd2; rename PP into Pn
  end.
  match goal with
  | H : Θ ⨟ empty ⊢ᵣᵃ pskl_to_bskl_inh Pn ⊳ ?QQ |- _ =>
      rename H into Hrefb; rename QQ into Qdom
  end.
  match goal with
  | H : Θ ⊢ᵃ[ mode_fn M ] e1 ⇨ bskl_arrow Qdom ?QQ |- _ =>
      rename H into Hd1
  end.
  simpl in Hrig.
  assert (Hrig2 : forall α, α `in` ftvar_in_exp e2 -> binds α abind_tvar Θ0)
    by (intros α Hα; apply Hrig; clear - Hα; fsetdec).
  assert (Hrig1 : forall α, α `in` ftvar_in_exp e1 -> binds α abind_tvar Θ0)
    by (intros α Hα; apply Hrig; clear - Hα; fsetdec).
  assert (Hlc2 : lc_exp e2) by (inversion Hlc; assumption).
  assert (Hlc1 : lc_exp e1) by (inversion Hlc; assumption).
  (* the run targets are wf (K1) *)
  assert (HwfPn : Θ ⨟ empty ⊢ₚₛᵃ Pn)
    by (pose proof (ad_pat_target_wf Hd2 HwfΘ) as Hw;
        rewrite bskl_to_pskl_pskl_to_bskl_syn in Hw; exact Hw).
  assert (Hwfarr : Θ ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl (bskl_arrow Qdom Q)))
    by (exact (ad_pat_target_wf Hd1 HwfΘ)).
  cbn [bskl_to_pskl] in Hwfarr.
  inversion Hwfarr; subst.
  match goal with
  | H : Θ ⨟ empty ⊢ₚₛᵃ bskl_to_pskl Qdom |- _ => rename H into HwfQdom
  end.
  match goal with
  | H : Θ ⨟ empty ⊢ₚₛᵃ bskl_to_pskl Q |- _ => rename H into HwfQcod
  end.
  (* ---- 1. the argument's run (e2 at TC, ◇) ---- *)
  destruct (IH2 mode_tc Θ0 pskl_hole κ Θ (pskl_to_bskl_syn Pn)
              Hwf0 HwfΘ
              ltac:(apply a_wf_pskl__hole)
              ltac:(apply a_sk_mode_compat__tc)
              Hinc Hrig2 Hskl HsklT Hlc2 Hd2
              ltac:(cbn [msubst_pskl pskl_to_bskl_inh];
                    apply ad_refine_syn__hole; exact HwfPn))
    as [P1 [Θ1 [Hrun2 Hopt2]]].
  (* its own identity increase *)
  assert (Hexp2 : a_wf_exp Θ0 e2).
  { apply a_wf_exp_of_tvarish; [ exact Hlc2 | ].
    intros α Hα. left. apply Hrig2. exact Hα. }
  destruct (a_pat_sound Hrun2 Hwf0 Hskl
              ltac:(apply a_wf_pskl__hole)
              ltac:(apply a_sk_mode_compat__tc)
              Hexp2)
    as [Hle2 [Hwf1 _]].
  destruct Hle2 as [[κa [Hida Hinca]] _].
  destruct (Hopt2 κa Hida Hinca) as [ζ1 [Hζ1 [Heqv1 Hprec1]]].
  rewrite bskl_to_pskl_pskl_to_bskl_syn in Hprec1.
  (* ---- 2. the function's input refinement at ζ1 ---- *)
  (* (h) : the domain, by precision-preserves-refinement *)
  assert (Hh : Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl ζ1 P1)) ⊳ Qdom).
  { eapply ad_precise_preserves_refine;
      [ exact Hprec1 | exact Hrefb | exact HwfΘ
      | intros α Hα; clear - Hα; fsetdec | exact HwfQdom ]. }
  (* (i) : the codomain, transported along the equivalence *)
  assert (Hσ1 : msubst_compose ζ1 κa ∷ Θ0 ⊑ Θ)
    by (eapply a_inc_compose;
        [ exact Hinca | exact Hwf0 | exact Hwf1 | exact Hζ1 ]).
  assert (Hpp : Θ ⨟ empty ⊢ₚᵣᵃ
                  (msubst_pskl (msubst_compose ζ1 κa) P0) ⊑ (msubst_pskl κ P0)).
  { eapply a_inc_equiv_precise_msubst_flip with (Θ0 := Θ0) (Δ0 := empty);
      [ exact HwfP0 | exact Hwf0 | exact HwfΘ | exact Hinc | exact Hσ1
      | exact Heqv1 | clear; fsetdec ]. }
  assert (Hi : Θ ⨟ empty ⊢ᵣᵃ
                 (pskl_to_bskl_inh (msubst_pskl (msubst_compose ζ1 κa) P0)) ⊳ Q).
  { eapply ad_precise_preserves_refine;
      [ exact Hpp | exact Href | exact HwfΘ
      | intros α Hα; clear - Hα; fsetdec | exact HwfQcod ]. }
  assert (Hms1 : msubst_pskl (msubst_compose ζ1 κa) P0 = msubst_pskl ζ1 P0).
  { eapply msubst_compose_id_pskl;
      [ exact Hwf0 | exact Hwf1 | exact Hida | exact Hinca | exact Hζ1
      | eapply a_wf_pskl_to_a_scope_pskl;
          [ exact HwfP0 | intros z b Hb; exact Hb
          | intros α Hα; clear - Hα; fsetdec ] ]. }
  rewrite Hms1 in Hi.
  (* ---- 3. the function's run (e1 at FN M, P1 → P0) ---- *)
  assert (HwfP1 : Θ1 ⨟ empty ⊢ₚₛᵃ P1)
    by (eapply a_pat_output_wf;
        [ exact Hrun2 | exact Hwf0 | exact Hskl
        | apply a_wf_pskl__hole | apply a_sk_mode_compat__tc | exact Hexp2 ]).
  assert (HwfP0mid : Θ1 ⨟ empty ⊢ₚₛᵃ P0).
  { pose proof (a_wf_pskl_msubst_inc Hinca Hwf0 HwfP0
                  ltac:(intros α Hα; clear - Hα; solve_notin_auto)) as Hw.
    rewrite (msubst_pskl_id P0 Hida) in Hw. exact Hw. }
  assert (Hskl1 : forall y Ps, binds y (abind_var_skl Ps) Θ1 ->
             Θ1 ⨟ empty ⊢ₚₛᵃ Ps).
  { intros y Ps Hb.
    assert (Hb0 : binds y (abind_var_skl Ps) Θ0)
      by (eapply a_pat_tm_ge; [ exact Hrun2 | exact I | exact Hb ]).
    pose proof (a_wf_pskl_msubst_inc Hinca Hwf0 (Hskl _ _ Hb0)
                  ltac:(intros α Hα; clear - Hα; solve_notin_auto)) as Hw.
    rewrite (msubst_pskl_id Ps Hida) in Hw. exact Hw. }
  assert (Hrig1mid : forall α, α `in` ftvar_in_exp e1 ->
             binds α abind_tvar Θ1)
    by (intros α Hα; eapply a_inc_binds_tvar;
        [ exact Hinca | apply Hrig1; exact Hα ]).
  destruct (IH1 (mode_fn M) Θ1 (pskl_arrow P1 P0) ζ1 Θ (bskl_arrow Qdom Q)
              Hwf1 HwfΘ
              ltac:(apply a_wf_pskl__arrow; [ exact HwfP1 | exact HwfP0mid ])
              ltac:(apply a_sk_mode_compat__fn; exact Hmod)
              Hζ1 Hrig1mid Hskl1 HsklT Hlc1 Hd1
              ltac:(cbn [msubst_pskl pskl_to_bskl_inh];
                    apply ad_refine_syn__arrow; [ exact Hh | exact Hi ]))
    as [P2 [Θ2 [Hrun1 Hopt1]]].
  (* the function's output is an ARROW (the run's image is FN-compatible) *)
  assert (Hexp1 : a_wf_exp Θ1 e1).
  { apply a_wf_exp_of_tvarish; [ exact Hlc1 | ].
    intros α Hα. left. apply Hrig1mid. exact Hα. }
  destruct (a_pat_sound Hrun1 Hwf1 Hskl1
              ltac:(apply a_wf_pskl__arrow; [ exact HwfP1 | exact HwfP0mid ])
              ltac:(apply a_sk_mode_compat__fn; exact Hmod)
              Hexp1)
    as [Hle1 [Hwf2 [Qt [HeQt [Hpat1 _]]]]].
  pose proof (ad_pat_mod_comp_sk Hpat1) as Hmc.
  inversion Hmc; subst.
  destruct Hle1 as [[κb [Hidb Hincb]] _].
  (* ---- 4. the run (the output IS the arrow's erasure, by conversion) ---- *)
  match goal with
  | Hm : mod_comp_sk (bskl_arrow ?QA ?QB) (mode_fn M) |- _ =>
      rename QA into Qa; rename QB into Qb
  end.
  exists (bskl_to_pskl Qb), Θ2.
  split.
  { eapply a_pat__app; [ exact Hrun2 | exact Hrun1 ]. }
  (* ---- 5. optimality: glue the two runs ---- *)
  intros κ1 Hid1 Hinc1.
  assert (Heqκa : κ1 = κa)
    by (eapply a_inc_id_msubst_unique;
        [ exact Hinc1 | exact Hinca | exact Hid1 | exact Hida ]).
  destruct (Hopt1 κb Hidb Hincb) as [ζ2 [Hζ2 [Heqv2 Hprec2]]].
  exists ζ2.
  split; [ exact Hζ2 | ].
  split.
  { assert (Hglue : a_inc_equiv Θ0 κ (msubst_compose ζ2 κa) Θ).
    { eapply a_inc_equiv_glue with
        (Θmid := Θ1) (Θfin := Θ2) (κ1b := κb) (ζ1 := ζ1);
        [ exact Hwf0 | exact Hwf1 | exact Hwf2 | exact HwfΘ
        | exact Hida | exact Hidb
        | intros α Hα;
          pose proof (a_inc_dom_flex Hinca Hα) as Hfα;
          eapply a_inc_flex_dom;
            [ exact Hincb | exact Hwf1
            | eapply a_inc_id_flex_preserve;
                [ exact Hinca | exact Hida | exact Hwf0 | exact Hfα ] ]
        | exact Hinca | exact Hincb | exact Hζ1 | exact Hζ2
        | exact Heqv1 | exact Heqv2 ]. }
    rewrite Heqκa. exact Hglue. }
  { (* the codomain of the arrow precision *)
    unfold ad_precise in Hprec2 |- *.
    cbn [msubst_pskl bskl_to_pskl pskl_to_bskl_inh] in Hprec2.
    destruct (ad_refine_syn_arrow_inv Hprec2) as [_ Hcod].
    exact Hcod. }
Qed.

(* ===================================================================== *)
(*  THEOREM 3 — thm:complete-skeleton-inference.  The induction is pure   *)
(*  glue over the nine step lemmas: strong induction on [size_exp]        *)
(*  (every recursive premise is at a strict subterm — the mech FUSED      *)
(*  [P-Sub] into the base rows, so no lexicographic measure is needed).   *)
(* ===================================================================== *)

Lemma a_pat_complete_gen : forall n e M Θ0 P0 κ Θ Q,
  size_exp e < n ->
  a_wf_aenv Θ0 -> a_wf_aenv Θ ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  a_sk_mode_compat M P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp e -> binds α abind_tvar Θ0) ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ0 -> Θ0 ⨟ empty ⊢ₚₛᵃ Ps) ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ -> Θ ⨟ empty ⊢ₚₛᵃ Ps) ->
  lc_exp e ->
  Θ ⊢ᵃ[ M ] e ⇨ Q ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q ->
  pat_complete_concl M Θ0 P0 e κ Θ Q.
Proof.
  induction n as [ | n IHn ];
    intros e M Θ0 P0 κ Θ Q Hsz Hwf0 HwfΘ HwfP0 Hmod Hinc Hrig Hskl HsklT
           Hlc Hd Href;
    [ exfalso; clear - Hsz; lia | ].
  destruct e as [ | m | x | e0 | A e0 | e1 e2 | e0 A | e0 ]; simpl in Hsz.
  - (* unit *) apply a_pat_complete_unit; assumption.
  - (* a bound variable has no rule *) inversion Hd.
  - (* var *) apply a_pat_complete_var; assumption.
  - (* abs : the mode picks the row *)
    destruct M as [ | | M' ].
    + apply a_pat_complete_abs; try assumption;
        [ intros Hc; discriminate Hc | ].
      intros x M2 Θ02 P02 κ2 Θ2 Q2; intros.
      apply IHn; try assumption.
      rewrite size_exp_open_exp_wrt_exp_var. clear - Hsz; lia.
    + inversion Hmod; subst.
      apply a_pat_complete_abs_check; try assumption.
      intros x M2 Θ02 P02 κ2 Θ2 Q2; intros.
      apply IHn; try assumption.
      rewrite size_exp_open_exp_wrt_exp_var. clear - Hsz; lia.
    + apply a_pat_complete_abs; try assumption;
        [ intros Hc; discriminate Hc | ].
      intros x M2 Θ02 P02 κ2 Θ2 Q2; intros.
      apply IHn; try assumption.
      rewrite size_exp_open_exp_wrt_exp_var. clear - Hsz; lia.
  - (* abs_anno *)
    destruct M as [ | | M' ].
    + apply a_pat_complete_abs_anno; try assumption;
        [ intros Hc; discriminate Hc | ].
      intros x M2 Θ02 P02 κ2 Θ2 Q2; intros.
      apply IHn; try assumption.
      rewrite size_exp_open_exp_wrt_exp_var. clear - Hsz; lia.
    + inversion Hmod; subst.
      apply a_pat_complete_abs_anno_check; try assumption.
      intros x M2 Θ02 P02 κ2 Θ2 Q2; intros.
      apply IHn; try assumption.
      rewrite size_exp_open_exp_wrt_exp_var. clear - Hsz; lia.
    + apply a_pat_complete_abs_anno; try assumption;
        [ intros Hc; discriminate Hc | ].
      intros x M2 Θ02 P02 κ2 Θ2 Q2; intros.
      apply IHn; try assumption.
      rewrite size_exp_open_exp_wrt_exp_var. clear - Hsz; lia.
  - (* app *)
    pose proof (size_exp_min e1) as Hm1.
    pose proof (size_exp_min e2) as Hm2.
    apply a_pat_complete_app; try assumption.
    + intros M2 Θ02 P02 κ2 Θ2 Q2; intros.
      apply IHn; try assumption. clear - Hsz Hm1; lia.
    + intros M2 Θ02 P02 κ2 Θ2 Q2; intros.
      apply IHn; try assumption. clear - Hsz Hm2; lia.
  - (* anno *)
    apply a_pat_complete_anno; try assumption.
    intros α Hα. apply Hrig. simpl. clear - Hα; fsetdec.
  - (* freeze : the rule pins the mode and the input ghost *)
    destruct M as [ | | M' ]; [ inversion Hd | | inversion Hd ].
    inversion Hmod; subst.
    apply a_pat_complete_freeze; [ | exact Hd | exact Href ].
    intros Q' Hd' Href'.
    apply IHn; try assumption;
      try solve [ clear - Hsz; lia
                | apply a_wf_pskl__hole
                | apply a_sk_mode_compat__ti
                | inversion Hlc; assumption ].
Qed.

(** ⭐ THEOREM 3 (thm:complete-skeleton-inference, proofs.tex:1711).
    Whenever the DECLARATIVE system infers a skeleton [Q] at any solution
    [κ] of the question [(Θ0; M; P0)], the ALGORITHM's run succeeds, and
    for every identity increase out of the question context the run's
    answer factors through the solution: a composing witness [ζ] whose
    composite is equivalent to [κ] and whose image of the run's output is
    MORE PRECISE than the declarative target.

    Hypotheses beyond the paper's statement (all WF-SIDE-CONDITIONS.md
    externals): well-formedness of the two contexts and the input
    skeleton, the payload-wf DISCIPLINE of both contexts' skeleton term
    entries, mode compatibility, [lc], and the term side condition — an
    annotation is SOURCE syntax, so its type variables are RIGID. *)
Theorem a_pat_complete : forall e M Θ0 P0 κ Θ Q,
  a_wf_aenv Θ0 -> a_wf_aenv Θ ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  a_sk_mode_compat M P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp e -> binds α abind_tvar Θ0) ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ0 -> Θ0 ⨟ empty ⊢ₚₛᵃ Ps) ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ -> Θ ⨟ empty ⊢ₚₛᵃ Ps) ->
  lc_exp e ->
  Θ ⊢ᵃ[ M ] e ⇨ Q ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q ->
  exists P1 Θ1,
    a_pat M Θ0 P0 e P1 Θ1 /\
    (forall κ1, is_id_msubst κ1 -> κ1 ∷ Θ0 ⊑ Θ1 ->
       exists ζ,
         ζ ∷ Θ1 ⊑ Θ /\
         a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ /\
         Θ ⨟ empty ⊢ₚᵣᵃ (msubst_pskl ζ P1) ⊑ (bskl_to_pskl Q)).
Proof.
  intros.
  eapply a_pat_complete_gen with (n := S (size_exp e)); try eassumption.
  clear; lia.
Qed.
