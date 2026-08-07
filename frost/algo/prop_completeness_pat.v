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
