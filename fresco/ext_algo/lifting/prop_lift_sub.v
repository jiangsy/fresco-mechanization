(** Subtyping and flexible-variable subtyping: lifting from [a_*] to supply-threaded [e_*] derivations. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.ltac_utils.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.prop_tag.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.prop_ln.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo.subtyping.prop_looksub.
Require Import src.fresco.algo.subtyping.prop_solve_sub.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.basic.def_supply.
Require Import src.fresco.ext_algo.basic.def_guess.
Require Import src.fresco.ext_algo.basic.prop_guess.
Require Import src.fresco.ext_algo.basic.prop_termination.
Require Import src.fresco.ext_algo.subtyping.def_look.
Require Import src.fresco.ext_algo.subtyping.prop_look.
Require Import src.fresco.ext_algo.subtyping.def_solve.
Require Import src.fresco.ext_algo.subtyping.def_extract.
Require Import src.fresco.ext_algo.subtyping.prop_solve.
Require Import src.fresco.ext_algo.subtyping.prop_solve_det.
Require Import src.fresco.ext_algo.subtyping.prop_solve_rel.
Require Import src.fresco.ext_algo.lifting.prop_lift_context.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo.basic.prop_inc_strengthen.
Require Import src.fresco.algo.consistency.prop_consis_rename.
Require Import src.fresco.algo.consistency.prop_soundness_consis.
Require Import src.fresco.ext_algo.consistency.def_consis.
Require Import src.fresco.ext_algo.consistency.prop_consis.
Require Import src.fresco.ext_algo.subtyping.def_sub.
Require Import src.fresco.ext_algo.subtyping.prop_sub.
Require Import src.fresco.ext_algo.subtyping.prop_extract.
Require Import src.fresco.algo_decl.prop_stability.
Require Import src.fresco.algo.basic.prop_wf_preservation.
Require Import src.fresco.algo.subtyping.prop_soundness_subtag.
Require Import src.fresco.ext_algo.typing.def_pat.
Require Import src.fresco.ext_algo.typing.prop_pat.
Require Import src.fresco.algo.basic.prop_mod_compat.
Require Import src.fresco.algo_decl.prop_precision.
Require Import src.fresco.algo.typing.prop_soundness_pat.
Require Import src.fresco.algo.typing.prop_completeness_pat.
Require Import src.fresco.algo.typing.prop_soundness_typing.
Require Import src.fresco.algo_decl.prop_ctx_mono.
Require Import src.fresco.ext_algo.typing.def_typing.
Require Import src.fresco.ext_algo.typing.prop_typing.

Set Implicit Arguments.

Open Scope fresco_a_scope.
Open Scope fresco_e_scope.

Require Export src.fresco.ext_algo.lifting.prop_lift_solve.
Require Export src.fresco.ext_algo.lifting.prop_lift_consis.


(* ===================================================================== *)
(*  §10  ⭐⭐⭐ THE a_sub RUNG — [a_sub] / [a_sub_flex] lift to [e_sub] /    *)
(*  [e_sub_flex], all 16 rows (2026-08-21, §8c.36–§8c.42)                  *)
(*                                                                        *)
(*  Same discipline as §9's consis rung: side 1 carries what               *)
(*  [subtag_sound_concl] wants, side 2 carries ONLY [uniq Θ0'] and the     *)
(*  supply bound.  ⭐ The strongest evidence the two rungs' motives line up *)
(*  is [lift_consis_nil] below — it has EXACTLY [lift_sub_concl]'s          *)
(*  hypothesis list, and its proof discharges every non-Δ premise with one  *)
(*  [try assumption].                                                      *)
(* ===================================================================== *)


(** ⭐ At the CHECK sort and mode the yield IS the check-against — every
    [a_sub_mode_ty] / [mode_tc] rule either returns [P0] outright ([Check],
    [ForallR]) or passes its premise's yield through ([ForallL]); the rest
    are at another sort or another mode.  ⚙ [a_sub__forall_r]'s lift needs
    it because [e_sub__forall_r] PINS the premise's yield, while the motive
    only relates it. *)
Lemma e_sub_tc_yield :
  (forall S0 NM M P0 Θ0 P Q S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
     NM = a_sub_mode_ty -> M = mode_tc -> Q = P0) /\
  (forall S0 NM M P0 Θ0 Ξ α Q S1 Θ1,
     e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1 -> True).
Proof.
  apply (e_sub_sub_flex_mutind
           (fun S0 NM M P0 Θ0 P Q S1 Θ1 _ =>
              NM = a_sub_mode_ty -> M = mode_tc -> Q = P0)
           (fun S0 NM M P0 Θ0 Ξ α Q S1 Θ1 _ => True));
    try solve [ intros; exact I ];
    intros; try discriminate; try reflexivity.
  - (* ForallL passes the premise's yield through *)
    match goal with IH : _ -> _ -> _ = _ |- _ => apply IH; assumption end.
Qed.

(* ===================================================================== *)
(*  THE MOTIVES                                                           *)
(*                                                                        *)
(*  Same discipline as the consis rung (§8c.32): side 1 carries the        *)
(*  package [subtag_sound_concl] wants, side 2 carries ONLY [uniq Θ0'] +   *)
(*  [ftvar_in_aenv Θ0' ⊆ S0].  ⭐ Here that is even cheaper than at consis: *)
(*  [e_sub_sub_flex_sound] re-establishes BOTH at the output in one go.    *)
(* ===================================================================== *)

Definition lift_sub_post (Θ0 : aenv) (Q : pskl) (Θ1 : aenv)
    (S0 : atoms) (NM : a_sub_mode) (M : mode) (Θ0' : aenv)
    (P0' P' : pskl) (ρ : list (atom * atom)) (V : atoms) : Prop :=
  exists S1 ρe Θ1' Q',
    {{ S0 ↝ S1 ⊨ Θ0' ⊢[ NM | M | P0' ] P' ⩽ Q' ⊣ Θ1' }}e
    /\ rel_aenv (ρe ++ ρ) V Θ1 Θ1'
    /\ flex_agree_rel (ρe ++ ρ) V Θ1 Θ1'
    /\ rel_pskl (ρe ++ ρ) V Q Q'
    /\ rel_ext ρe (ftvar_in_aenv Θ0) S0
    /\ (forall a b, In (a, b) ρe -> a `in` dom Θ1 /\ b `in` dom Θ1').

Definition lift_sub_concl (NM : a_sub_mode) (M : mode) (P0 : pskl)
    (Θ0 : aenv) (P Q : pskl) (Θ1 : aenv) : Prop :=
  forall S0 Θ0' P0' P' ρ V,
    rel_aenv ρ V Θ0 Θ0' ->
    rel_pskl ρ V P0 P0' ->
    rel_pskl ρ V P P' ->
    flex_agree_rel ρ V Θ0 Θ0' ->
    rel_inj ρ V ->
    rel_fun ρ V (dom Θ0) ->
    {{ ⊢ Θ0 }}a ->
    uniq Θ0' ->
    ftvar_in_aenv Θ0' [<=] S0 ->
    V [<=] ftvar_in_aenv Θ0 ->
    (forall a, a `in` dom Θ1 -> a `notin` dom Θ0 -> a `notin` cols_l ρ) ->
    dom Θ0' [<=] S0 ->
    V ∪ cols_r ρ [<=] S0 ->
    ftvar_in_pskl P0' ∪ ftvar_in_pskl P' [<=] S0 ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
    lift_sub_post Θ0 Q Θ1 S0 NM M Θ0' P0' P' ρ V.

Definition lift_sub_flex_post (Θ0 Ξ : aenv) (Θ1 : aenv) (Q : pskl)
    (S0 : atoms) (NM : a_sub_mode) (M : mode) (Θ0' Ξ' : aenv) (α' : atom)
    (P0' : pskl) (ρ : list (atom * atom)) (V : atoms) : Prop :=
  exists S1 ρe Θ1' Q',
    e_sub_flex S0 NM M P0' Θ0' Ξ' α' Q' S1 Θ1'
    /\ rel_aenv (ρe ++ ρ) V Θ1 Θ1'
    /\ flex_agree_rel (ρe ++ ρ) V Θ1 Θ1'
    /\ rel_pskl (ρe ++ ρ) V Q Q'
    /\ rel_ext ρe (ftvar_in_aenv (Ξ ++ Θ0)) S0
    /\ (forall a b, In (a, b) ρe -> a `in` dom Θ1 /\ b `in` dom Θ1').

Definition lift_sub_flex_concl (NM : a_sub_mode) (M : mode) (P0 : pskl)
    (Θ0 Ξ : aenv) (α : atom) (Q : pskl) (Θ1 : aenv) : Prop :=
  forall S0 Θ0' Ξ' α' P0' ρ V,
    rel_aenv ρ V Θ0 Θ0' ->
    rel_aenv ρ V Ξ Ξ' ->
    rel_atom ρ V α α' ->
    rel_pskl ρ V P0 P0' ->
    flex_agree_rel ρ V (Ξ ++ Θ0) (Ξ' ++ Θ0') ->
    rel_inj ρ V ->
    rel_fun ρ V (dom (Ξ ++ Θ0)) ->
    {{ ⊢ (Ξ ++ Θ0) }}a ->
    a_decls Ξ ->
    a_decls Ξ' ->
    uniq (Ξ' ++ Θ0') ->
    ftvar_in_aenv (Ξ' ++ Θ0') [<=] S0 ->
    V [<=] ftvar_in_aenv (Ξ ++ Θ0) ->
    (forall a, a `in` dom Θ1 -> a `notin` dom (Ξ ++ Θ0) ->
       a `notin` cols_l ρ) ->
    dom (Ξ' ++ Θ0') [<=] S0 ->
    V ∪ cols_r ρ [<=] S0 ->
    ftvar_in_pskl P0' [<=] S0 ->
    {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a ->
    a_binds_tvar α (Ξ ++ Θ0) ->
    lift_sub_flex_post Θ0 Ξ Θ1 Q S0 NM M Θ0' Ξ' α' P0' ρ V.

(* ===================================================================== *)
(*  ⭐ THE CONSIS RUNG'S LIFT, AT THE Δ = ∅ CALLS [a_sub] MAKES            *)
(*                                                                        *)
(*  [a_sub__check] (through [a_consis_chk]) and [a_sub__arrow] both run    *)
(*  consistency with both Δ-trackers empty, where EVERY Δ-side premise of  *)
(*  [lift_consis_concl] is vacuous.  What is left is exactly               *)
(*  [lift_sub_concl]'s own hypothesis list, so the two rows can hand their *)
(*  package straight through.                                             *)
(* ===================================================================== *)

Lemma lift_consis_nil : forall Θ0 P0 P Q Θ1,
  {{ Θ0 ⊢[ P0 ] P ∼ Q ⊣ Θ1 }}a ->
  forall S0 Θ0' P0' P' ρ V,
    rel_aenv ρ V Θ0 Θ0' ->
    rel_pskl ρ V P0 P0' ->
    rel_pskl ρ V P P' ->
    flex_agree_rel ρ V Θ0 Θ0' ->
    rel_inj ρ V ->
    rel_fun ρ V (dom Θ0) ->
    {{ ⊢ Θ0 }}a ->
    uniq Θ0' ->
    ftvar_in_aenv Θ0' [<=] S0 ->
    V [<=] ftvar_in_aenv Θ0 ->
    (forall a, a `in` dom Θ1 -> a `notin` dom Θ0 -> a `notin` cols_l ρ) ->
    dom Θ0' [<=] S0 ->
    V ∪ cols_r ρ [<=] S0 ->
    ftvar_in_pskl P0' ∪ ftvar_in_pskl P' [<=] S0 ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
    lift_consis_post Θ0 Q Θ1 S0 Θ0' empty empty P0' P' ρ V.
Proof.
  intros Θ0 P0 P Q Θ1 Hc S0 Θ0' P0' P' ρ V HrΘ HrP0 HrP Hagr Hinj Hfun
    Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP Hwfp0 Hwfp.
  apply ((proj2 (proj2 a_assign_unify_consis_rel_e)) _ _ _ _ _ _ _ Hc);
    try assumption.
  - (* rel_atoms at ∅ *)
    intros a b Hat. split; intros Hin; clear - Hin; fsetdec.
  - intros a b Hat. split; intros Hin; clear - Hin; fsetdec.
  - (* the Δ coverage *) clear; fsetdec.
  - (* every Δ-name is rigid *) apply rig_empty.
  - (* no_flex_dep *) apply no_flex_dep_empty.
  - (* flex_above_free *) apply faf_empty.
  - (* Δ ⊆ ftvar_in_aenv Θ0 *) clear; fsetdec.
Qed.

(* ===================================================================== *)
(*  ⭐⭐ THE WALK'S SHARED PEEL                                             *)
(*                                                                        *)
(*  The four skip rows of [a_sub_flex] differ ONLY in the entry they step  *)
(*  over, so the V-SHRINK, the IH and the re-attachment live here once and *)
(*  each row is left with its own [e_sub_flex] constructor.  ⭐ It is the   *)
(*  consis rung's [Assign-Skip] (prop_lift.v §9) with two deltas: the walk *)
(*  also carries a YIELD, and [rel_pskl] is MONOTONE in [V] so widening    *)
(*  the IH's [VS] back is free; and the e-side skip rules carry NO         *)
(*  Barendregt premise (def_sub.v:152-175), the supply having accounted    *)
(*  for it.                                                                *)
(* ===================================================================== *)

Lemma lift_sub_flex_peel :
  forall NM M P0 Θ0 Θ1 Ξ α Q (β : atom) (bd : abind),
  lift_sub_flex_concl NM M P0 Θ0 Ξ α Q Θ1 ->
  α <> β ->
  β `notin` ftvar_in_pskl P0 ->
  β `notin` dom Θ1 ->
  forall S0 Θ0' Ξ' α' P0' ρ V,
    rel_aenv ρ V ((β ~ bd) ++ Θ0) Θ0' ->
    rel_aenv ρ V Ξ Ξ' ->
    rel_atom ρ V α α' ->
    rel_pskl ρ V P0 P0' ->
    flex_agree_rel ρ V (Ξ ++ (β ~ bd) ++ Θ0) (Ξ' ++ Θ0') ->
    rel_inj ρ V ->
    rel_fun ρ V (dom (Ξ ++ (β ~ bd) ++ Θ0)) ->
    {{ ⊢ (Ξ ++ (β ~ bd) ++ Θ0) }}a ->
    a_decls Ξ ->
    a_decls Ξ' ->
    uniq (Ξ' ++ Θ0') ->
    ftvar_in_aenv (Ξ' ++ Θ0') [<=] S0 ->
    V [<=] ftvar_in_aenv (Ξ ++ (β ~ bd) ++ Θ0) ->
    (forall a, a `in` dom ((β ~ bd) ++ Θ1) ->
       a `notin` dom (Ξ ++ (β ~ bd) ++ Θ0) -> a `notin` cols_l ρ) ->
    dom (Ξ' ++ Θ0') [<=] S0 ->
    V ∪ cols_r ρ [<=] S0 ->
    ftvar_in_pskl P0' [<=] S0 ->
    {{ (Ξ ++ (β ~ bd) ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a ->
    a_binds_tvar α (Ξ ++ (β ~ bd) ++ Θ0) ->
  exists (b : atom) bd2 Θ0'' S1 ρe Θ1' Q',
    Θ0' = (b ~ bd2) ++ Θ0''
    /\ rel_abind ρ V bd bd2
    /\ α' <> b
    /\ b `notin` ftvar_in_pskl P0'
    /\ e_sub_flex S0 NM M P0' Θ0'' Ξ' α' Q' S1 Θ1'
    /\ rel_aenv (ρe ++ ρ) V ((β ~ bd) ++ Θ1) ((b ~ bd2) ++ Θ1')
    /\ flex_agree_rel (ρe ++ ρ) V ((β ~ bd) ++ Θ1) ((b ~ bd2) ++ Θ1')
    /\ rel_pskl (ρe ++ ρ) V Q Q'
    /\ rel_ext ρe (ftvar_in_aenv (Ξ ++ (β ~ bd) ++ Θ0)) S0
    /\ (forall a b0, In (a, b0) ρe ->
          a `in` dom ((β ~ bd) ++ Θ1) /\ b0 `in` dom ((b ~ bd2) ++ Θ1')).
Proof.
  intros NM M P0 Θ0 Θ1 Ξ α Q β bd IH Hne Hβp Hβd.
  intros S0 Θ0' Ξ' α' P0' ρ V HrΘ HrΞ Hrα HrP0 Hagr Hinj Hfun Hwf Hdec
    Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP Hwfp0 Hbα.
  destruct (rel_aenv_cons_inv_l HrΘ)
    as (b & bd2 & Θ0'' & E0' & Hab & Hbd & Hrest).
  subst Θ0'.
  assert (Huq1 : uniq (Ξ ++ (β ~ bd) ++ Θ0))
    by (apply a_wf_aenv_uniq; exact Hwf).
  assert (Huq2 : uniq (Ξ' ++ (b ~ bd2) ++ Θ0'')) by (exact Huq2p).
  assert (HwfC : {{ ⊢ (Ξ ++ Θ0) }}a)
    by (eapply a_wf_aenv_strip_mid; [ exact Hdec | exact Hwf ]).
  assert (Huq2C : uniq (Ξ' ++ Θ0'')) by (clear - Huq2p; solve_uniq).
  assert (Hftv2C : ftvar_in_aenv (Ξ' ++ Θ0'') [<=] S0).
  { repeat rewrite ftvar_in_aenv_app in Hftv2 |- *. simpl in Hftv2.
    clear - Hftv2. fsetdec. }
  assert (Hβnd : β `notin` dom (Ξ ++ Θ0)).
  { clear - Huq1. repeat rewrite dom_app in *. simpl in *.
    destruct_uniq. fsetdec. }
  assert (Hbnd : b `notin` dom (Ξ' ++ Θ0'')).
  { clear - Huq2. repeat rewrite dom_app in *. simpl in *.
    destruct_uniq. fsetdec. }
  assert (Hsc : ftvar_in_aenv (Ξ ++ (β ~ bd) ++ Θ0)
                [<=] dom (Ξ ++ (β ~ bd) ++ Θ0))
    by (apply a_wf_aenv_ftv_dom; exact Hwf).
  assert (HVdom : V [<=] dom (Ξ ++ (β ~ bd) ++ Θ0))
    by (clear - Hscp Hsc; fsetdec).
  assert (HscC : ftvar_in_aenv (Ξ ++ Θ0) [<=] dom (Ξ ++ Θ0))
    by (apply a_wf_aenv_ftv_dom; exact HwfC).
  assert (Hβd0 : β `in` dom (Ξ ++ (β ~ bd) ++ Θ0))
    by (repeat rewrite dom_app; simpl; clear; fsetdec).
  assert (Hβfun : forall y, rel_atom ρ V β y -> y = b)
    by (intros y Hy; exact (Hfun β y b Hβd0 Hy Hab)).
  assert (Hne2 : α' <> b).
  { intros Ex. apply Hne. rewrite Ex in Hrα. exact (Hinj α β b Hrα Hab). }
  assert (Hbdftv : ftvar_in_abind bd [<=] dom Θ0)
    by (eapply a_wf_aenv_cons_payload_ftv;
        eapply a_wf_aenv_strip_prefix; exact Hwf).
  assert (Hds0 : dom Θ0 [<=] ftvar_in_aenv Θ0)
    by (apply dom_subset_ftvar_in_aenv).
  assert (HbP : b `notin` ftvar_in_pskl P0')
    by (eapply rel_pskl_notin_r_inj;
        [ exact HrP0 | exact Hinj | exact Hab | exact Hβp ]).
  remember (V ∩ ftvar_in_aenv (Ξ ++ Θ0)) as VS eqn:EVS.
  assert (HVS : VS [<=] V) by (subst VS; clear; fsetdec).
  assert (HVSsplit : forall x, x `in` V -> x <> β -> x `in` VS).
  { intros x Hx Hne0. subst VS.
    pose proof (dom_subset_ftvar_in_aenv (Ξ ++ Θ0)) as Hds.
    assert (Hxd : x `in` dom (Ξ ++ (β ~ bd) ++ Θ0))
      by (clear - Hx HVdom; fsetdec).
    repeat rewrite dom_app in Hxd. simpl in Hxd.
    repeat rewrite dom_app in Hds.
    clear - Hx Hne0 Hxd Hds. fsetdec. }
  assert (HVSne : forall x, x `in` VS -> x <> β).
  { intros x Hx Ex. rewrite Ex in Hx.
    assert (Hin : β `in` ftvar_in_aenv (Ξ ++ Θ0))
      by (subst VS; clear - Hx; fsetdec).
    clear - Hin HscC Hβnd. fsetdec. }
  assert (HrΘS : rel_aenv ρ VS Θ0 Θ0'').
  { eapply rel_aenv_shrink_V; [ exact Hrest | ].
    intros x Hx Hf. subst VS.
    pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
    rewrite ftvar_in_aenv_app. clear - Hx Hf Hds. fsetdec. }
  assert (HrΞS : rel_aenv ρ VS Ξ Ξ').
  { eapply rel_aenv_shrink_V; [ exact HrΞ | ].
    intros x Hx Hf. subst VS.
    pose proof (dom_subset_ftvar_in_aenv Ξ) as Hds.
    rewrite ftvar_in_aenv_app. clear - Hx Hf Hds. fsetdec. }
  assert (HrαS : rel_atom ρ VS α α').
  { inversion Hrα; subst.
    - apply rel_atom__pair; assumption.
    - apply rel_atom__id. apply HVSsplit; [ assumption | exact Hne ]. }
  assert (HrP0S : rel_pskl ρ VS P0 P0').
  { eapply rel_pskl_shrink_V; [ exact HrP0 | ].
    intros x Hx Hf. apply HVSsplit; [ exact Hx | ].
    intros Ex. rewrite Ex in Hf. contradiction. }
  assert (HagrS : flex_agree_rel ρ VS (Ξ ++ Θ0) (Ξ' ++ Θ0''))
    by (eapply flex_agree_peel;
        [ exact Hagr | exact Hab | exact Hinj | exact Hβfun | exact Hβnd
        | exact Hbnd | exact HVS | exact HVSne ]).
  assert (HinjS : rel_inj ρ VS)
    by (eapply rel_inj_weaken_V; [ exact Hinj | exact HVS ]).
  assert (HfunS : rel_fun ρ VS (dom (Ξ ++ Θ0))).
  { eapply rel_fun_weaken;
      [ eapply rel_fun_weaken_V; [ exact Hfun | exact HVS ]
      | intros x y Hx; exact Hx
      | repeat rewrite dom_app; simpl; clear; fsetdec ]. }
  assert (HbαS : a_binds_tvar α (Ξ ++ Θ0)).
  { eapply a_binds_tvar_strip_mid; [ exact Hbα | | | ];
      solve [ intros E; inversion E; subst; apply Hne; reflexivity
            | intros τ0 E; inversion E; subst; apply Hne; reflexivity ]. }
  assert (HscpS : VS [<=] ftvar_in_aenv (Ξ ++ Θ0))
    by (subst VS; clear; fsetdec).
  assert (HblkS : forall a0, a0 `in` dom Θ1 -> a0 `notin` dom (Ξ ++ Θ0) ->
                  a0 `notin` cols_l ρ).
  { intros a0 Ha0 Hn0. apply Hblk.
    - simpl. clear - Ha0. fsetdec.
    - assert (Hne0 : a0 <> β)
        by (intros Ex; rewrite Ex in Ha0; contradiction).
      repeat rewrite dom_app in Hn0 |- *. simpl. clear - Hn0 Hne0. fsetdec. }
  assert (HdΘS : dom (Ξ' ++ Θ0'') [<=] S0)
    by (repeat rewrite dom_app in HdΘ |- *; simpl in HdΘ;
        clear - HdΘ; fsetdec).
  assert (HcovS : VS ∪ cols_r ρ [<=] S0) by (clear - Hcov HVS; fsetdec).
  assert (HwfpS : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a)
    by (eapply a_wf_pskl_strip_mid; [ exact Hwfp0 | exact Hβp ]).

  destruct (IH S0 Θ0'' Ξ' α' P0' ρ VS HrΘS HrΞS HrαS HrP0S HagrS HinjS HfunS
              HwfC Hdec Hdec2 Huq2C Hftv2C HscpS HblkS HdΘS HcovS HcovP
              HwfpS HbαS)
    as (S1 & ρe & Θ1' & Q' & D2 & HrΘ1 & Hagr1 & HrQ & Hext1 & Hdom1).
  exists b, bd2, Θ0'', S1, ρe, Θ1', Q'.
  split; [ reflexivity | ].
  split; [ exact Hbd | ].
  split; [ exact Hne2 | ].
  split; [ exact HbP | ].
  split; [ exact D2 | ].
  split.
  { apply rel_aenv__cons.
    - eapply rel_atom_incl; [ exact Hab | ].
      intros x y Hx. apply in_or_app. right. exact Hx.
    - eapply rel_abind_mono; [ exact Hbd | intros x y Hx; apply in_or_app;
        right; exact Hx | intros x Hx; exact Hx ].
    - eapply rel_aenv_mono;
        [ exact HrΘ1 | intros x y Hx; exact Hx | exact HVS ]. }
  assert (Hbnd1 : b `notin` dom Θ1').
  { pose proof ((proj2 e_sub_sub_flex_dom_upper) _ _ _ _ _ _ _ _ _ _ D2)
      as Hup.
    assert (HbS0 : b `in` S0)
      by (repeat rewrite dom_app in HdΘ; simpl in HdΘ; clear - HdΘ; fsetdec).
    rewrite dom_app in Hup. clear - Hup Hbnd HbS0.
    repeat rewrite dom_app in Hbnd. fsetdec. }
  assert (Hinj' : rel_inj (ρe ++ ρ) V)
    by (eapply rel_inj_app; [ exact Hinj | exact Hext1 | exact Hcov ]).
  assert (Hab' : rel_atom (ρe ++ ρ) V β b)
    by (eapply rel_atom_incl;
        [ exact Hab | intros x y Hx; apply in_or_app; right; exact Hx ]).
  assert (Hβfun' : forall y, rel_atom (ρe ++ ρ) V β y -> y = b).
  { intros y Hy. destruct (rel_atom_app_inv ρe ρ Hy) as [Hin0 | Hat0].
    - exfalso. destruct (Hdom1 _ _ Hin0) as [Hd1 _]. contradiction.
    - exact (Hβfun y Hat0). }
  split.
  { eapply flex_agree_reattach;
      [ exact Hagr1 | exact Hab' | exact Hinj' | exact Hβfun'
      | exact HVSsplit
      | intros HβV; symmetry; apply Hβfun; apply rel_atom__id; exact HβV
      | (* ⭐ the head agrees because [rel_abind] forces the two entries to
           have the same KIND: flexible on both sides, or rigid on both *)
        inversion Hbd; subst;
        [ (* tvar *) split; intros Hf; exfalso;
            [ apply Hβd | apply Hbnd1 ]; apply a_flex_tvar_in_dom;
            (eapply a_flex_tvar_head_tail;
               [ exact Hf | discriminate | intros ?; discriminate ])
        | (* flex *) split; intros _; left; unfold binds; simpl; left; reflexivity
        | (* flex_def *) split; intros _; right; eexists; unfold binds; simpl;
            left; reflexivity
        | (* var_typ *) split; intros Hf; exfalso;
            [ apply Hβd | apply Hbnd1 ]; apply a_flex_tvar_in_dom;
            (eapply a_flex_tvar_head_tail;
               [ exact Hf | discriminate | intros ?; discriminate ])
        | (* var_skl *) split; intros Hf; exfalso;
            [ apply Hβd | apply Hbnd1 ]; apply a_flex_tvar_in_dom;
            (eapply a_flex_tvar_head_tail;
               [ exact Hf | discriminate | intros ?; discriminate ]) ] ]. }
  assert (Hftsub : ftvar_in_aenv (Ξ ++ (β ~ bd) ++ Θ0)
                   [<=] add β (ftvar_in_abind bd ∪ ftvar_in_aenv (Ξ ++ Θ0))).
  { repeat rewrite ftvar_in_aenv_app. simpl. clear; fsetdec. }
  split.
  { eapply rel_pskl_mono;
      [ exact HrQ | intros x y Hx; exact Hx | exact HVS ]. }
  split.
  { destruct Hext1 as [Hfr1 [Hri1 Hlf1]]. unfold rel_ext.
    split; [ | split; [ exact Hri1 | exact Hlf1 ] ].
    intros a0 b0 Hin. destruct (Hfr1 _ _ Hin) as [Ha0 Hb0].
    split; [ | exact Hb0 ].
    destruct (Hdom1 _ _ Hin) as [Hd1 _].
    assert (Hne0 : a0 <> β)
      by (intros Ex; rewrite Ex in Hd1; contradiction).
    repeat rewrite ftvar_in_aenv_app in Ha0 |- *. simpl.
    clear - Ha0 Hne0 Hbdftv Hds0. fsetdec. }
  intros a0 b0 Hin. destruct (Hdom1 _ _ Hin) as [Hd1 Hd2].
  split; [ clear - Hd1; simpl_env; fsetdec | clear - Hd2; simpl_env; fsetdec ].
Qed.

Theorem a_sub_sub_flex_rel_e :
  (forall NM M P0 Θ0 P Q Θ1, a_sub NM M P0 Θ0 P Q Θ1 ->
     lift_sub_concl NM M P0 Θ0 P Q Θ1) /\
  (forall NM M P0 Θ0 Ξ α Q Θ1, a_sub_flex NM M P0 Θ0 Ξ α Q Θ1 ->
     lift_sub_flex_concl NM M P0 Θ0 Ξ α Q Θ1).
Proof.
  apply (a_sub_sub_flex_tm_mutind
           (fun NM M P0 Θ0 P Q Θ1 _ => lift_sub_concl NM M P0 Θ0 P Q Θ1)
           (fun NM M P0 Θ0 Ξ α Q Θ1 _ =>
              lift_sub_flex_concl NM M P0 Θ0 Ξ α Q Θ1)).
  - (* S-Infer : output = subject, context unchanged *)
    intros NM P Θ0.
    intros S0 Θ0' P0' P' ρ V HrΘ HrP0 HrP Hagr Hinj Hfun Hwf Huq2p Hftv2
      Hscp Hblk HdΘ Hcov HcovP Hwfp0 Hwfp.
    inversion HrP0 as [ | n0 | u0 v0 Hu0 | A1 A2 A3 A4 Hu1 Hu2 | B1 B2 Hu3
                      | | C1 C2 Hu4 ]; subst.
    exists S0, (@nil (atom * atom)%type), Θ0', P'.
    split; [ apply e_sub__infer | ]. simpl.
    split; [ exact HrΘ | ].
    split; [ exact Hagr | ].
    split; [ exact HrP | ].
    split.
    { unfold rel_ext. repeat split; intros; simpl in *; contradiction. }
    intros a b Hin. inversion Hin.
  - (* S-Check : the consistency call, at Δ = ∅ *)
    intros Θ0 Θ1 A B Hgfa Hgfb Hga Hgb Hc.
    intros S0 Θ0' P0' P' ρ V HrΘ HrP0 HrP Hagr Hinj Hfun Hwf Huq2p Hftv2
      Hscp Hblk HdΘ Hcov HcovP Hwfp0 Hwfp.
    destruct Hc as [Qc Hc].
    destruct (lift_consis_nil Hc HrΘ HrP0 HrP Hagr Hinj Hfun Hwf Huq2p Hftv2
                Hscp Hblk HdΘ Hcov HcovP Hwfp0 Hwfp)
      as (S1 & ρe & Θ1' & Qc' & De & HrΘ1 & Hagr1 & HrQ & Hext & Hdom1).
    exists S1, ρe, Θ1', P0'.
    split.
    { apply e_sub__check;
        [ eapply rel_pskl_ghost_free; [ exact HrP | exact Hgfa ]
        | eapply rel_pskl_ghost_free; [ exact HrP0 | exact Hgfb ]
        | eapply rel_pskl_guarded; [ exact HrP | exact Hga ]
        | eapply rel_pskl_guarded; [ exact HrP0 | exact Hgb ]
        | exists Qc'; exact De ]. }
    split; [ exact HrΘ1 | ].
    split; [ exact Hagr1 | ].
    split.
    { eapply rel_pskl_mono;
        [ exact HrP0 | intros x y Hx; apply in_or_app; right; exact Hx
        | intros x Hx; exact Hx ]. }
    split; [ exact Hext | ]. exact Hdom1.
  - (* ⭐⭐ S-ForallR — PROBE: everything but [Hblk'] *)
    intros α Θ0 Θ1 Ξ A B Hgf Hsuf Huq Hfr Hprem IH.
    intros S0 Θ0' P0' P' ρ V HrΘ HrP0 HrP Hagr Hinj Hfun Hwf Huq2p Hftv2
      Hscp Hblk HdΘ Hcov HcovP Hwfp0 Hwfp.
    inversion HrP0 as [ | n0 | u0 v0 Hu0 | A1 A2 A3 A4 Hu1 Hu2
                      | B1 B2 HrB | | C1 C2 Hu3 ]; subst.
    destruct (atom_fresh S0) as [α2 Hα2].
    rewrite dom_app in Hfr.
    assert (Hαd : α `notin` dom Θ0) by (clear - Hfr; fsetdec).
    assert (HαΘ1 : α `notin` dom Θ1) by (clear - Hfr; fsetdec).
    assert (HfrA : α `notin` ftvar_in_pskl A) by (clear - Hfr; fsetdec).
    assert (HfrB : α `notin` ftvar_in_pskl B) by (clear - Hfr; fsetdec).
    assert (Hsc0 : ftvar_in_aenv Θ0 [<=] dom Θ0)
      by (apply a_wf_aenv_ftv_dom; exact Hwf).
    assert (HfrΘ : α `notin` ftvar_in_aenv Θ0) by (clear - Hαd Hsc0; fsetdec).
    assert (HαV : α `notin` V) by (intros Hin; apply HfrΘ; apply Hscp; exact Hin).
    assert (Hα2d : α2 `notin` dom Θ0') by (clear - Hα2 HdΘ; fsetdec).
    assert (Hα2V : α2 `notin` V) by (clear - Hα2 Hcov; fsetdec).
    assert (Hα2f : α2 `notin` ftvar_in_aenv Θ0') by (clear - Hα2 Hftv2; fsetdec).
    (* ⭐ FIRST restrict at the JUNK SUFFIX's domain: the rule freshens Ξ
       only against the CONTEXT, so its names can collide with ρ's left
       column — and then [Hblk'] below is underivable. *)
    assert (HΞΘ0 : dom Ξ ∩ ftvar_in_aenv Θ0 [=] empty).
    { assert (Hdisj : disjoint Ξ Θ0) by (clear - Huq; solve_uniq).
      unfold disjoint in Hdisj. clear - Hdisj Hsc0. fsetdec. }
    assert (HΞB : dom Ξ ∩ ftvar_in_pskl (pskl_all_syn B) [=] empty).
    { assert (Hsub : ftvar_in_pskl (pskl_all_syn B) [<=] dom Θ0).
      { intros x Hx. apply a_binds_tvar_in_dom; exact (a_wf_pskl_ftv_binds Hwfp0 Hx). }
      assert (Hdisj : disjoint Ξ Θ0) by (clear - Huq; solve_uniq).
      unfold disjoint in Hdisj. clear - Hdisj Hsub. fsetdec. }
    assert (HΞA : dom Ξ ∩ ftvar_in_pskl A [=] empty).
    { assert (Hsub : ftvar_in_pskl A [<=] dom Θ0).
      { intros x Hx. apply a_binds_tvar_in_dom; exact (a_wf_pskl_ftv_binds Hwfp Hx). }
      assert (Hdisj : disjoint Ξ Θ0) by (clear - Huq; solve_uniq).
      unfold disjoint in Hdisj. clear - Hdisj Hsub. fsetdec. }
    remember (restrict_l (dom Ξ) ρ) as ρ0 eqn:Eρ0.
    assert (Hρ0incl : forall a b, In (a, b) ρ0 -> In (a, b) ρ)
      by (subst ρ0; intros a b Hin; eapply restrict_l_incl; exact Hin).
    assert (Hcl00 : cols_l ρ0 [<=] cols_l ρ)
      by (subst ρ0; apply cols_l_restrict_l).
    assert (Hcr00 : cols_r ρ0 [<=] cols_r ρ)
      by (subst ρ0; apply cols_r_restrict_l).
    assert (HΞcols : forall a, a `in` dom Ξ -> a `notin` cols_l ρ0)
      by (subst ρ0; intros a Ha; apply restrict_l_notin; exact Ha).
    assert (HrΘ0 : rel_aenv ρ0 V Θ0 Θ0')
      by (subst ρ0; apply rel_aenv_restrict_l; [ exact HrΘ | exact HΞΘ0 ]).
    assert (HrB0 : rel_pskl ρ0 V B B2).
    { subst ρ0. apply rel_pskl_restrict_l; [ exact HrB | ].
      simpl in HΞB. clear - HΞB. fsetdec. }
    assert (HrA0 : rel_pskl ρ0 V A P')
      by (subst ρ0; apply rel_pskl_restrict_l; [ exact HrP | exact HΞA ]).
    assert (Hagr0 : flex_agree_rel ρ0 V Θ0 Θ0')
      by (eapply flex_agree_rel_weaken;
          [ exact Hagr | exact Hρ0incl | intros x Hx; exact Hx ]).
    assert (Hinj0 : rel_inj ρ0 V)
      by (eapply rel_inj_sub; [ exact Hinj | exact Hρ0incl ]).
    assert (Hfun0 : rel_fun ρ0 V (dom Θ0))
      by (eapply rel_fun_weaken;
          [ exact Hfun | exact Hρ0incl | intros x Hx; exact Hx ]).
    assert (Hcov0 : V ∪ cols_r ρ0 [<=] S0) by (clear - Hcov Hcr00; fsetdec).
    (* ⚠️ ρ0 must survive the row's later bare [subst]s, so drop its defining
       equation now — every fact about it is already an assert above. *)
    clear Eρ0.
    assert (Hcl0 : cols_l (restrict_pairs α α2 ρ0) [<=] cols_l ρ0)
      by apply cols_l_restrict_pairs.
    assert (Hcr0 : cols_r (restrict_pairs α α2 ρ0) [<=] cols_r ρ0)
      by apply cols_r_restrict_pairs.
    assert (Hαl : α `notin` cols_l (restrict_pairs α α2 ρ0))
      by apply restrict_pairs_notin_l.
    assert (Hα2r : α2 `notin` cols_r (restrict_pairs α α2 ρ0))
      by apply restrict_pairs_notin_r.
    assert (HrΘr : rel_aenv (restrict_pairs α α2 ρ0) V Θ0 Θ0')
      by (apply rel_aenv_restrict; [ exact HrΘ0 | exact HfrΘ | exact Hα2f ]).
    assert (HrΘ' : rel_aenv ((α, α2) :: restrict_pairs α α2 ρ0) V
                     ((α ~ abind_tvar) ++ Θ0) ((α2 ~ abind_tvar) ++ Θ0')).
    { apply rel_aenv__cons;
        [ apply rel_atom__pair; left; reflexivity | constructor | ].
      eapply rel_aenv_mono;
        [ exact HrΘr | intros x y Hx; right; exact Hx | intros x Hx; exact Hx ]. }
    assert (HrBr : rel_pskl (restrict_pairs α α2 ρ0) V B B2)
      by (apply rel_pskl_restrict;
          [ exact HrB0 | clear - HfrB; fsetdec
          | clear - Hα2 HcovP; simpl in HcovP; fsetdec ]).
    assert (HrAr : rel_pskl (restrict_pairs α α2 ρ0) V A P')
      by (apply rel_pskl_restrict;
          [ exact HrA0 | clear - HfrA; fsetdec
          | clear - Hα2 HcovP; simpl in HcovP; fsetdec ]).
    assert (HrB' : rel_pskl ((α, α2) :: restrict_pairs α α2 ρ0) V
                     (open_pskl_wrt_pskl B (pskl_var_f α))
                     (open_pskl_wrt_pskl B2 (pskl_var_f α2)))
      by (apply rel_pskl_open_pair; exact HrBr).
    assert (HrA' : rel_pskl ((α, α2) :: restrict_pairs α α2 ρ0) V A P')
      by (eapply rel_pskl_mono;
          [ exact HrAr | intros x y Hx; right; exact Hx
          | intros x Hx; exact Hx ]).
    assert (Hagr' : flex_agree_rel ((α, α2) :: restrict_pairs α α2 ρ0) V
                      ((α ~ abind_tvar) ++ Θ0) ((α2 ~ abind_tvar) ++ Θ0')).
    { apply flex_agree_rel_push_look; [ | exact Hαd | exact Hα2d ].
      eapply flex_agree_rel_weaken;
        [ exact Hagr0 | intros x y Hx; eapply restrict_pairs_incl; exact Hx
        | intros x Hx; exact Hx ]. }
    assert (Hinj' : rel_inj ((α, α2) :: restrict_pairs α α2 ρ0) V)
      by (apply rel_inj_push;
          [ eapply rel_inj_sub;
              [ exact Hinj0 | intros x y Hx; eapply restrict_pairs_incl; exact Hx ]
          | exact Hα2V | exact Hα2r ]).
    assert (Hfun' : rel_fun ((α, α2) :: restrict_pairs α α2 ρ0) V
                      (dom ((α ~ abind_tvar) ++ Θ0))).
    { simpl. apply rel_fun_push;
        [ eapply rel_fun_weaken;
            [ exact Hfun0 | intros x y Hx; eapply restrict_pairs_incl; exact Hx
            | intros x Hx; exact Hx ]
        | exact HαV | exact Hαl ]. }
    assert (Hwf' : {{ ⊢ ((α ~ abind_tvar) ++ Θ0) }}a)
      by (apply a_wf_aenv__tvar; [ exact Hαd | exact Hwf ]).
    assert (Huq2' : uniq ((α2 ~ abind_tvar) ++ Θ0'))
      by (clear - Huq2p Hα2d; solve_uniq).
    assert (Hftv2' : ftvar_in_aenv ((α2 ~ abind_tvar) ++ Θ0') [<=] add α2 S0)
      by (simpl; clear - Hftv2; fsetdec).
    assert (Hscp' : V [<=] ftvar_in_aenv ((α ~ abind_tvar) ++ Θ0))
      by (simpl; clear - Hscp; fsetdec).
    assert (HdΘ' : dom ((α2 ~ abind_tvar) ++ Θ0') [<=] add α2 S0)
      by (simpl; clear - HdΘ; fsetdec).
    assert (Hcov' : V ∪ cols_r ((α, α2) :: restrict_pairs α α2 ρ0)
                    [<=] add α2 S0)
      by (simpl; clear - Hcov0 Hcr0; fsetdec).
    assert (HcovP' : ftvar_in_pskl (open_pskl_wrt_pskl B2 (pskl_var_f α2))
                     ∪ ftvar_in_pskl P' [<=] add α2 S0).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B2 (pskl_var_f α2))
        as Hu1. simpl in Hu1, HcovP. clear - Hu1 HcovP. fsetdec. }
    assert (Hwfp0' : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ
                       (open_pskl_wrt_pskl B (pskl_var_f α)) }}a)
      by (apply a_wf_pskl_all_syn_open_tvar;
          [ exact Hwfp0 | clear - Hαd HfrB; fsetdec ]).
    assert (Hwfp' : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ A }}a)
      by (eapply a_wf_pskl_tvar_mono;
          [ exact Hwfp
          | intros γ Hγ; apply (a_binds_tvar_weaken_mid nil (α ~ abind_tvar));
            exact Hγ ]).
    assert (Hblk' : forall a, a `in` dom (Ξ ++ (α ~ abind_tvar) ++ Θ1) ->
              a `notin` dom ((α ~ abind_tvar) ++ Θ0) ->
              a `notin` cols_l ((α, α2) :: restrict_pairs α α2 ρ0)).
    { intros a Ha Hn. simpl in Ha, Hn |- *.
      assert (Hne : a <> α) by (clear - Hn; fsetdec).
      repeat rewrite dom_app in Ha. simpl dom in Ha.
      assert (Hc : a `notin` cols_l ρ0).
      { destruct (AtomSetProperties.In_dec a (dom Ξ)) as [HaΞ | HaΞ].
        - exact (HΞcols a HaΞ).
        - assert (HaΘ1 : a `in` dom Θ1) by (clear - Ha HaΞ Hne; fsetdec).
          assert (Hc0 : a `notin` cols_l ρ)
            by (apply Hblk; [ exact HaΘ1 | clear - Hn; fsetdec ]).
          clear - Hc0 Hcl00. fsetdec. }
      clear - Hne Hc Hcl0. fsetdec. }
    destruct (IH (add α2 S0) ((α2 ~ abind_tvar) ++ Θ0')
                (open_pskl_wrt_pskl B2 (pskl_var_f α2)) P'
                ((α, α2) :: restrict_pairs α α2 ρ0) V
                HrΘ' HrB' HrA' Hagr' Hinj' Hfun' Hwf' Huq2' Hftv2' Hscp'
                Hblk' HdΘ' Hcov' HcovP' Hwfp0' Hwfp')
      as (S1 & ρe & Θ1out & Q' & De & HrΘout & Hagrout & HrQ & Hext & Hdomout).
    (* ---- side 1's output, via a_sub's own soundness ---- *)
    destruct ((proj1 a_sub_output_wf_bundle) _ _ _ _ _ _ _ Hprem Hwf' Hwfp0'
                Hwfp') as [Hle1 [HwfOut HwfQ]].
    assert (HuqOut : uniq (Ξ ++ (α ~ abind_tvar) ++ Θ1))
      by (apply a_wf_aenv_uniq; exact HwfOut).
    assert (HΞΘ1 : dom Ξ ∩ dom Θ1 [=] empty).
    { assert (Hd : disjoint Ξ ((α ~ abind_tvar) ++ Θ1))
        by (clear - HuqOut; solve_uniq).
      unfold disjoint in Hd. simpl in Hd. clear - Hd. fsetdec. }
    assert (HwfΘ1 : {{ ⊢ Θ1 }}a).
    { eapply a_wf_aenv_strip_prefix.
      eapply a_wf_aenv_strip_prefix with (Ξ := Ξ). simpl_env. exact HwfOut. }
    assert (Hftv1 : ftvar_in_aenv Θ1 [<=] dom Θ1)
      by (apply a_wf_aenv_ftv_dom; exact HwfΘ1).
    assert (HΞf1 : dom Ξ ∩ ftvar_in_aenv Θ1 [=] empty)
      by (clear - HΞΘ1 Hftv1; fsetdec).
    (* ---- the pair list the premise ran at, and its injectivity ---- *)
    assert (Hinjout : rel_inj (ρe ++ (α, α2) :: restrict_pairs α α2 ρ0) V)
      by (eapply rel_inj_app; [ exact Hinj' | exact Hext | exact Hcov' ]).
    assert (Hαρe : forall b, ~ In (α, b) ρe).
    { intros b Hin. destruct Hext as [Hxfr _]. destruct (Hxfr _ _ Hin) as [Hna _].
      apply Hna. simpl. clear; fsetdec. }
    assert (Hαonly : forall y,
              rel_atom (ρe ++ (α, α2) :: restrict_pairs α α2 ρ0) V α y ->
              y = α2).
    { intros y Hat. inversion Hat as [ a0 b0 Hin | a0 HinV ]; subst.
      - apply in_app_or in Hin. destruct Hin as [Hin | [Ehd | Hin]].
        + exfalso. exact (Hαρe _ Hin).
        + inversion Ehd; reflexivity.
        + exfalso. apply (@restrict_pairs_notin_l α α2 ρ0).
          eapply cols_l_in; exact Hin.
      - exfalso. exact (HαV HinV). }
    (* ---- SPLIT the premise's output at the junk suffix, then the opener ---- *)
    destruct (@rel_aenv_app_inv_l Ξ
                (ρe ++ (α, α2) :: restrict_pairs α α2 ρ0) V
                ((α ~ abind_tvar) ++ Θ1) Θ1out HrΘout)
      as (Ξ2 & Θrest & Eout & HrΞ2 & HrTail).
    subst Θ1out.
    destruct (rel_aenv_cons_inv_l HrTail)
      as (b & bd2 & Θ1' & E2 & Hab2 & Hbd2 & HrΘ1').
    subst Θrest. inversion Hbd2; subst.
    assert (Eb : b = α2)
      by (apply Hαonly; exact Hab2).
    subst b.
    (* ---- side 2's junk is apart from side 2's input ---- *)
    assert (HΞ2Θ0 : forall a, a `in` dom Ξ2 -> a `notin` dom Θ0').
    { intros a Ha.
      destruct (rel_aenv_dom_r_inv HrΞ2 Ha) as (a' & Ha' & Hat').
      inversion Hat' as [ x0 y0 Hin | x0 HinV ]; subst.
      - apply in_app_or in Hin. destruct Hin as [Hin | [Ehd | Hin]].
        + destruct Hext as [Hxfr _]. destruct (Hxfr _ _ Hin) as [_ Hnb].
          clear - Hnb HdΘ. fsetdec.
        + exfalso. injection Ehd as E1 E2x. subst a'.
          clear - Ha' Hfr. fsetdec.
        + exfalso. apply (HΞcols a' Ha'). eapply cols_l_in.
          eapply restrict_pairs_incl; exact Hin.
      - exfalso.
        assert (Had : a `in` dom Θ0) by (apply Hscp in HinV; clear - HinV Hsc0; fsetdec).
        assert (Hd : disjoint Ξ Θ0) by (clear - Huq; solve_uniq).
        unfold disjoint in Hd. clear - Hd Ha' Had. fsetdec. }
    assert (HcovS : ftvar_in_aenv ((α2 ~ abind_tvar) ++ Θ0')
                    ∪ ftvar_in_pskl (open_pskl_wrt_pskl B2 (pskl_var_f α2))
                    ∪ ftvar_in_pskl P' [<=] add α2 S0).
    { repeat apply AtomSetProperties.union_subset_3;
        [ exact Hftv2' | clear - HcovP'; fsetdec | clear - HcovP'; fsetdec ]. }
    destruct (e_sub_sub_flex_sound) as [HsndS _].
    destruct (HsndS _ _ _ _ _ _ _ _ _ De Huq2' HcovS)
      as [HaD [HuqOut2 [Hftv1out HftvQ]]].
    assert (Huq2Ξ : uniq (Ξ2 ++ Θ0')).
    { apply uniq_app_4.
      - clear - HuqOut2. solve_uniq.
      - exact Huq2p.
      - apply disjoint_from_pointwise. exact HΞ2Θ0. }
    (* ⭐ the e-rule PINS the premise's yield; the motive only relates it *)
    assert (EQ' : Q' = open_pskl_wrt_pskl B2 (pskl_var_f α2))
      by (exact ((proj1 e_sub_tc_yield) _ _ _ _ _ _ _ _ _ De eq_refl eq_refl)).
    subst Q'.
    (* ---- the e-side conclusion ---- *)
    assert (Dc : {{ S0 ↝ S1 ⊨ Θ0' ⊢[ a_sub_mode_ty | mode_tc |
                    (pskl_all_syn B2) ] P' ⩽ (pskl_all_syn B2) ⊣ Θ1' }}e).
    { apply e_sub__forall_r with (α := α2) (Ξ := Ξ2);
        [ eapply rel_pskl_ghost_free; [ exact HrP0 | exact Hgf ]
        | eapply rel_aenv_suffix; [ exact HrΞ2 | exact Hsuf ]
        | exact Huq2Ξ | exact Hα2 | exact De ]. }
    (* ---- hand back at the CALLER's pair list ---- *)
    remember (restrict_l (dom Ξ) ρe) as ρeo eqn:Eρeo.
    assert (Hρeoincl : forall a b0, In (a, b0) ρeo -> In (a, b0) ρe)
      by (subst ρeo; intros a b0 Hin; eapply restrict_l_incl; exact Hin).
    assert (HρeoΞ : forall a b0, In (a, b0) ρeo -> a `notin` dom Ξ).
    { subst ρeo. intros a b0 Hin Ha.
      apply (restrict_l_notin ρe Ha). eapply cols_l_in; exact Hin. }
    assert (Hdomeo : forall a b0, In (a, b0) ρeo ->
              a `in` dom Θ1 /\ b0 `in` dom Θ1').
    { intros a b0 Hin.
      pose proof (Hρeoincl _ _ Hin) as Hin'.
      pose proof (HρeoΞ _ _ Hin) as HaΞ.
      destruct (Hdomout _ _ Hin') as [Hd1 Hd2].
      destruct Hext as [Hxfr _]. destruct (Hxfr _ _ Hin') as [Hna Hnb].
      assert (Hane : a <> α) by (intros ->; apply Hna; simpl; clear; fsetdec).
      assert (Hbne : b0 <> α2) by (intros ->; apply Hnb; clear; fsetdec).
      assert (HbΞ2 : b0 `notin` dom Ξ2).
      { intros Hb2. destruct (rel_aenv_dom_r_inv HrΞ2 Hb2) as (a'' & Ha'' & Hat'').
        assert (Ea : a'' = a).
        { apply (Hinjout a'' a b0 Hat'').
          apply rel_atom__pair. apply in_or_app; left; exact Hin'. }
        subst a''. contradiction. }
      simpl_env in Hd1. simpl_env in Hd2.
      split; [ clear - Hd1 HaΞ Hane; fsetdec
             | clear - Hd2 HbΞ2 Hbne; fsetdec ]. }
    exists S1, ρeo, Θ1', (pskl_all_syn B2).
    split; [ exact Dc | ].
    (* the CONTEXT relation: drop the JUNK pairs and the OPENER pair, then
       widen back to the caller's list *)
    assert (HαfΘ1 : α `notin` ftvar_in_aenv Θ1).
    { assert (Hd : α `notin` dom Θ1) by (clear - Hfr; fsetdec).
      clear - Hd Hftv1. fsetdec. }
    assert (Hα2fΘ1 : α2 `notin` ftvar_in_aenv Θ1').
    { intros Hin. destruct (rel_aenv_ftv_corr_r HrΘ1' Hin) as (a & Ha & Hat).
      assert (Ea : a = α).
      { apply (Hinjout a α α2 Hat). apply rel_atom__pair.
        apply in_or_app; right; left; reflexivity. }
      subst a. exact (HαfΘ1 Ha). }
    assert (Hincl : forall a b0,
              In (a, b0) (restrict_pairs α α2
                            (restrict_l (dom Ξ)
                               (ρe ++ (α, α2) :: restrict_pairs α α2 ρ0))) ->
              In (a, b0) (ρeo ++ ρ)).
    { intros a b0 Hin.
      assert (Hane : a <> α).
      { intros ->.
        apply (@restrict_pairs_notin_l α α2
                 (restrict_l (dom Ξ)
                    (ρe ++ (α, α2) :: restrict_pairs α α2 ρ0))).
        eapply cols_l_in; exact Hin. }
      apply restrict_pairs_incl in Hin.
      assert (HaΞ : a `notin` dom Ξ).
      { intros Ha.
        apply (restrict_l_notin
                 (ρe ++ (α, α2) :: restrict_pairs α α2 ρ0) Ha).
        eapply cols_l_in; exact Hin. }
      apply restrict_l_incl in Hin.
      apply in_app_or in Hin. destruct Hin as [Hin | [Ehd | Hin]].
      - apply in_or_app; left. subst ρeo. apply restrict_l_in; assumption.
      - exfalso. injection Ehd as E1 E2x. apply Hane. symmetry. exact E1.
      - apply in_or_app; right. apply Hρ0incl.
        eapply restrict_pairs_incl; exact Hin. }
    assert (HrΘfin : rel_aenv (ρeo ++ ρ) V Θ1 Θ1').
    { eapply rel_aenv_mono;
        [ exact (rel_aenv_restrict
                   (rel_aenv_restrict_l HrΘ1' HΞf1) HαfΘ1 Hα2fΘ1)
        | exact Hincl | intros x Hx; exact Hx ]. }
    split; [ exact HrΘfin | ].
    assert (Hextfin : rel_ext ρeo (ftvar_in_aenv Θ0) S0).
    { destruct Hext as [Hxfr [Hri Hlf]]. unfold rel_ext.
      split; [ | split ].
      - intros a b0 Hin. destruct (Hxfr _ _ (Hρeoincl _ _ Hin)) as [Hna Hnb].
        simpl in Hna. split; [ clear - Hna; fsetdec | clear - Hnb; fsetdec ].
      - intros a1 a2' b0 H1 H2.
        exact (Hri a1 a2' b0 (Hρeoincl _ _ H1) (Hρeoincl _ _ H2)).
      - intros a b1 b2 H1 H2.
        exact (Hlf a b1 b2 (Hρeoincl _ _ H1) (Hρeoincl _ _ H2)). }
    assert (Hagrfin : flex_agree_rel (ρeo ++ ρ) V Θ1 Θ1').
    { eapply rel_aenv_flex_agree_ext;
        [ exact HrΘfin | exact Hinj | exact Hfun | exact Hextfin
        | apply dom_subset_ftvar_in_aenv
        | clear - Hscp Hsc0; fsetdec | exact Hcov | exact Hblk ]. }

    split; [ exact Hagrfin | ].
    (* ---- the YIELD is the check-against, so it just widens ---- *)
    split.
    { eapply rel_pskl_mono;
        [ exact HrP0 | intros x y Hx; apply in_or_app; right; exact Hx
        | intros x Hx; exact Hx ]. }
    (* ---- rel_ext, weakened off the opener ---- *)
    split; [ exact Hextfin | ].
    exact Hdomeo.
  - (* S-UnivGhostR : output = ⫯subject, context unchanged *)
    intros Θ0 P Hg.
    intros S0 Θ0' P0' P' ρ V HrΘ HrP0 HrP Hagr Hinj Hfun Hwf Huq2p Hftv2
      Hscp Hblk HdΘ Hcov HcovP Hwfp0 Hwfp.
    inversion HrP0 as [ | n0 | u0 v0 Hu0 | A1 A2 A3 A4 Hu1 Hu2 | B1 B2 Hu3
                      | | C1 C2 Hu4 ]; subst.
    exists S0, (@nil (atom * atom)%type), Θ0', (pskl_univ_ghost P').
    split.
    { apply e_sub__univ_ghost_r.
      eapply rel_pskl_guarded; [ exact HrP | exact Hg ]. }
    simpl.
    split; [ exact HrΘ | ].
    split; [ exact Hagr | ].
    split; [ apply rel_pskl__univ_ghost; exact HrP | ].
    split.
    { unfold rel_ext. repeat split; intros; simpl in *; contradiction. }
    intros a b Hin. inversion Hin.
  - (* S-FlexMono : hand to the WALK at the empty pending suffix *)
    intros NM M P0 Θ0 Θ1 α Q Hf IHf.
    intros S0 Θ0' P0' P' ρ V HrΘ HrP0 HrP Hagr Hinj Hfun Hwf Huq2p Hftv2
      Hscp Hblk HdΘ Hcov HcovP Hwfp0 Hwfp.
    inversion HrP as [ | n1 | u1 α2 Hatα | D1 D2 D3 D4 Hu5 Hu6 | E1 E2 Hu7
                     | | F1 F2 Hu8 ]; subst.
    assert (HcovP0 : ftvar_in_pskl P0' [<=] S0)
      by (simpl in HcovP; clear - HcovP; fsetdec).
    assert (Hbα : a_binds_tvar α Θ0).
    { inversion Hwfp as [ | Θz Δz αz Hd | | | | ]; subst. exact Hd. }
    destruct (IHf S0 Θ0' nil α2 P0' ρ V HrΘ (@rel_aenv__nil ρ V) Hatα HrP0
                ltac:(simpl_env; exact Hagr) Hinj
                ltac:(simpl_env; exact Hfun)
                ltac:(simpl_env; exact Hwf) a_decls__nil a_decls__nil
                ltac:(simpl_env; exact Huq2p)
                ltac:(simpl_env; exact Hftv2)
                ltac:(simpl_env; exact Hscp)
                ltac:(simpl_env; exact Hblk)
                ltac:(simpl_env; exact HdΘ) Hcov HcovP0
                ltac:(simpl_env; exact Hwfp0)
                ltac:(simpl_env; exact Hbα))
      as (S1 & ρe & Θ1' & Q' & De & HrΘ1 & Hagr1 & HrQ & Hext & Hdom1).
    exists S1, ρe, Θ1', Q'.
    split; [ apply e_sub__flex_mono; exact De | ].
    split; [ exact HrΘ1 | ].
    split; [ exact Hagr1 | ].
    split; [ exact HrQ | ].
    split; [ simpl_env in Hext; exact Hext | ]. exact Hdom1.
  - (* ⭐ S-Arrow : consistency on the domain, then the codomain at ITS output *)
    intros NM M Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc Hs IHs.
    intros S0 Θ0' P0' P' ρ V HrΘ HrP0 HrP Hagr Hinj Hfun Hwf Huq2p Hftv2
      Hscp Hblk HdΘ Hcov HcovP Hwfp0 Hwfp.
    inversion HrP0 as [ | n0 | u0 v0 Hu0 | A1 A2 P0a2 P0b2 HrP0a HrP0b
                      | A3 A4 Hu1 | | A5 A6 Hu2 ]; subst.
    inversion HrP as [ | n1 | u3 v3 Hu3 | B1 B2 P12 P22 HrP1 HrP2
                     | B3 B4 Hu4 | | B5 B6 Hu5 ]; subst.
    inversion Hwfp0 as [ Θx Δx | Θx Δx αx Hbx | Θx Δx Xa Xb Hw0a Hw0b
                       | Lx Θx Δx Xp Hallx | Θx Δx
                       | Θx Δx Xp Hgx Hwix ]; subst.
    inversion Hwfp as [ Θy Δy | Θy Δy αy Hby | Θy Δy Ya Yb Hw1a Hw1b
                      | Ly Θy Δy Yp Hally | Θy Δy
                      | Θy Δy Yp Hgy Hwiy ]; subst.
    assert (Hsc0 : ftvar_in_aenv Θ0 [<=] dom Θ0)
      by (apply a_wf_aenv_ftv_dom; exact Hwf).
    assert (Hdm0 : dom Θ0 [<=] dom Θ1) by (exact (auc_dom_mono_consis Hc)).
    assert (Hdm1 : dom Θ1 [<=] dom Θ2)
      by (exact ((proj1 a_sub_sub_flex_dom_mono) _ _ _ _ _ _ _ Hs)).
    assert (Hblk1 : forall a, a `in` dom Θ1 -> a `notin` dom Θ0 ->
                    a `notin` cols_l ρ)
      by (intros a Ha Hn; apply Hblk; [ clear - Ha Hdm1; fsetdec | exact Hn ]).
    assert (HcovP1 : ftvar_in_pskl P0a2 ∪ ftvar_in_pskl P12 [<=] S0)
      by (simpl in HcovP; clear - HcovP; fsetdec).
    destruct (lift_consis_nil Hc HrΘ HrP0a HrP1 Hagr Hinj Hfun Hwf Huq2p
                Hftv2 Hscp Hblk1 HdΘ Hcov HcovP1 Hw0a Hw1a)
      as (S1 & ρe1 & Θ1' & Q1' & D1e & HrΘ1 & Hagr1 & HrQ1 & Hext1 & Hdom1).
    pose proof (e_consis_supply_grows D1e) as Hgr1.
    assert (HdΘ1 : dom Θ1' [<=] S1).
    { pose proof ((proj2 (proj2 e_assign_unify_consis_dom_upper))
                    _ _ _ _ _ _ _ _ _ D1e) as Hup.
      clear - Hup HdΘ Hgr1. fsetdec. }
    assert (HcovE : ftvar_in_aenv Θ0' ∪ ftvar_in_pskl P0a2
                    ∪ ftvar_in_pskl P12 [<=] S0)
      by (clear - Hftv2 HcovP1; fsetdec).
    assert (Hftv1 : ftvar_in_aenv Θ1' [<=] S1)
      by (eapply (proj2 (proj2 e_assign_unify_consis_ctx_ftvar));
          [ exact D1e | exact HcovE ]).
    assert (HcovE2 : ftvar_in_aenv Θ0' ∪ ftvar_in_pskl P0a2
                     ∪ ftvar_in_pskl P12 ∪ empty ∪ empty [<=] S0)
      by (clear - HcovE; fsetdec).
    assert (Huq1' : uniq Θ1').
    { pose proof (e_consis_sound D1e Huq2p HcovE2) as Ha1.
      exact ((proj2 (proj2 a_assign_unify_consis_uniq)) _ _ _ _ _ _ _ Ha1
               Huq2p). }
    (* ---- side 1's context at the first half's output ---- *)
    destruct (a_consis_isub_wf_nil Hc Hwf Hw0a Hw1a) as [Hle01 HwfΘ1].
    assert (Hd1s : dom Θ1 [<=] ftvar_in_aenv Θ1)
      by (apply dom_subset_ftvar_in_aenv).
    assert (Hscp1 : V [<=] ftvar_in_aenv Θ1)
      by (clear - Hscp Hsc0 Hdm0 Hd1s; fsetdec).
    assert (Hwfp0b1 : {{ Θ1 ⨟ empty ⊢ₚₛ P0b }}a)
      by (eapply a_isub_wf_pskl; [ exact Hle01 | exact Hw0b ]).
    assert (Hwfp21 : {{ Θ1 ⨟ empty ⊢ₚₛ P2 }}a)
      by (eapply a_isub_wf_pskl; [ exact Hle01 | exact Hw1b ]).
    (* ---- the relation, widened by the first half's new pairs ---- *)
    assert (Hinj1 : rel_inj (ρe1 ++ ρ) V)
      by (eapply rel_inj_app; [ exact Hinj | exact Hext1 | exact Hcov ]).
    assert (HVdom0 : V [<=] dom Θ0) by (clear - Hscp Hsc0; fsetdec).
    assert (Hfun1 : rel_fun (ρe1 ++ ρ) V (dom Θ1)).
    { eapply rel_fun_app;
        [ exact Hfun | exact Hext1 | apply dom_subset_ftvar_in_aenv
        | intros a Ha Hn; exact (Hblk1 a Ha Hn)
        | intros a Ha Hn; clear - HVdom0 Hn; fsetdec ]. }
    assert (HrP0b' : rel_pskl (ρe1 ++ ρ) V P0b P0b2)
      by (apply rel_pskl_widen; exact HrP0b).
    assert (HrP2' : rel_pskl (ρe1 ++ ρ) V P2 P22)
      by (apply rel_pskl_widen; exact HrP2).
    assert (Hc1r : cols_r ρe1 [<=] S1).
    { intros y Hy. destruct (cols_r_in_inv _ _ Hy) as (a & Hin).
      destruct (Hdom1 _ _ Hin) as [_ Hd2]. clear - Hd2 HdΘ1. fsetdec. }
    assert (Hcov1 : V ∪ cols_r (ρe1 ++ ρ) [<=] S1).
    { rewrite cols_r_app. clear - Hcov Hc1r Hgr1. fsetdec. }
    assert (Hblk2 : forall a, a `in` dom Θ2 -> a `notin` dom Θ1 ->
                    a `notin` cols_l (ρe1 ++ ρ)).
    { intros a Ha Hn. rewrite cols_l_app.
      assert (Hc1 : a `notin` cols_l ρe1).
      { intros Hy. destruct (cols_l_in_inv _ _ Hy) as (y & Hin).
        destruct (Hdom1 _ _ Hin) as [Hd1 _]. contradiction. }
      assert (Hc2 : a `notin` cols_l ρ)
        by (apply Hblk; [ exact Ha | clear - Hn Hdm0; fsetdec ]).
      clear - Hc1 Hc2. fsetdec. }
    assert (HcovP2 : ftvar_in_pskl P0b2 ∪ ftvar_in_pskl P22 [<=] S1)
      by (simpl in HcovP; clear - HcovP Hgr1; fsetdec).
    destruct (IHs S1 Θ1' P0b2 P22 (ρe1 ++ ρ) V HrΘ1 HrP0b' HrP2' Hagr1
                Hinj1 Hfun1 HwfΘ1 Huq1' Hftv1 Hscp1 Hblk2 HdΘ1 Hcov1 HcovP2
                Hwfp0b1 Hwfp21)
      as (S2 & ρe2 & Θ2' & Q2' & D2e & HrΘ2 & Hagr2 & HrQ2 & Hext2 & Hdom2).
    assert (HcovE3 : ftvar_in_aenv Θ1' ∪ ftvar_in_pskl P0b2
                     ∪ ftvar_in_pskl P22 [<=] S1)
      by (clear - Hftv1 HcovP2; fsetdec).
    assert (Hdm2' : dom Θ1' [<=] dom Θ2').
    { pose proof (e_sub_sound D2e Huq1' HcovE3) as Ha2.
      exact ((proj1 a_sub_sub_flex_dom_mono) _ _ _ _ _ _ _ Ha2). }
    exists S2, (ρe2 ++ ρe1), Θ2', (pskl_arrow Q1' Q2').
    split; [ eapply e_sub__arrow; [ exact D1e | exact D2e ] | ].
    rewrite app_assoc.
    split; [ exact HrΘ2 | ].
    split; [ exact Hagr2 | ].
    split.
    { constructor; [ | exact HrQ2 ].
      eapply rel_pskl_mono;
        [ exact HrQ1 | intros x y Hx; apply in_or_app; right; exact Hx
        | intros x Hx; exact Hx ]. }
    split.
    { eapply rel_ext_app;
        [ exact Hext1 | exact Hext2
        | clear - Hsc0 Hdm0 Hd1s; fsetdec
        | exact Hgr1
        | intros a b Hin; destruct (Hdom1 _ _ Hin) as [Hd1 Hd2];
          split; [ clear - Hd1 Hd1s; fsetdec | clear - Hd2 HdΘ1; fsetdec ] ]. }
    intros a b Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + destruct (Hdom2 _ _ Hin) as [Hd1 Hd2]. split; [ exact Hd1 | exact Hd2 ].
    + destruct (Hdom1 _ _ Hin) as [Hd1 Hd2].
      split; [ clear - Hd1 Hdm1; fsetdec | clear - Hd2 Hdm2'; fsetdec ].
  - (* ⭐⭐ S-ForallL — the COMMON opener, and the extract is NOT inductive.
       [a_extract_family_of_instance] moves side 1's opener to any fresh
       atom with the SAME [Ξ ↪ P1], and side 2's is ours to pick subject
       only to [α' ∉ S0]; so both sides run at ONE atom and the relation
       carries it by IDENTITY.  ⭐ The opener never enters the subtyping
       premise's CONTEXT — the extract consumes it and leaves [Θ0] alone —
       so there is no pair to push and no junk suffix to strip. *)
    intros α NM M P0 Θ0 Θ1 P Q Ξ P1 Hne Hg Hfr Hex Huq Hwf1 Hs IHs.
    intros S0 Θ0' P0' P' ρ V HrΘ HrP0 HrP Hagr Hinj Hfun Hwf Huq2p Hftv2
      Hscp Hblk HdΘ Hcov HcovP Hwfp0 Hwfp.
    inversion HrP as [ | n0 | u0 v0 Hu0 | A1 A2 A3 A4 Hu1 Hu2
                     | Pb Pb2 HrPb | | C1 C2 Hu3 ]; subst.
    (* ---- side 1's data ---- *)
    assert (Hsc0 : ftvar_in_aenv Θ0 [<=] dom Θ0)
      by (apply a_wf_aenv_ftv_dom; exact Hwf).
    assert (HfrP : α `notin` ftvar_in_pskl P) by (clear - Hfr; solve_notin_auto).
    assert (Hdm : dom (Ξ ++ Θ0) [<=] dom Θ1)
      by (exact ((proj1 a_sub_sub_flex_dom_mono) _ _ _ _ _ _ _ Hs)).
    rewrite dom_app in Hdm.
    assert (HΞΘ0 : dom Ξ ∩ dom Θ0 [=] empty).
    { assert (Hdisj : disjoint Ξ Θ0) by (clear - Huq; solve_uniq).
      unfold disjoint in Hdisj. clear - Hdisj. fsetdec. }
    (* ⭐ THE BLOCK PREMISE [a_extract_rel_e] WANTS, read off the motive's
       own [Hblk]: the block is inside [dom Θ1] and outside [dom Θ0]. *)
    assert (HblkΞ : dom Ξ ∩ cols_l ρ [=] empty).
    { intros x. split; intros Hx; [ | clear - Hx; fsetdec ].
      exfalso.
      assert (HxΞ : x `in` dom Ξ) by (clear - Hx; fsetdec).
      assert (Hxc : x `in` cols_l ρ) by (clear - Hx; fsetdec).
      apply (Hblk x); [ clear - Hdm HxΞ; fsetdec
                      | clear - HΞΘ0 HxΞ; fsetdec | exact Hxc ]. }

    (* ---- the COMMON opener ---- *)
    assert (Hfam0 : exists L, forall a0,
              a0 `notin` (singleton α `union` ftvar_in_pskl P `union` L) ->
              {{ Θ0 ⊢ (open_pskl_wrt_pskl P (pskl_var_f a0))
                 ⊳[ NM , a0 , M ] P0 ⤳ Ξ ↪ P1 }}a)
      by (eapply a_extract_family_of_instance; [ exact Hex | exact HfrP ]).
    destruct Hfam0 as (L & Hfam).
    destruct (atom_fresh (S0 ∪ cols_l ρ ∪ ftvar_in_aenv Θ0 ∪ dom Θ0
                            ∪ dom Ξ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P0
                            ∪ singleton α ∪ L)) as [α' Hα'].
    pose proof (Hfam α' ltac:(clear - Hα'; solve_notin_auto)) as Hex'.
    assert (Hα'S0 : α' `notin` S0) by (clear - Hα'; solve_notin_auto).
    assert (Hα'cl : α' `notin` cols_l ρ) by (clear - Hα'; solve_notin_auto).
    assert (Hα'Θ0 : α' `notin` ftvar_in_aenv Θ0)
      by (clear - Hα'; solve_notin_auto).
    assert (Hα'd0 : α' `notin` dom Θ0) by (clear - Hα'; solve_notin_auto).
    assert (Hα'Ξ : α' `notin` dom Ξ) by (clear - Hα'; solve_notin_auto).
    assert (Hα'cr : α' `notin` cols_r ρ) by (clear - Hα'S0 Hcov; fsetdec).
    assert (Hα'd0' : α' `notin` dom Θ0') by (clear - Hα'S0 HdΘ; fsetdec).
    assert (Hα'V : α' `notin` V) by (clear - Hα'Θ0 Hscp; fsetdec).

    (* ---- the extract, at [add α' V] and [add α' S0] ---- *)
    assert (HrPo : rel_pskl ρ (add α' V)
                     (open_pskl_wrt_pskl P (pskl_var_f α'))
                     (open_pskl_wrt_pskl Pb2 (pskl_var_f α')))
      by (apply rel_pskl_open_var; exact HrPb).
    assert (HrP0w : rel_pskl ρ (add α' V) P0 P0')
      by (eapply rel_pskl_mono;
          [ exact HrP0 | intros x y Hx; exact Hx | clear; fsetdec ]).
    assert (Hagr2 : flex_agree_rel ρ (add α' V) Θ0 Θ0').
    { destruct Hagr as [HagV Hagp]. split; [ | exact Hagp ].
      intros x Hx. destruct (x == α') as [-> | Hnex].
      - split; intros Hfl; exfalso; apply a_flex_tvar_in_dom in Hfl;
          [ apply Hα'd0; exact Hfl | apply Hα'd0'; exact Hfl ].
      - apply HagV. clear - Hx Hnex. fsetdec. }
    assert (Hscp' : add α' V [<=] add α' (ftvar_in_aenv Θ0))
      by (clear - Hscp; fsetdec).
    assert (HdΘ' : dom Θ0' [<=] add α' S0) by (clear - HdΘ; fsetdec).
    assert (Hcov' : add α' V ∪ cols_r ρ [<=] add α' S0)
      by (clear - Hcov; fsetdec).
    assert (HcovP' : ftvar_in_pskl (open_pskl_wrt_pskl Pb2 (pskl_var_f α'))
                     ∪ ftvar_in_pskl P0' [<=] add α' S0).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Pb2
                    (pskl_var_f α')) as Hup.
      simpl in Hup. simpl in HcovP. clear - Hup HcovP. fsetdec. }
    assert (Hα'in : α' `in` add α' V) by (clear; fsetdec).
    destruct (a_extract_rel_e Hex' HrPo HrP0w Hα'in Hα'cl Hα'cr Hagr2
                Hscp' HblkΞ Hα'Ξ HdΘ' Hcov' HcovP')
      as (S1e & ρx & ρn & Ξ2 & P1' & De & EΞ1 & EΞ2 & Hρx & Hxblk & HrP1).
    pose proof (e_extract_block De) as (HΞ2S1 & HΞ2S0 & HuqΞ2 & HftvΞ2).
    pose proof (e_extract_supply_grows De) as Hgre.
    assert (Hdfl : dom Ξ [=] cols_l ρn)
      by (rewrite EΞ1; apply dom_flex_pairs_l).
    assert (Hdfr : dom Ξ2 [=] cols_r ρn)
      by (rewrite EΞ2; apply dom_flex_pairs_r).
    assert (HΞ2S : dom Ξ2 ∩ S0 [=] empty) by (clear - HΞ2S0; fsetdec).

    (* ⭐⭐ THE ρx COLUMN GOES BEFORE THE IH.  [ρx] is the extract's LEAKED
       OPENERS; the motive's [Hblk] cannot keep them out of [dom Θ1], and
       a [rel_fun] extension would owe the same, so the IH must run at
       [ρn ++ ρ].  ⭐ What pays is the extract's own block conjunct
       ([Hxblk]) together with the rule's SCOPING FILTER on [P1]: every
       free variable of [P1] is bound in [Ξ ++ Θ0], and ρx's atoms are in
       NEITHER half. *)
    assert (HftP1 : ftvar_in_pskl P1 [<=] dom (Ξ ++ Θ0)).
    { intros x Hx. apply a_binds_tvar_in_dom; exact (a_wf_pskl_ftv_binds Hwf1 Hx). }
    rewrite dom_app in HftP1.
    assert (Hdrop : rel_pskl (ρn ++ ρ) V P1 P1').
    { eapply rel_pskl_morph_ftv; [ exact HrP1 | | ].
      - intros a b Ha Hin. apply in_app_or in Hin.
        destruct Hin as [Hin | Hin]; [ exfalso | apply rel_atom__pair; exact Hin ].
        assert (Hal : a `in` cols_l ρx) by (eapply cols_l_in; exact Hin).
        destruct (Hρx _ _ Hin) as [Hnf _].
        pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds0.
        clear - Ha Hal Hnf Hxblk HftP1 Hds0. fsetdec.
      - intros a Ha Hv. apply rel_atom__id.
        assert (Hnea : a <> α')
          by (intros Ex; rewrite Ex in Ha;
              clear - Ha HftP1 Hα'd0 Hα'Ξ; fsetdec).
        clear - Hv Hnea. fsetdec. }

    (* ---- the IH, at [Ξ ++ Θ0] / [Ξ2 ++ Θ0'] ---- *)
    assert (HrΞ : rel_aenv (ρn ++ ρ) V Ξ Ξ2)
      by (rewrite EΞ1, EΞ2; apply rel_aenv_flex_pairs).
    assert (HrΘw : rel_aenv (ρn ++ ρ) V Θ0 Θ0')
      by (eapply rel_aenv_mono;
          [ exact HrΘ | intros x y Hx; apply in_or_app; right; exact Hx
          | intros x Hx; exact Hx ]).
    assert (HrΘΞ : rel_aenv (ρn ++ ρ) V (Ξ ++ Θ0) (Ξ2 ++ Θ0'))
      by (apply rel_aenv_app; [ exact HrΞ | exact HrΘw ]).
    assert (HrP0n : rel_pskl (ρn ++ ρ) V P0 P0')
      by (eapply rel_pskl_mono;
          [ exact HrP0 | intros x y Hx; apply in_or_app; right; exact Hx
          | intros x Hx; exact Hx ]).
    assert (HrPn : rel_pskl (ρn ++ ρ) V P Pb2)
      by (eapply rel_pskl_mono;
          [ exact HrPb | intros x y Hx; apply in_or_app; right; exact Hx
          | intros x Hx; exact Hx ]).
    assert (HrOpen : rel_pskl (ρn ++ ρ) V
                       (open_pskl_wrt_pskl P P1)
                       (open_pskl_wrt_pskl Pb2 P1'))
      by (apply rel_pskl_open_skl; [ exact HrPn | exact Hdrop ]).
    assert (HΞV : dom Ξ ∩ V [=] empty)
      by (clear - HΞΘ0 Hscp Hsc0; fsetdec).
    assert (Hnl : cols_l ρn ∩ (V ∪ cols_l ρ) [=] empty)
      by (clear - HΞV HblkΞ Hdfl; fsetdec).
    assert (Hnr : cols_r ρn ∩ (V ∪ cols_r ρ) [=] empty)
      by (clear - HΞ2S Hdfr Hcov; fsetdec).
    assert (HagrΞ : flex_agree_rel (ρn ++ ρ) V (Ξ ++ Θ0) (Ξ2 ++ Θ0')).
    { rewrite EΞ1, EΞ2. apply flex_agree_rel_push_pairs;
        [ exact Hagr | exact Hnl | exact Hnr ]. }
    assert (Hextn : rel_ext ρn (ftvar_in_aenv Θ0) S0).
    { apply rel_ext_flex_pairs;
        [ rewrite <- EΞ1; clear - Huq; solve_uniq
        | rewrite <- EΞ2; exact HuqΞ2
        | clear - Hdfl HΞΘ0 Hsc0; fsetdec
        | clear - Hdfr HΞ2S; fsetdec ]. }
    assert (Hinjn : rel_inj (ρn ++ ρ) V)
      by (eapply rel_inj_app; [ exact Hinj | exact Hextn | exact Hcov ]).
    assert (Hfunn : rel_fun (ρn ++ ρ) V (dom (Ξ ++ Θ0))).
    { eapply rel_fun_app;
        [ exact Hfun | exact Hextn
        | apply dom_subset_ftvar_in_aenv
        | intros a Ha Hn; rewrite dom_app in Ha;
          apply (Hblk a); [ clear - Hdm Ha Hn; fsetdec | exact Hn ]
        | intros a Ha Hn; rewrite dom_app in Ha;
          clear - Ha Hn Hscp Hsc0; fsetdec ]. }
    assert (HwfΞ : {{ ⊢ (Ξ ++ Θ0) }}a).
    { apply a_wf_aenv_decls_app;
        [ rewrite EΞ1; apply a_decls_flex_pairs_l | exact Huq | exact Hwf ]. }
    assert (HuqΞ2' : uniq (Ξ2 ++ Θ0')).
    { assert (Hd2 : dom Ξ2 ∩ dom Θ0' [=] empty)
        by (clear - HΞ2S HdΘ; fsetdec).
      clear - HuqΞ2 Huq2p Hd2. solve_uniq. }
    assert (Hftv2' : ftvar_in_aenv (Ξ2 ++ Θ0') [<=] S1e).
    { rewrite ftvar_in_aenv_app.
      clear - HftvΞ2 HΞ2S1 Hftv2 Hgre Hα'S0. fsetdec. }
    assert (HscpΞ : V [<=] ftvar_in_aenv (Ξ ++ Θ0))
      by (rewrite ftvar_in_aenv_app; clear - Hscp; fsetdec).
    assert (HblkIH : forall a, a `in` dom Θ1 -> a `notin` dom (Ξ ++ Θ0) ->
              a `notin` cols_l (ρn ++ ρ)).
    { intros a Ha Hn. rewrite dom_app in Hn. rewrite cols_l_app.
      assert (Hn1 : a `notin` cols_l ρn) by (clear - Hn Hdfl; fsetdec).
      assert (Hn2 : a `notin` cols_l ρ)
        by (apply (Hblk a); [ exact Ha | clear - Hn; fsetdec ]).
      clear - Hn1 Hn2. fsetdec. }
    assert (HdΘΞ : dom (Ξ2 ++ Θ0') [<=] S1e)
      by (rewrite dom_app; clear - HΞ2S1 HdΘ Hgre Hα'S0; fsetdec).
    assert (HcovΞ : V ∪ cols_r (ρn ++ ρ) [<=] S1e).
    { rewrite cols_r_app.
      clear - Hcov Hdfr HΞ2S1 Hgre Hα'S0. fsetdec. }
    assert (Hcov1 : ftvar_in_pskl (open_pskl_wrt_pskl Pb2 (pskl_var_f α'))
                    ∪ ftvar_in_pskl P0' [<=] S1e)
      by (clear - HcovP' Hgre; fsetdec).
    assert (HP1'S : ftvar_in_pskl P1' [<=] S1e).
    { pose proof (e_extract_out_ftvar De) as Hout.
      clear - Hout Hcov1. fsetdec. }
    assert (HPb2S : ftvar_in_pskl Pb2 [<=] S1e).
    { simpl in HcovP. clear - HcovP Hgre. fsetdec. }
    assert (HcovPΞ : ftvar_in_pskl P0'
                     ∪ ftvar_in_pskl (open_pskl_wrt_pskl Pb2 P1') [<=] S1e).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Pb2 P1') as Hup.
      clear - Hup HP1'S HPb2S Hcov1. fsetdec. }
    assert (Hwfp0Ξ : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a)
      by (eapply a_wf_pskl_weaken;
          [ intros x b Hbd; apply binds_app_3; exact Hbd | exact Hwfp0 ]).
    assert (HwfpΞ : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ
                       (open_pskl_wrt_pskl P P1) }}a).
    { inversion Hwfp; subst.
      match goal with
      | Hb : forall a, a `notin` ?L0 -> _ |- _ =>
          eapply a_wf_pskl_open with (L := L0); [ | exact Hwf1 ];
          intros a0 Ha0; eapply a_wf_pskl_weaken;
            [ intros x b Hbd; apply binds_app_1 in Hbd;
              destruct Hbd as [Hbd | Hbd];
              [ apply binds_app_2; exact Hbd
              | apply binds_app_3; apply binds_app_3; exact Hbd ]
            | apply Hb; exact Ha0 ]
      end. }
    destruct (IHs S1e (Ξ2 ++ Θ0') P0'
                (open_pskl_wrt_pskl Pb2 P1') (ρn ++ ρ) V
                HrΘΞ HrP0n HrOpen HagrΞ Hinjn Hfunn HwfΞ HuqΞ2' Hftv2'
                HscpΞ HblkIH HdΘΞ HcovΞ HcovPΞ Hwfp0Ξ HwfpΞ)
      as (S2 & ρe1 & Θ1' & Q' & D2e & HrΘ1 & Hagr1 & HrQ & Hext1 & Hdom1).

    (* ⛔⛔ OWED (2) — side 2's scoping premise for [e_sub__forall_l]. *)
    assert (Hwf2 : {{ (Ξ2 ++ Θ0') ⨟ empty ⊢ₚₛ P1' }}a).
    { eapply a_wf_pskl_rel;
        [ exact Hwf1 | exact HrΘΞ | exact Hfunn | clear; fsetdec
        | exact Hdrop ]. }

    (* ---- the answer ---- *)
    exists S2, (ρe1 ++ ρn), Θ1', Q'.
    split.
    { eapply e_sub__forall_l with (α := α').
      - exact Hne.
      - destruct Hg as [Hgd | ->];
          [ left; eapply rel_pskl_guarded; [ exact HrP0 | exact Hgd ]
          | inversion HrP0; subst; right; reflexivity ].
      - exact Hα'S0.
      - exact De.
      - exact Hwf2.
      - exact D2e. }
    rewrite app_assoc.
    split; [ exact HrΘ1 | ].
    split; [ exact Hagr1 | ].
    split; [ exact HrQ | ].
    assert (Hdm2 : dom (Ξ2 ++ Θ0') [<=] dom Θ1').
    { assert (HcovE : ftvar_in_aenv (Ξ2 ++ Θ0') ∪ ftvar_in_pskl P0'
                      ∪ ftvar_in_pskl (open_pskl_wrt_pskl Pb2 P1') [<=] S1e)
        by (clear - Hftv2' HcovPΞ; fsetdec).
      pose proof (e_sub_sound D2e HuqΞ2' HcovE) as Ha2.
      exact ((proj1 a_sub_sub_flex_dom_mono) _ _ _ _ _ _ _ Ha2). }
    split.
    { eapply rel_ext_app;
        [ exact Hextn | exact Hext1
        | rewrite ftvar_in_aenv_app; clear; fsetdec
        | clear - Hgre Hα'S0; fsetdec
        | intros a b Hin;
          assert (Hal : a `in` cols_l ρn) by (eapply cols_l_in; exact Hin);
          assert (Har : b `in` cols_r ρn) by (eapply cols_r_in; exact Hin);
          split;
            [ rewrite ftvar_in_aenv_app;
              pose proof (dom_subset_ftvar_in_aenv Ξ) as Hdsx;
              clear - Hal Hdfl Hdsx; fsetdec
            | clear - Har Hdfr HΞ2S1; fsetdec ] ]. }
    intros a b Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + destruct (Hdom1 _ _ Hin) as [Hd1 Hd2]. split; [ exact Hd1 | exact Hd2 ].
    + assert (Hal : a `in` cols_l ρn) by (eapply cols_l_in; exact Hin).
      assert (Har : b `in` cols_r ρn) by (eapply cols_r_in; exact Hin).
      split;
        [ clear - Hal Hdfl Hdm; fsetdec
        | clear - Har Hdfr Hdm2; rewrite dom_app in Hdm2; fsetdec ].
  - (* S-Ghost : output = the check-against, context unchanged *)
    intros M Θ0 P0 Hmg.
    intros S0 Θ0' P0' P' ρ V HrΘ HrP0 HrP Hagr Hinj Hfun Hwf Huq2p Hftv2
      Hscp Hblk HdΘ Hcov HcovP Hwfp0 Hwfp.
    inversion HrP as [ | n1 | u1 v1 Hu4 | D1 D2 D3 D4 Hu5 Hu6 | E1 E2 Hu7
                     | | F1 F2 Hu8 ]; subst.
    exists S0, (@nil (atom * atom)%type), Θ0', P0'.
    split; [ apply e_sub__ghost; exact Hmg | ]. simpl.
    split; [ exact HrΘ | ].
    split; [ exact Hagr | ].
    split; [ exact HrP0 | ].
    split.
    { unfold rel_ext. repeat split; intros; simpl in *; contradiction. }
    intros a b Hin. inversion Hin.
  - (* S-UnivGhostL : strip the subject's ⫯ *)
    intros M Θ0 Θ1 P0 P Q Hne Hs IHs.
    intros S0 Θ0' P0' P' ρ V HrΘ HrP0 HrP Hagr Hinj Hfun Hwf Huq2p Hftv2
      Hscp Hblk HdΘ Hcov HcovP Hwfp0 Hwfp.
    inversion HrP as [ | n1 | u1 v1 Hu4 | D1 D2 D3 D4 Hu5 Hu6 | E1 E2 Hu7
                     | | F1 P12 HrPb ]; subst.
    assert (HcovP1 : ftvar_in_pskl P0' ∪ ftvar_in_pskl P12 [<=] S0)
      by (simpl in HcovP; clear - HcovP; fsetdec).
    assert (Hwfp1 : {{ Θ0 ⨟ empty ⊢ₚₛ P }}a)
      by (inversion Hwfp; subst; rewrite aenv_minus_empty in *; assumption).
    destruct (IHs S0 Θ0' P0' P12 ρ V HrΘ HrP0 HrPb Hagr Hinj Hfun Hwf Huq2p
                Hftv2 Hscp Hblk HdΘ Hcov HcovP1 Hwfp0 Hwfp1)
      as (S1 & ρe & Θ1' & Q' & De & HrΘ1 & Hagr1 & HrQ & Hext & Hdom1).
    exists S1, ρe, Θ1', Q'.
    split; [ apply e_sub__univ_ghost_l; [ exact Hne | exact De ] | ].
    split; [ exact HrΘ1 | ].
    split; [ exact Hagr1 | ].
    split; [ exact HrQ | ].
    split; [ exact Hext | ]. exact Hdom1.
  - (* ⭐⭐ W-Solve — the walk's GENERATIVE row.  It invents two atoms fresh
       for the CONTEXT only, so (like the ∀ rows) ρ must be restricted at
       them first; then TWO pairs are pushed and the head gains a
       definition. *)
    intros NM M P0 Θ0 Θ1 Ξ α0 α β Q Hne Hαf Hβf Hprem IH.
    intros S0 Θ0' Ξ' α' P0' ρ V HrΘ HrΞ Hrα HrP0 Hagr Hinj Hfun Hwf Hdec
      Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP Hwfp0 Hbα.
    destruct (rel_aenv_cons_inv_l HrΘ)
      as (b0 & bd2 & Θ0'' & E0' & Hab0 & Hbd0 & Hrest).
    subst Θ0'. inversion Hbd0; subst.
    destruct (atom_fresh S0) as [a2 Ha2].
    destruct (atom_fresh (add a2 S0)) as [b2 Hb2].
    assert (Hα0d : α0 `in` dom (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0))
      by (repeat rewrite dom_app; simpl; clear; fsetdec).
    assert (Eα' : α' = b0) by (exact (Hfun α0 α' b0 Hα0d Hrα Hab0)).
    subst α'.
    assert (Hsc : ftvar_in_aenv (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0)
                  [<=] dom (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0))
      by (apply a_wf_aenv_ftv_dom; exact Hwf).
    assert (Hαnd : α `notin` dom (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0)).
    { repeat rewrite dom_app in Hαf |- *. simpl. clear - Hαf. fsetdec. }
    assert (Hβnd : β `notin` dom (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0)).
    { repeat rewrite dom_app in Hβf |- *. simpl. clear - Hβf. fsetdec. }
    (* ⭐ NO restriction is needed here, and that is the difference from
       [S-ForallR]: the two invented atoms SURVIVE into the output, so the
       motive's own block premise already puts them off ρ's left column. *)
    assert (Hdm : dom (Ξ ++ (α0 ~ abind_flex_mono_def
                              (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
                         ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono)
                         ++ Θ0) [<=] dom Θ1)
      by (exact ((proj1 a_sub_sub_flex_dom_mono) _ _ _ _ _ _ _ Hprem)).
    assert (HαΘ1 : α `in` dom Θ1)
      by (clear - Hdm; repeat rewrite dom_app in Hdm; simpl in Hdm; fsetdec).
    assert (HβΘ1 : β `in` dom Θ1)
      by (clear - Hdm; repeat rewrite dom_app in Hdm; simpl in Hdm; fsetdec).
    assert (Hαcl : α `notin` cols_l ρ)
      by (apply Hblk; [ exact HαΘ1 | exact Hαnd ]).
    assert (Hβcl : β `notin` cols_l ρ)
      by (apply Hblk; [ exact HβΘ1 | exact Hβnd ]).
    assert (Hρincl : forall a b, In (a, b) ρ -> In (a, b) ρ)
      by (intros a b Hin; exact Hin).
    assert (Hρin : forall a b, In (a, b) ρ -> In (a, b) ρ)
      by (intros a b Hin; exact Hin).
    assert (Hcl00 : cols_l ρ [<=] cols_l ρ)
      by (clear; fsetdec).
    assert (Hcr00 : cols_r ρ [<=] cols_r ρ)
      by (clear; fsetdec).
    assert (HrΘ00 : rel_aenv ρ V Θ0 Θ0'') by (exact Hrest).
    assert (HrΞ0 : rel_aenv ρ V Ξ Ξ') by (exact HrΞ).
    assert (HrP00 : rel_pskl ρ V P0 P0') by (exact HrP0).
    assert (Hrα0 : rel_atom ρ V α0 b0) by (exact Hab0).
    assert (Hagr0 : flex_agree_rel ρ V (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0)
                      (Ξ' ++ (b0 ~ abind_flex_mono) ++ Θ0''))
      by (exact Hagr).
    assert (Hinj0 : rel_inj ρ V) by (exact Hinj).
    assert (Hfun0 : rel_fun ρ V (dom (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0)))
      by (exact Hfun).
    assert (Hcov0 : V ∪ cols_r ρ [<=] S0) by (exact Hcov).
    assert (Hαcl0 : α `notin` cols_l ρ) by (exact Hαcl).
    assert (Hβcl0 : β `notin` cols_l ρ) by (exact Hβcl).
    (* ---- the two pairs, and the extended relation ---- *)
    assert (Ha2V : a2 `notin` V) by (clear - Ha2 Hcov; fsetdec).
    assert (Hb2V : b2 `notin` V) by (clear - Hb2 Hcov; fsetdec).
    assert (Ha2cr : a2 `notin` cols_r ρ) by (clear - Ha2 Hcov Hcr00; fsetdec).
    assert (Hb2cr : b2 `notin` cols_r ρ) by (clear - Hb2 Hcov Hcr00; fsetdec).
    assert (Hab2 : a2 <> b2) by (clear - Hb2; fsetdec).
    assert (HαV : α `notin` V)
      by (intros Hin; apply Hαnd; apply Hscp in Hin; clear - Hin Hsc; fsetdec).
    assert (HβV : β `notin` V)
      by (intros Hin; apply Hβnd; apply Hscp in Hin; clear - Hin Hsc; fsetdec).
    remember ((α, a2) :: (β, b2) :: ρ) as ρ1 eqn:Eρ1.
    assert (Hρ1incl : forall a b, In (a, b) ρ -> In (a, b) ρ1)
      by (subst ρ1; intros a b Hin; right; right; exact Hin).
    assert (Hinj1 : rel_inj ρ1 V).
    { subst ρ1. apply rel_inj_push;
        [ apply rel_inj_push; [ exact Hinj0 | exact Hb2V | exact Hb2cr ]
        | exact Ha2V | simpl; clear - Ha2cr Hab2; fsetdec ]. }
    assert (Hfun1 : rel_fun ρ1 V
              (dom (Ξ ++ (α0 ~ abind_flex_mono_def
                            (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
                      ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono)
                      ++ Θ0))).
    { subst ρ1. eapply rel_fun_weaken;
        [ apply rel_fun_push;
            [ apply rel_fun_push; [ exact Hfun0 | exact HβV | exact Hβcl0 ]
            | exact HαV | simpl; clear - Hαcl0 Hne; fsetdec ]
        | intros x y Hx; exact Hx
        | repeat rewrite dom_app; simpl; clear; fsetdec ]. }
    assert (HrΘ1 : rel_aenv ρ1 V
              (Ξ ++ (α0 ~ abind_flex_mono_def
                       (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
                 ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0)
              (Ξ' ++ (b0 ~ abind_flex_mono_def
                        (ptyp_arrow (ptyp_var_f a2) (ptyp_var_f b2)))
                  ++ (b2 ~ abind_flex_mono) ++ (a2 ~ abind_flex_mono)
                  ++ Θ0'')).
    { apply rel_aenv_app.
      - eapply rel_aenv_mono;
          [ exact HrΞ0 | exact Hρ1incl | intros x Hx; exact Hx ].
      - apply rel_aenv__cons.
        + eapply rel_atom_incl; [ exact Hrα0 | exact Hρ1incl ].
        + constructor. unfold rel_ptyp. simpl. constructor;
            apply rel_pskl__var_f; apply rel_atom__pair; subst ρ1;
            [ left; reflexivity | right; left; reflexivity ].
        + apply rel_aenv__cons;
            [ apply rel_atom__pair; subst ρ1; right; left; reflexivity
            | constructor | ].
          apply rel_aenv__cons;
            [ apply rel_atom__pair; subst ρ1; left; reflexivity
            | constructor | ].
          eapply rel_aenv_mono;
            [ exact HrΘ00 | exact Hρ1incl | intros x Hx; exact Hx ]. }
    assert (Hagr1 : flex_agree_rel ρ1 V
              (Ξ ++ (α0 ~ abind_flex_mono_def
                       (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
                 ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0)
              (Ξ' ++ (b0 ~ abind_flex_mono_def
                        (ptyp_arrow (ptyp_var_f a2) (ptyp_var_f b2)))
                  ++ (b2 ~ abind_flex_mono) ++ (a2 ~ abind_flex_mono)
                  ++ Θ0'')).
    { split.
      - intros x HxV.
        assert (Hxα : x <> α) by (intros ->; contradiction).
        assert (Hxβ : x <> β) by (intros ->; contradiction).
        assert (Hxa2 : x <> a2) by (intros ->; contradiction).
        assert (Hxb2 : x <> b2) by (intros ->; contradiction).
        rewrite (a_flex_tvar_solve_shape Ξ _ _ Θ0 Hxα Hxβ).
        rewrite (a_flex_tvar_solve_shape Ξ' _ _ Θ0'' Hxa2 Hxb2).
        exact (proj1 Hagr0 x HxV).
      - intros x y Hin. subst ρ1.
        destruct Hin as [E1 | [E2 | Hin]].
        + injection E1 as -> ->. split; intros _; left; unfold binds;
            apply in_or_app; right; right; right; left; reflexivity.
        + injection E2 as -> ->. split; intros _; left; unfold binds;
            apply in_or_app; right; right; left; reflexivity.
        + assert (Hxα : x <> α)
            by (intros ->; apply Hαcl0; eapply cols_l_in; exact Hin).
          assert (Hxβ : x <> β)
            by (intros ->; apply Hβcl0; eapply cols_l_in; exact Hin).
          assert (Hya2 : y <> a2)
            by (intros ->; apply Ha2cr; eapply cols_r_in; exact Hin).
          assert (Hyb2 : y <> b2)
            by (intros ->; apply Hb2cr; eapply cols_r_in; exact Hin).
          rewrite (a_flex_tvar_solve_shape Ξ _ _ Θ0 Hxα Hxβ).
          rewrite (a_flex_tvar_solve_shape Ξ' _ _ Θ0'' Hya2 Hyb2).
          exact (proj2 Hagr0 x y Hin). }
    (* ---- the premise's wf package ---- *)
    assert (Huq1 : uniq (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Hwf0 : {{ ⊢ Θ0 }}a).
    { eapply a_wf_aenv_strip_prefix with (Ξ := Ξ ++ (α0 ~ abind_flex_mono)).
      simpl_env. exact Hwf. }
    assert (Hwfmid : {{ ⊢ ((β ~ abind_flex_mono) ++ (α ~ abind_flex_mono)
                           ++ Θ0) }}a).
    { apply a_wf_aenv__flex;
        [ simpl; clear - Hβf Hne; simpl_env in *; fsetdec | ].
      apply a_wf_aenv__flex;
        [ clear - Hαf; simpl_env in *; fsetdec | exact Hwf0 ]. }
    assert (HbαM : binds α abind_flex_mono
                    ((β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0))
      by (unfold binds; simpl; right; left; reflexivity).
    assert (HbβM : binds β abind_flex_mono
                    ((β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0))
      by (unfold binds; simpl; left; reflexivity).
    assert (Hwfdef : {{ ⊢ ((α0 ~ abind_flex_mono_def
                              (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
                           ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono)
                           ++ Θ0) }}a).
    { apply a_wf_aenv__flex_def.
      - simpl. clear - Hαf Hβf Huq1. simpl_env in *. solve_uniq.
      - apply a_wf_ptyp__arrow; apply a_wf_ptyp__var;
          [ right; left; exact HbαM | right; left; exact HbβM ].
      - repeat constructor.
      - exact Hwfmid. }
    assert (HwfBig : {{ ⊢ (Ξ ++ (α0 ~ abind_flex_mono_def
                (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
           ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0) }}a).
    { apply a_wf_aenv_prepend_decls;
        [ exact Hdec | clear - Huq1; solve_uniq | | exact Hwfdef ].
      intros γ Hγ. simpl_env. clear - Huq1 Hαf Hβf Hγ. destruct_uniq.
      unfold disjoint in *. simpl_env in *. fsetdec. }
    assert (Hbigmon : forall γ, a_binds_tvar γ (Ξ ++ (α0 ~ abind_flex_mono)
                                                  ++ Θ0) ->
              a_binds_tvar γ (Ξ ++ (α0 ~ abind_flex_mono_def
                (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
           ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0)).
    { intros γ [Hb | [Hb | [t Hb]]]; unfold binds in Hb;
        apply in_app_or in Hb; destruct Hb as [Hb | Hb];
        try (simpl in Hb; destruct Hb as [E | Hb]; [ inversion E; subst | ]);
        solve [ left; unfold binds; apply in_or_app; left; exact Hb
              | right; left; unfold binds; apply in_or_app; left; exact Hb
              | right; right; exists t; unfold binds; apply in_or_app; left;
                exact Hb
              | right; right;
                exists (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β));
                unfold binds; apply in_or_app; right; left; reflexivity
              | left; unfold binds; apply in_or_app; right;
                simpl; right; right; right; exact Hb
              | right; left; unfold binds; apply in_or_app; right;
                simpl; right; right; right; exact Hb
              | right; right; exists t; unfold binds; apply in_or_app; right;
                simpl; right; right; right; exact Hb ]. }
    assert (Hwfp01 : {{ (Ξ ++ (α0 ~ abind_flex_mono_def
                (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
           ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a)
      by (eapply a_wf_pskl_tvar_mono; [ exact Hwfp0 | exact Hbigmon ]).
    assert (Hwfp11 : {{ (Ξ ++ (α0 ~ abind_flex_mono_def
                (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
           ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0) ⨟ empty ⊢ₚₛ
                       (pskl_arrow (pskl_var_f α) (pskl_var_f β)) }}a).
    { apply a_wf_pskl__arrow; apply a_wf_pskl__var;
        [ right; left | right; left ]; unfold binds; apply in_or_app; right;
        simpl; [ right; right; left; reflexivity
               | right; left; reflexivity ]. }
    (* ---- side 2's package at the extended context ---- *)
    assert (Ha2d : a2 `notin` dom (Ξ' ++ (b0 ~ abind_flex_mono) ++ Θ0''))
      by (clear - Ha2 HdΘ; fsetdec).
    assert (Hb2d : b2 `notin` dom (Ξ' ++ (b0 ~ abind_flex_mono) ++ Θ0''))
      by (clear - Hb2 HdΘ; fsetdec).
    assert (Huq21 : uniq (Ξ' ++ (b0 ~ abind_flex_mono_def
                 (ptyp_arrow (ptyp_var_f a2) (ptyp_var_f b2)))
            ++ (b2 ~ abind_flex_mono) ++ (a2 ~ abind_flex_mono)
            ++ Θ0'')).
    { assert (Hbase : uniq ((Ξ' ++ (b0 ~ abind_flex_mono_def
                               (ptyp_arrow (ptyp_var_f a2) (ptyp_var_f b2))))
                            ++ Θ0''))
        by (clear - Huq2p; simpl_env in *; solve_uniq).
      assert (Hstep1 : uniq ((Ξ' ++ (b0 ~ abind_flex_mono_def
                                (ptyp_arrow (ptyp_var_f a2) (ptyp_var_f b2))))
                             ++ (a2 ~ abind_flex_mono) ++ Θ0'')).
      { apply uniq_insert_mid;
          [ exact Hbase
          | simpl_env in Ha2d; simpl_env; clear - Ha2d; fsetdec
          | simpl_env in Ha2d; clear - Ha2d; fsetdec ]. }
      assert (Hstep2 : uniq ((Ξ' ++ (b0 ~ abind_flex_mono_def
                                (ptyp_arrow (ptyp_var_f a2) (ptyp_var_f b2))))
                             ++ (b2 ~ abind_flex_mono)
                             ++ (a2 ~ abind_flex_mono) ++ Θ0'')).
      { apply uniq_insert_mid;
          [ exact Hstep1
          | simpl_env in Hb2d; simpl_env; clear - Hb2d; fsetdec
          | simpl_env in Hb2d; simpl_env; clear - Hb2d Hab2; fsetdec ]. }
      simpl_env in Hstep2. simpl_env. exact Hstep2. }
    assert (Hftv21 : ftvar_in_aenv (Ξ' ++ (b0 ~ abind_flex_mono_def
                 (ptyp_arrow (ptyp_var_f a2) (ptyp_var_f b2)))
            ++ (b2 ~ abind_flex_mono) ++ (a2 ~ abind_flex_mono)
            ++ Θ0'') [<=] add b2 (add a2 S0)).
    { repeat rewrite ftvar_in_aenv_app in Hftv2 |- *.
      simpl ftvar_in_aenv in Hftv2 |- *. simpl ftvar_in_abind in *.
      clear - Hftv2. fsetdec. }
    assert (Hscp1 : V [<=] ftvar_in_aenv (Ξ ++ (α0 ~ abind_flex_mono_def
                (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
           ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0)).
    { repeat rewrite ftvar_in_aenv_app in Hscp |- *.
      simpl ftvar_in_aenv in Hscp |- *. simpl ftvar_in_abind in *.
      clear - Hscp. fsetdec. }
    assert (Hblk1 : forall a, a `in` dom Θ1 -> a `notin` dom (Ξ ++ (α0 ~ abind_flex_mono_def
                (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
           ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0) ->
              a `notin` cols_l ρ1).
    { intros a Ha Hn. subst ρ1. simpl.
      repeat rewrite dom_app in Hn. simpl in Hn.
      assert (Hnα : a <> α) by (clear - Hn; fsetdec).
      assert (Hnβ : a <> β) by (clear - Hn; fsetdec).
      assert (Hc : a `notin` cols_l ρ).
      { apply Hblk; [ exact Ha | ].
        repeat rewrite dom_app. simpl. clear - Hn. fsetdec. }
      clear - Hc Hnα Hnβ Hcl00. fsetdec. }
    assert (HdΘ1 : dom (Ξ' ++ (b0 ~ abind_flex_mono_def
                 (ptyp_arrow (ptyp_var_f a2) (ptyp_var_f b2)))
            ++ (b2 ~ abind_flex_mono) ++ (a2 ~ abind_flex_mono)
            ++ Θ0'') [<=] add b2 (add a2 S0)).
    { repeat rewrite dom_app in HdΘ |- *. simpl in HdΘ |- *.
      clear - HdΘ. fsetdec. }
    assert (Hcov1 : V ∪ cols_r ρ1 [<=] add b2 (add a2 S0)).
    { subst ρ1. simpl. clear - Hcov. fsetdec. }
    assert (HcovP1 : ftvar_in_pskl P0'
                     ∪ ftvar_in_pskl (pskl_arrow (pskl_var_f a2)
                                                 (pskl_var_f b2))
                     [<=] add b2 (add a2 S0))
      by (simpl; clear - HcovP; fsetdec).
    destruct (IH (add b2 (add a2 S0)) (Ξ' ++ (b0 ~ abind_flex_mono_def
                 (ptyp_arrow (ptyp_var_f a2) (ptyp_var_f b2)))
            ++ (b2 ~ abind_flex_mono) ++ (a2 ~ abind_flex_mono)
            ++ Θ0'') P0'
                (pskl_arrow (pskl_var_f a2) (pskl_var_f b2)) ρ1 V
                HrΘ1 (ltac:(subst ρ1; eapply rel_pskl_mono;
                            [ exact HrP00 | intros x y Hx; right; right;
                              exact Hx | intros x Hx; exact Hx ]))
                (ltac:(subst ρ1; constructor; apply rel_pskl__var_f;
                       apply rel_atom__pair;
                       [ left; reflexivity | right; left; reflexivity ]))
                Hagr1 Hinj1 Hfun1 HwfBig Huq21 Hftv21 Hscp1 Hblk1 HdΘ1
                Hcov1 HcovP1 Hwfp01 Hwfp11)
      as (S1 & ρe & Θ1' & Q' & De & HrΘout & Hagrout & HrQ & Hext & Hdomout).
    assert (HcovE : ftvar_in_aenv (Ξ' ++ (b0 ~ abind_flex_mono_def
                 (ptyp_arrow (ptyp_var_f a2) (ptyp_var_f b2)))
            ++ (b2 ~ abind_flex_mono) ++ (a2 ~ abind_flex_mono)
            ++ Θ0'') ∪ ftvar_in_pskl P0'
                    ∪ ftvar_in_pskl (pskl_arrow (pskl_var_f a2)
                                                (pskl_var_f b2))
                    [<=] add b2 (add a2 S0))
      by (repeat apply AtomSetProperties.union_subset_3;
          solve [ exact Hftv21 | clear - HcovP1; fsetdec ]).
    pose proof (e_sub_sound De Huq21 HcovE) as HaD.
    assert (Hdm2 : dom (Ξ' ++ (b0 ~ abind_flex_mono_def
                 (ptyp_arrow (ptyp_var_f a2) (ptyp_var_f b2)))
            ++ (b2 ~ abind_flex_mono) ++ (a2 ~ abind_flex_mono)
            ++ Θ0'') [<=] dom Θ1')
      by (exact ((proj1 a_sub_sub_flex_dom_mono) _ _ _ _ _ _ _ HaD)).
    assert (Ha2Θ1 : a2 `in` dom Θ1')
      by (clear - Hdm2; simpl_env in Hdm2; fsetdec).
    assert (Hb2Θ1 : b2 `in` dom Θ1')
      by (clear - Hdm2; simpl_env in Hdm2; fsetdec).
    assert (HsubW : ftvar_in_aenv (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0)
                    [<=] ftvar_in_aenv (Ξ ++ (α0 ~ abind_flex_mono_def
                (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
           ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0)).
    { repeat rewrite ftvar_in_aenv_app.
      simpl ftvar_in_aenv. simpl ftvar_in_abind. clear; fsetdec. }
    assert (Hαft : α `notin` ftvar_in_aenv
                     (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0))
      by (clear - Hαnd Hsc; fsetdec).
    assert (Hβft : β `notin` ftvar_in_aenv
                     (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0))
      by (clear - Hβnd Hsc; fsetdec).
    assert (Hαin : α `in` ftvar_in_aenv (Ξ ++ (α0 ~ abind_flex_mono_def
                (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
           ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0)).
    { repeat rewrite ftvar_in_aenv_app.
      simpl ftvar_in_aenv. simpl ftvar_in_abind. clear; fsetdec. }
    assert (Hβin : β `in` ftvar_in_aenv (Ξ ++ (α0 ~ abind_flex_mono_def
                (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
           ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0)).
    { repeat rewrite ftvar_in_aenv_app.
      simpl ftvar_in_aenv. simpl ftvar_in_abind. clear; fsetdec. }
    assert (Hnew : rel_ext ((α, a2) :: (β, b2) :: nil)
                     (ftvar_in_aenv (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0)) S0).
    { unfold rel_ext. split; [ | split ].
      - intros a b Hin. destruct Hin as [E1 | [E2 | []]];
          [ inversion E1 | inversion E2 ]; subst;
          split; solve [ exact Hαft | exact Hβft | exact Ha2
                       | clear - Hb2; fsetdec ].
      - intros a1 a3 b H1 H2.
        destruct H1 as [E1 | [E1 | []]]; destruct H2 as [E2 | [E2 | []]];
          inversion E1; inversion E2; subst; try reflexivity;
          exfalso; clear - Hb2; fsetdec.
      - intros a b1 b3 H1 H2.
        destruct H1 as [E1 | [E1 | []]]; destruct H2 as [E2 | [E2 | []]];
          inversion E1; inversion E2; subst; try reflexivity;
          exfalso; apply Hne; reflexivity. }
    (* ---- assemble: the row's TWO pairs join what the premise invented ---- *)
    exists S1, (ρe ++ ((α, a2) :: (β, b2) :: nil)), Θ1', Q'.
    split; [ apply e_sub_flex__solve with (α := a2) (β := b2);
             [ exact Ha2 | exact Hb2 | exact De ] | ].
    rewrite app_assoc. simpl. subst ρ1.
    split; [ exact HrΘout | ].
    split; [ exact Hagrout | ].
    split; [ exact HrQ | ].
    split.
    { eapply rel_ext_app;
        [ exact Hnew | exact Hext | exact HsubW | clear; fsetdec | ].
      intros a b Hin. destruct Hin as [E1 | [E2 | []]];
        [ inversion E1 | inversion E2 ]; subst;
        split; solve [ exact Hαin | exact Hβin | clear; fsetdec ]. }
    intros a b Hin. apply in_app_or in Hin.
    destruct Hin as [Hin | [E1 | [E2 | []]]].
    + exact (Hdomout _ _ Hin).
    + inversion E1; subst. split; [ exact HαΘ1 | exact Ha2Θ1 ].
    + inversion E2; subst. split; [ exact HβΘ1 | exact Hb2Θ1 ].
  - (* ⭐ W-Assign — the walk's only DESCENT, and its premise runs at
       SUBSTITUTED skeletons.  ⚙ Simpler than the consis [Assign-Assign] it
       is templated on: [e_sub_flex__assign] carries NO side condition, so
       none of that row's [a_flex_tvar] plumbing for the subject is needed. *)
    intros NM M P0 Θ0 Θ1 Ξ α β τ Q Hβd Hprem IH.
    intros S0 Θ0' Ξ' α' P0' ρ V HrΘ HrΞ Hrα HrP0 Hagr Hinj Hfun Hwf Hdec
      Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP Hwfp0 HbαM.
    destruct (rel_aenv_cons_inv_l HrΘ)
      as (b & bdd & Θ0'' & E0' & Hab & Hbd & Hrest).
    subst Θ0'.
    inversion Hbd as [ | | t1 t2 Hrτ | A1 A2 HrA | Q1 Q2 HrQ0 ]; subst.
    assert (Huq1 : uniq (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Huq2 : uniq (Ξ' ++ (b ~ abind_flex_mono_def t2) ++ Θ0''))
      by (exact Huq2p).
    assert (HwfC : {{ ⊢ (Ξ ++ Θ0) }}a)
      by (eapply a_wf_aenv_strip_mid; [ exact Hdec | exact Hwf ]).
    assert (Huq2C : uniq (Ξ' ++ Θ0'')) by (clear - Huq2p; solve_uniq).
    assert (Hftv2C : ftvar_in_aenv (Ξ' ++ Θ0'') [<=] S0).
    { repeat rewrite ftvar_in_aenv_app in Hftv2 |- *. simpl in Hftv2.
      clear - Hftv2. fsetdec. }
    assert (Hτdom : ftvar_in_ptyp τ [<=] dom Θ0)
      by (apply a_wf_ptyp_ftv_dom;
          exact (proj1 (@a_wf_aenv_mid_def_inv Ξ β τ Θ0 Hdec Hwf))).
    assert (Hτ2dom : ftvar_in_ptyp t2 [<=] S0).
    { repeat rewrite ftvar_in_aenv_app in Hftv2. simpl in Hftv2.
      clear - Hftv2. fsetdec. }
    assert (Hsc : ftvar_in_aenv (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0)
                  [<=] dom (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
      by (apply a_wf_aenv_ftv_dom; exact Hwf).
    assert (HVdom : V [<=] dom (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
      by (clear - Hscp Hsc; fsetdec).
    assert (Hβnd : β `notin` dom (Ξ ++ Θ0)).
    { clear - Huq1. repeat rewrite dom_app in *. simpl in *.
      destruct_uniq. fsetdec. }
    assert (Hbnd : b `notin` dom (Ξ' ++ Θ0'')).
    { clear - Huq2. repeat rewrite dom_app in *. simpl in *.
      destruct_uniq. fsetdec. }
    assert (HscC : ftvar_in_aenv (Ξ ++ Θ0) [<=] dom (Ξ ++ Θ0))
      by (apply a_wf_aenv_ftv_dom; exact HwfC).
    assert (Hβd0 : β `in` dom (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
      by (repeat rewrite dom_app; simpl; clear; fsetdec).
    assert (Hβfun : forall y, rel_atom ρ V β y -> y = b)
      by (intros y Hy; exact (Hfun β y b Hβd0 Hy Hab)).
    remember (V ∩ ftvar_in_aenv (Ξ ++ Θ0)) as VC eqn:EVC.
    assert (HVC : VC [<=] V) by (subst VC; clear; fsetdec).
    assert (HVCsplit : forall x, x `in` V -> x <> β -> x `in` VC).
    { intros x Hx Hne. subst VC.
      pose proof (dom_subset_ftvar_in_aenv (Ξ ++ Θ0)) as Hds.
      assert (Hxd : x `in` dom (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
        by (clear - Hx HVdom; fsetdec).
      repeat rewrite dom_app in Hxd. simpl in Hxd.
      repeat rewrite dom_app in Hds.
      clear - Hx Hne Hxd Hds. fsetdec. }
    assert (HVCne : forall x, x `in` VC -> x <> β).
    { intros x Hx Ex. rewrite Ex in Hx.
      assert (Hin : β `in` ftvar_in_aenv (Ξ ++ Θ0))
        by (subst VC; clear - Hx; fsetdec).
      clear - Hin HscC Hβnd. fsetdec. }
    assert (HrΘC : rel_aenv ρ VC (Ξ ++ Θ0) (Ξ' ++ Θ0'')).
    { eapply rel_aenv_shrink_V; [ apply rel_aenv_app; eassumption | ].
      intros x Hx Hf. apply HVCsplit; [ exact Hx | ].
      intros Ex. rewrite Ex in Hf.
      pose proof (dom_subset_ftvar_in_aenv (Ξ ++ Θ0)) as Hds.
      clear - Hf Hds HscC Hβnd. fsetdec. }
    assert (HrPsub : rel_pskl ρ V (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0)
                       (subst_pskl_in_pskl (ptyp_to_pskl t2) b P0'))
      by (apply rel_pskl_subst;
          [ exact HrP0 | exact Hrτ | exact Hab | exact Hinj | exact Hβfun ]).
    assert (HrVsub : rel_pskl ρ V
                       (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α))
                       (subst_pskl_in_pskl (ptyp_to_pskl t2) b (pskl_var_f α')))
      by (apply rel_pskl_subst;
          [ constructor; exact Hrα | exact Hrτ | exact Hab | exact Hinj
          | exact Hβfun ]).
    assert (Hshr : forall (R : pskl) x, x `in` V ->
              x `in` ftvar_in_pskl (subst_pskl_in_pskl (ptyp_to_pskl τ) β R) ->
              x `in` VC).
    { intros R x Hx Hin.
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper R (ptyp_to_pskl τ) β)
        as Hu.
      rewrite ftvar_ptyp_to_pskl in Hu.
      destruct (AtomSetProperties.In_dec x (ftvar_in_ptyp τ)) as [Hxτ | Hxτ].
      - subst VC.
        pose proof (dom_subset_ftvar_in_aenv (Ξ ++ Θ0)) as Hds.
        repeat rewrite dom_app in Hds.
        clear - Hx Hxτ Hτdom Hds. fsetdec.
      - apply HVCsplit; [ exact Hx | ].
        intros Ex. rewrite Ex in Hin. clear - Hin Hu Hxτ Ex. fsetdec. }
    assert (HrPsubC : rel_pskl ρ VC (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0)
                        (subst_pskl_in_pskl (ptyp_to_pskl t2) b P0'))
      by (eapply rel_pskl_shrink_V;
          [ exact HrPsub | intros x Hx Hf; exact (Hshr P0 x Hx Hf) ]).
    assert (HrVsubC : rel_pskl ρ VC
                        (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α))
                        (subst_pskl_in_pskl (ptyp_to_pskl t2) b (pskl_var_f α')))
      by (eapply rel_pskl_shrink_V;
          [ exact HrVsub
          | intros x Hx Hf; exact (Hshr (pskl_var_f α) x Hx Hf) ]).
    assert (HagrC : flex_agree_rel ρ VC (Ξ ++ Θ0) (Ξ' ++ Θ0''))
      by (eapply flex_agree_peel;
          [ exact Hagr | exact Hab | exact Hinj | exact Hβfun | exact Hβnd
          | exact Hbnd | exact HVC | exact HVCne ]).
    assert (HinjC : rel_inj ρ VC)
      by (eapply rel_inj_weaken_V; [ exact Hinj | exact HVC ]).
    assert (HfunC : rel_fun ρ VC (dom (Ξ ++ Θ0))).
    { eapply rel_fun_weaken;
        [ eapply rel_fun_weaken_V; [ exact Hfun | exact HVC ]
        | intros x y Hx; exact Hx
        | repeat rewrite dom_app; simpl; clear; fsetdec ]. }
    assert (HblkC : forall a0, a0 `in` dom Θ1 -> a0 `notin` dom (Ξ ++ Θ0) ->
                    a0 `notin` cols_l ρ).
    { intros a0 Ha0 Hn0. apply Hblk.
      - simpl. clear - Ha0. fsetdec.
      - assert (Hne : a0 <> β) by (intros Ex; rewrite Ex in Ha0; contradiction).
        repeat rewrite dom_app in Hn0 |- *. simpl. clear - Hn0 Hne. fsetdec. }
    assert (HdΘC : dom (Ξ' ++ Θ0'') [<=] S0)
      by (repeat rewrite dom_app in HdΘ |- *; simpl in HdΘ;
          clear - HdΘ; fsetdec).
    assert (HcovC : VC ∪ cols_r ρ [<=] S0) by (clear - Hcov HVC; fsetdec).
    assert (Hα'd : ftvar_in_pskl (pskl_var_f α') [<=] S0).
    { simpl. pose proof (rel_atom_r_in Hrα) as Hin.
      clear - Hin Hcov. fsetdec. }
    assert (HcovS : ftvar_in_pskl (subst_pskl_in_pskl (ptyp_to_pskl t2) b P0')
                    ∪ ftvar_in_pskl
                        (subst_pskl_in_pskl (ptyp_to_pskl t2) b
                           (pskl_var_f α')) [<=] S0).
    { pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P0' (ptyp_to_pskl t2) b)
        as Hu1.
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper (pskl_var_f α')
                    (ptyp_to_pskl t2) b) as Hu2.
      rewrite ftvar_ptyp_to_pskl in Hu1, Hu2.
      clear - Hu1 Hu2 HcovP Hτ2dom Hα'd. fsetdec. }
    (* ---- the wf package the a_sub premise wants ---- *)
    assert (HbβM : binds β (abind_flex_mono_def τ)
                    (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
      by (unfold binds; apply in_or_app; right; simpl; left; reflexivity).
    assert (Hτmono : mono_ptyp τ)
      by (exact (@a_wf_aenv_binds_def_mono _ β τ Hwf HbβM)).
    assert (Hβτ : β `notin` ftvar_in_ptyp τ).
    { repeat rewrite dom_app in Hβnd. clear - Hτdom Hβnd. fsetdec. }
    assert (HwfPsub : {{ (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0) ⨟ empty ⊢ₚₛ
                        (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0) }}a)
      by (apply a_wf_pskl_mono_subst;
          [ exact Hwfp0 | exact Hwf | exact HbβM | exact Hτmono ]).
    assert (HwfVsub : {{ (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0) ⨟ empty ⊢ₚₛ
                        (subst_pskl_in_pskl (ptyp_to_pskl τ) β
                           (pskl_var_f α)) }}a).
    { apply a_wf_pskl_mono_subst;
        [ | exact Hwf | exact HbβM | exact Hτmono ].
      apply a_wf_pskl__var. exact HbαM. }
    assert (Hstrip : forall R,
              β `notin` ftvar_in_pskl (subst_pskl_in_pskl (ptyp_to_pskl τ) β R)).
    { intros R.
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper R (ptyp_to_pskl τ) β)
        as Hu.
      rewrite ftvar_ptyp_to_pskl in Hu. clear - Hu Hβτ. fsetdec. }
    assert (HwfPsubC : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ
                         (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0) }}a)
      by (eapply a_wf_pskl_strip_mid; [ exact HwfPsub | exact (Hstrip P0) ]).
    assert (HwfVsubC : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ
                         (subst_pskl_in_pskl (ptyp_to_pskl τ) β
                            (pskl_var_f α)) }}a)
      by (eapply a_wf_pskl_strip_mid;
          [ exact HwfVsub | exact (Hstrip (pskl_var_f α)) ]).
    assert (HscpC : VC [<=] ftvar_in_aenv (Ξ ++ Θ0))
      by (subst VC; clear; fsetdec).
    destruct (IH S0 (Ξ' ++ Θ0'')
                (subst_pskl_in_pskl (ptyp_to_pskl t2) b P0')
                (subst_pskl_in_pskl (ptyp_to_pskl t2) b (pskl_var_f α'))
                ρ VC HrΘC HrPsubC HrVsubC HagrC HinjC HfunC HwfC Huq2C
                Hftv2C HscpC HblkC HdΘC HcovC HcovS HwfPsubC HwfVsubC)
      as (S1 & ρe & Θ1' & Q' & D2 & HrΘ1 & Hagr1 & HrQ & Hext1 & Hdom1).
    exists S1, ρe, ((b ~ abind_flex_mono_def t2) ++ Θ1'), Q'.
    split; [ apply e_sub_flex__assign with (τ := t2); exact D2 | ].
    split.
    { apply rel_aenv__cons.
      - eapply rel_atom_incl; [ exact Hab | ].
        intros x y Hx. apply in_or_app. right. exact Hx.
      - constructor. unfold rel_ptyp in Hrτ |- *.
        eapply rel_pskl_mono;
          [ exact Hrτ | intros x y Hx; apply in_or_app; right; exact Hx
          | intros x Hx; exact Hx ].
      - eapply rel_aenv_mono;
          [ exact HrΘ1 | intros x y Hx; exact Hx | exact HVC ]. }
    assert (Hinj' : rel_inj (ρe ++ ρ) V)
      by (eapply rel_inj_app; [ exact Hinj | exact Hext1 | exact Hcov ]).
    assert (Hab' : rel_atom (ρe ++ ρ) V β b)
      by (eapply rel_atom_incl;
          [ exact Hab | intros x y Hx; apply in_or_app; right; exact Hx ]).
    assert (Hβfun' : forall y, rel_atom (ρe ++ ρ) V β y -> y = b).
    { intros y Hy. destruct (rel_atom_app_inv ρe ρ Hy) as [Hin0 | Hat0].
      - exfalso. destruct (Hdom1 _ _ Hin0) as [Hd1 _]. contradiction.
      - exact (Hβfun y Hat0). }
    split.
    { eapply flex_agree_reattach;
        [ exact Hagr1 | exact Hab' | exact Hinj' | exact Hβfun'
        | exact HVCsplit
        | intros HβV; symmetry; apply Hβfun; apply rel_atom__id; exact HβV
        | split; intros _; right; eexists; unfold binds; simpl;
          left; reflexivity ]. }
    split.
    { eapply rel_pskl_mono;
        [ exact HrQ | intros x y Hx; exact Hx | exact HVC ]. }
    assert (Hftsub : ftvar_in_aenv (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0)
                     [<=] add β (ftvar_in_aenv (Ξ ++ Θ0))).
    { repeat rewrite ftvar_in_aenv_app. simpl.
      pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
      clear - Hτdom Hds. fsetdec. }
    split.
    { destruct Hext1 as [Hfr1 [Hri1 Hlf1]]. unfold rel_ext.
      split; [ | split; [ exact Hri1 | exact Hlf1 ] ].
      intros a0 b0 Hin. destruct (Hfr1 _ _ Hin) as [Ha0 Hb0].
      split; [ | exact Hb0 ].
      destruct (Hdom1 _ _ Hin) as [Hd1 _].
      assert (Hne : a0 <> β) by (intros Ex; rewrite Ex in Hd1; contradiction).
      clear - Ha0 Hne Hftsub. fsetdec. }
    intros a0 b0 Hin. destruct (Hdom1 _ _ Hin) as [Hd1 Hd2].
    split; [ clear - Hd1; simpl_env; fsetdec
           | clear - Hd2; simpl_env; fsetdec ].
  - (* W-Depend : the entry MOVES into the pending suffix *)
    intros NM M P0 Θ0 Θ1 Ξ α β Q Hne Hbin Hprem IH.
    intros S0 Θ0' Ξ' α' P0' ρ V HrΘ HrΞ Hrα HrP0 Hagr Hinj Hfun Hwf Hdec
      Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP Hwfp0 HbαM.
    destruct (rel_aenv_cons_inv_l HrΘ)
      as (b & bdd & Θ0'' & E0' & Hab & Hbd & Hrest).
    subst Θ0'. inversion Hbd; subst.
    assert (Hne2 : α' <> b).
    { intros Ex. apply Hne. rewrite Ex in Hrα. exact (Hinj α β b Hrα Hab). }
    assert (Hβd0 : β `in` dom (Ξ ++ (β ~ abind_flex_mono) ++ Θ0))
      by (repeat rewrite dom_app; simpl; clear; fsetdec).
    assert (HbinP : b `in` ftvar_in_pskl P0').
    { destruct (rel_pskl_ftv_corr_l HrP0 Hbin) as (y & Hy & Hat).
      assert (Ey : y = b) by (exact (Hfun β y b Hβd0 Hat Hab)).
      rewrite <- Ey. exact Hy. }
    assert (HrΞ' : rel_aenv ρ V (Ξ ++ (β ~ abind_flex_mono))
                     (Ξ' ++ (b ~ abind_flex_mono))).
    { apply rel_aenv_app; [ exact HrΞ | ].
      apply rel_aenv__cons; [ exact Hab | constructor | constructor ]. }
    assert (Hagr' : flex_agree_rel ρ V ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0)
                      ((Ξ' ++ (b ~ abind_flex_mono)) ++ Θ0''))
      by (simpl_env; exact Hagr).
    assert (Hfun' : rel_fun ρ V (dom ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0)))
      by (simpl_env; exact Hfun).
    assert (HbαM' : a_binds_tvar α ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0))
      by (simpl_env; exact HbαM).
    assert (Hwf' : {{ ⊢ ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0) }}a)
      by (simpl_env; exact Hwf).
    assert (Huq2' : uniq ((Ξ' ++ (b ~ abind_flex_mono)) ++ Θ0''))
      by (simpl_env; exact Huq2p).
    assert (Hftv2' : ftvar_in_aenv ((Ξ' ++ (b ~ abind_flex_mono)) ++ Θ0'')
                     [<=] S0)
      by (simpl_env; exact Hftv2).
    assert (Hdec' : a_decls (Ξ ++ (β ~ abind_flex_mono)))
      by (apply a_decls_app; [ exact Hdec | apply a_decls_one ]).
    assert (Hdec2' : a_decls (Ξ' ++ (b ~ abind_flex_mono)))
      by (apply a_decls_app; [ exact Hdec2 | apply a_decls_one ]).
    assert (Hscp' : V [<=] ftvar_in_aenv ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0))
      by (simpl_env; exact Hscp).
    assert (Hblk' : forall a0, a0 `in` dom Θ1 ->
              a0 `notin` dom ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0) ->
              a0 `notin` cols_l ρ)
      by (intros a0 Ha0 Hn0; apply Hblk;
          [ exact Ha0
          | repeat rewrite dom_app in Hn0 |- *; simpl in Hn0 |- *;
            clear - Hn0; fsetdec ]).
    assert (HdΘ' : dom ((Ξ' ++ (b ~ abind_flex_mono)) ++ Θ0'') [<=] S0).
    { repeat rewrite dom_app in HdΘ |- *. simpl in HdΘ |- *.
      clear - HdΘ. fsetdec. }
    assert (Hwfp0' : {{ ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0) ⨟ empty
                       ⊢ₚₛ P0 }}a)
      by (simpl_env; exact Hwfp0).
    destruct (IH S0 Θ0'' (Ξ' ++ (b ~ abind_flex_mono)) α' P0' ρ V
                Hrest HrΞ' Hrα HrP0 Hagr' Hinj Hfun' Hwf' Hdec' Hdec2'
                Huq2' Hftv2' Hscp' Hblk' HdΘ' Hcov HcovP Hwfp0' HbαM')
      as (S1 & ρe & Θ1' & Q' & De & HrΘ1 & Hagr1 & HrQ & Hext1 & Hdom1).
    exists S1, ρe, Θ1', Q'.
    split; [ apply e_sub_flex__depend;
             [ exact Hne2 | exact HbinP | exact De ] | ].
    split; [ exact HrΘ1 | ].
    split; [ exact Hagr1 | ].
    split; [ exact HrQ | ].
    split; [ simpl_env in Hext1; simpl_env; exact Hext1 | exact Hdom1 ].
  - (* W-Skip : flexible head, stepped over and re-attached *)
    intros NM M P0 Θ0 Θ1 Ξ α β Q Hne Hni Hβ1 Hprem IH.
    intros S0 Θ0' Ξ' α' P0' ρ V HrΘ HrΞ Hrα HrP0 Hagr Hinj Hfun Hwf Hdec
      Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP Hwfp0 HbαM.
    destruct (lift_sub_flex_peel IH Hne Hni Hβ1 HrΘ HrΞ Hrα HrP0 Hagr Hinj
                Hfun Hwf Hdec Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP
                Hwfp0 HbαM)
      as (b & bd2 & Θ0'' & S1 & ρe & Θ1' & Q' & E & Hbd & Hne2 & HbP
          & De & HrΘ1 & Hagr1 & HrQ & Hext & Hdom1).
    subst Θ0'. inversion Hbd; subst.
    exists S1, ρe, ((b ~ abind_flex_mono) ++ Θ1'), Q'.
    split; [ apply e_sub_flex__skip; [ exact Hne2 | exact HbP | exact De ] | ].
    split; [ exact HrΘ1 | ].
    split; [ exact Hagr1 | ].
    split; [ exact HrQ | ].
    split; [ exact Hext | ]. exact Hdom1.
  - (* W-SkipRigid *)
    intros NM M P0 Θ0 Θ1 Ξ α β Q Hne Hni Hβ1 Hprem IH.
    intros S0 Θ0' Ξ' α' P0' ρ V HrΘ HrΞ Hrα HrP0 Hagr Hinj Hfun Hwf Hdec
      Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP Hwfp0 HbαM.
    destruct (lift_sub_flex_peel IH Hne Hni Hβ1 HrΘ HrΞ Hrα HrP0 Hagr Hinj
                Hfun Hwf Hdec Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP
                Hwfp0 HbαM)
      as (b & bd2 & Θ0'' & S1 & ρe & Θ1' & Q' & E & Hbd & Hne2 & HbP
          & De & HrΘ1 & Hagr1 & HrQ & Hext & Hdom1).
    subst Θ0'. inversion Hbd; subst.
    exists S1, ρe, ((b ~ abind_tvar) ++ Θ1'), Q'.
    split;
      [ apply e_sub_flex__skip_rigid; [ exact Hne2 | exact HbP | exact De ] | ].
    split; [ exact HrΘ1 | ].
    split; [ exact Hagr1 | ].
    split; [ exact HrQ | ].
    split; [ exact Hext | ]. exact Hdom1.
  - (* W-SkipTmVar (type entry) : the two side conditions the rule does NOT
       state are THEOREMS — a term entry is not tvar-ish, so it is neither the
       walk's subject nor a free variable of the check-against *)
    intros NM M P0 Θ0 Θ1 Ξ α x Apay Q Hxout Hprem IH.
    intros S0 Θ0' Ξ' α' P0' ρ V HrΘ HrΞ Hrα HrP0 Hagr Hinj Hfun Hwf Hdec
      Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP Hwfp0 HbαM.
    assert (Huq1 : uniq (Ξ ++ (x ~ abind_var_typ Apay) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Hbx : binds x (abind_var_typ Apay)
                    (Ξ ++ (x ~ abind_var_typ Apay) ++ Θ0))
      by (unfold binds; apply in_or_app; right; left; reflexivity).
    assert (Hne : α <> x)
      by (intros ->; eapply a_binds_tvar_not_var_typ;
          [ exact Huq1 | exact Hbx | exact HbαM ]).
    assert (Hni : x `notin` ftvar_in_pskl P0).
    { intros Hin.
      pose proof (a_wf_pskl_ftv_binds Hwfp0 Hin) as Htv;
        eapply a_binds_tvar_not_var_typ; [ exact Huq1 | exact Hbx | exact Htv ]. }
    destruct (lift_sub_flex_peel IH Hne Hni Hxout HrΘ HrΞ Hrα HrP0 Hagr Hinj
                Hfun Hwf Hdec Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP
                Hwfp0 HbαM)
      as (b & bd2 & Θ0'' & S1 & ρe & Θ1' & Q' & E & Hbd & Hne2 & HbP
          & De & HrΘ1 & Hagr1 & HrQ & Hext & Hdom1).
    subst Θ0'. inversion Hbd; subst.
    exists S1, ρe, ((b ~ abind_var_typ A2) ++ Θ1'), Q'.
    split; [ apply e_sub_flex__skip_tm_var; exact De | ].
    split; [ exact HrΘ1 | ].
    split; [ exact Hagr1 | ].
    split; [ exact HrQ | ].
    split; [ exact Hext | ]. exact Hdom1.
  - (* W-SkipTmVar (skeleton entry) *)
    intros NM M P0 Θ0 Θ1 Ξ α x Qpay Q Hxout Hprem IH.
    intros S0 Θ0' Ξ' α' P0' ρ V HrΘ HrΞ Hrα HrP0 Hagr Hinj Hfun Hwf Hdec
      Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP Hwfp0 HbαM.
    assert (Huq1 : uniq (Ξ ++ (x ~ abind_var_skl Qpay) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Hbx : binds x (abind_var_skl Qpay)
                    (Ξ ++ (x ~ abind_var_skl Qpay) ++ Θ0))
      by (unfold binds; apply in_or_app; right; left; reflexivity).
    assert (Hne : α <> x)
      by (intros ->; eapply a_binds_tvar_not_var_skl;
          [ exact Huq1 | exact Hbx | exact HbαM ]).
    assert (Hni : x `notin` ftvar_in_pskl P0).
    { intros Hin.
      pose proof (a_wf_pskl_ftv_binds Hwfp0 Hin) as Htv;
        eapply a_binds_tvar_not_var_skl; [ exact Huq1 | exact Hbx | exact Htv ]. }
    destruct (lift_sub_flex_peel IH Hne Hni Hxout HrΘ HrΞ Hrα HrP0 Hagr Hinj
                Hfun Hwf Hdec Hdec2 Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP
                Hwfp0 HbαM)
      as (b & bd2 & Θ0'' & S1 & ρe & Θ1' & Q' & E & Hbd & Hne2 & HbP
          & De & HrΘ1 & Hagr1 & HrQ & Hext & Hdom1).
    subst Θ0'. inversion Hbd; subst.
    exists S1, ρe, ((b ~ abind_var_skl Q2) ++ Θ1'), Q'.
    split; [ apply e_sub_flex__skip_tm_skl; exact De | ].
    split; [ exact HrΘ1 | ].
    split; [ exact Hagr1 | ].
    split; [ exact HrQ | ].
    split; [ exact Hext | ]. exact Hdom1.
Qed.
