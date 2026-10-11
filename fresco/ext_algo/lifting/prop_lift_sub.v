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
  apply e_sub_sub_flex_mutind;
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

(** [lift_consis_nil] together with what every caller derives next: the
    supply growth and side 2's output package, and side 1's output
    ([⊴] and wf) — so the caller can go straight on to a second call. *)
Lemma lift_consis_nil_out : forall Θ0 P0 P Q Θ1,
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
    exists S1 ρe Θ1' Q',
      {{ S0 ↝ S1 ⊨ Θ0' ⊢[ empty | empty | P0' ] P' ∼ Q' ⊣ Θ1' }}e
      /\ rel_aenv (ρe ++ ρ) V Θ1 Θ1'
      /\ flex_agree_rel (ρe ++ ρ) V Θ1 Θ1'
      /\ rel_pskl (ρe ++ ρ) V Q Q'
      /\ rel_ext ρe (ftvar_in_aenv Θ0) S0
      /\ (forall a b, In (a, b) ρe -> a `in` dom Θ1 /\ b `in` dom Θ1')
      /\ S0 [<=] S1
      /\ dom Θ1' [<=] S1
      /\ ftvar_in_aenv Θ1' [<=] S1
      /\ uniq Θ1'
      /\ Θ0 ⊴ Θ1
      /\ {{ ⊢ Θ1 }}a.
Proof.
  intros Θ0 P0 P Q Θ1 Hc S0 Θ0' P0' P' ρ V HrΘ HrP0 HrP Hagr Hinj Hfun
    Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov HcovP Hwfp0 Hwfp.
  destruct (lift_consis_nil Hc HrΘ HrP0 HrP Hagr Hinj Hfun Hwf Huq2p
              Hftv2 Hscp Hblk HdΘ Hcov HcovP Hwfp0 Hwfp)
    as (S1 & ρe & Θ1' & Q' & De & HrΘ1 & Hagr1 & HrQ & Hext & Hdom).
  pose proof (e_consis_supply_grows De) as Hgr.
  assert (HcovE : ftvar_in_aenv Θ0' ∪ ftvar_in_pskl P0'
                  ∪ ftvar_in_pskl P' ∪ empty ∪ empty [<=] S0)
    by (clear - Hftv2 HcovP; fsetdec).
  destruct (a_consis_isub_wf_nil Hc Hwf Hwfp0 Hwfp) as [Hle HwfΘ1].
  assert (HdΘ1 : dom Θ1' [<=] S1).
  { pose proof ((proj2 (proj2 e_assign_unify_consis_dom_upper))
                  _ _ _ _ _ _ _ _ _ De) as Hup.
    clear - Hup HdΘ Hgr. fsetdec. }
  assert (Hftv1 : ftvar_in_aenv Θ1' [<=] S1)
    by (eapply (proj2 (proj2 e_assign_unify_consis_ctx_ftvar));
        [ exact De | clear - HcovE; fsetdec ]).
  assert (Huq1 : uniq Θ1')
    by (exact ((proj2 (proj2 a_assign_unify_consis_uniq)) _ _ _ _ _ _ _
                 (e_consis_sound De Huq2p HcovE) Huq2p)).
  exists S1, ρe, Θ1', Q'.
  exact (conj De (conj HrΘ1 (conj Hagr1 (conj HrQ (conj Hext (conj Hdom
          (conj Hgr (conj HdΘ1 (conj Hftv1 (conj Huq1 (conj Hle HwfΘ1))))))))))).
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
  destruct (lift_drop_mid HrΞ Hrest Hab Hagr Hinj Hfun Hwf Hdec Huq2p Hftv2
              Hscp Hblk Hβd HdΘ Hcov)
    as (VS & HVS & HVSsplit & Hβfun & Hβnd & Hbnd & HrΞS & HrΘS & HagrS
        & HinjS & HfunS & HwfC & Huq2C & Hftv2C & HscpS & HblkS & HdΘS & HcovS
        & Hshr_at & Hshr).
  assert (Hne2 : α' <> b).
  { intros Ex. apply Hne. rewrite Ex in Hrα. exact (Hinj α β b Hrα Hab). }
  assert (Hbdftv : ftvar_in_abind bd [<=] dom Θ0)
    by (eapply a_wf_aenv_cons_payload_ftv;
        eapply a_wf_aenv_strip_prefix; exact Hwf).
  assert (HbP : b `notin` ftvar_in_pskl P0')
    by (eapply rel_pskl_notin_r_inj;
        [ exact HrP0 | exact Hinj | exact Hab | exact Hβp ]).
  assert (HbαS : a_binds_tvar α (Ξ ++ Θ0)).
  { eapply a_binds_tvar_strip_mid; [ exact Hbα | | | ];
      solve [ intros E; inversion E; subst; apply Hne; reflexivity
            | intros τ0 E; inversion E; subst; apply Hne; reflexivity ]. }
  assert (HwfpS : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a)
    by (eapply a_wf_pskl_strip_mid; [ exact Hwfp0 | exact Hβp ]).
  destruct (IH S0 Θ0'' Ξ' α' P0' ρ VS HrΘS HrΞS (Hshr_at α α' Hrα Hne)
              (Hshr P0 P0' HrP0 Hβp) HagrS HinjS HfunS
              HwfC Hdec Hdec2 Huq2C Hftv2C HscpS HblkS HdΘS HcovS HcovP
              HwfpS HbαS)
    as (S1 & ρe & Θ1' & Q' & D2 & HrΘ1 & Hagr1 & HrQ & Hext1 & Hdom1).
  assert (Hbnd1 : b `notin` dom Θ1').
  { pose proof ((proj2 e_sub_sub_flex_dom_upper) _ _ _ _ _ _ _ _ _ _ D2)
      as Hup.
    assert (HbS0 : b `in` S0)
      by (repeat rewrite dom_app in HdΘ; simpl in HdΘ; clear - HdΘ; fsetdec).
    rewrite dom_app in Hup. clear - Hup Hbnd HbS0.
    repeat rewrite dom_app in Hbnd. fsetdec. }
  (* ⭐ the head agrees because [rel_abind] forces the two entries to have
     the same KIND: flexible on both sides, or rigid on both *)
  assert (Hflag : a_flex_tvar ((β ~ bd) ++ Θ1) β
                  <-> a_flex_tvar ((b ~ bd2) ++ Θ1') b).
  { inversion Hbd; subst;
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
             [ exact Hf | discriminate | intros ?; discriminate ]) ]. }
  destruct (lift_reattach_mid Hab Hbd Hinj Hcov HVS HVSsplit Hβfun Hbdftv Hflag
              HrΘ1 Hagr1 Hext1 Hdom1 Hβd)
    as (HrF & HagrF & HextF & HdomF).
  exists b, bd2, Θ0'', S1, ρe, Θ1', Q'.
  split; [ reflexivity | ].
  split; [ exact Hbd | ].
  split; [ exact Hne2 | ].
  split; [ exact HbP | ].
  split; [ exact D2 | ].
  split; [ exact HrF | ].
  split; [ exact HagrF | ].
  split.
  { eapply rel_pskl_mono;
      [ exact HrQ | intros x y Hx; exact Hx | exact HVS ]. }
  exact (conj HextF HdomF).
Qed.

Theorem a_sub_sub_flex_rel_e :
  (forall NM M P0 Θ0 P Q Θ1, a_sub NM M P0 Θ0 P Q Θ1 ->
     lift_sub_concl NM M P0 Θ0 P Q Θ1) /\
  (forall NM M P0 Θ0 Ξ α Q Θ1, a_sub_flex NM M P0 Θ0 Ξ α Q Θ1 ->
     lift_sub_flex_concl NM M P0 Θ0 Ξ α Q Θ1).
Proof.
  apply a_sub_sub_flex_tm_mutind.
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
    destruct (lift_restrict_junk HΞΘ0 HrΘ Hagr Hinj Hfun Hcov)
      as (Hρ0incl & Hρ0in & Hcl00 & Hcr00 & HΞcols & HrΘ0 & Hagr0 & Hinj0
          & Hfun0 & Hcov0).
    assert (HrB0 : rel_pskl (restrict_l (dom Ξ) ρ) V B B2).
    { apply rel_pskl_restrict_l; [ exact HrB | ].
      simpl in HΞB. clear - HΞB. fsetdec. }
    assert (HrA0 : rel_pskl (restrict_l (dom Ξ) ρ) V A P')
      by (apply rel_pskl_restrict_l; [ exact HrP | exact HΞA ]).
    (* ⚠️ ρ0 must survive the row's later bare [subst]s, so make it opaque
       now — every fact about it is already stated above. *)
    set (ρ0 := restrict_l (dom Ξ) ρ) in *. clearbody ρ0.
    assert (Hcl0 : cols_l (restrict_pairs α α2 ρ0) [<=] cols_l ρ0)
      by apply cols_l_restrict_pairs.
    destruct (lift_consis_open_pair HrΘ0 Hagr0 Hinj0 Hfun0 HfrΘ Hα2f HαV Hα2V)
      as (HrΘ' & Hagr' & Hinj' & Hfun').
    assert (Hblk0 : forall a, a `in` dom Θ1 -> a `notin` dom Θ0 ->
                    a `notin` cols_l ρ0)
      by (intros a Ha Hn; pose proof (Hblk a Ha Hn) as Hc;
          clear - Hc Hcl00; fsetdec).
    destruct (lift_consis_open_scope Hwf Huq2p Hftv2 Hscp Hblk0 HdΘ Hcov0 Hαd
                Hα2d)
      as (Hwf' & Huq2' & Hftv2' & Hscp' & _ & HdΘ' & Hcov').
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
    assert (Hdomeo : forall a b0, In (a, b0) ρeo ->
              a `in` dom Θ1 /\ b0 `in` dom Θ1').
    { subst ρeo. eapply rel_aenv_restrict_l_dom;
        [ exact HrΞ2 | exact Hinjout
        | intros a b Hin; apply in_or_app; auto | ].
      intros a b Hin. destruct (Hdomout _ _ Hin) as [Hd1 Hd2].
      destruct Hext as [Hfresh _]. destruct (Hfresh _ _ Hin) as [Hna Hnb].
      assert (Ha : a <> α) by (intros ->; apply Hna; simpl; clear; fsetdec).
      assert (Hb : b <> α2) by (intros ->; apply Hnb; clear; fsetdec).
      simpl_env in Hd1. simpl_env in Hd2. rewrite !dom_app.
      split; [ clear - Hd1 Ha; fsetdec | clear - Hd2 Hb; fsetdec ]. }
    exists S1, ρeo, Θ1', (pskl_all_syn B2).
    split; [ exact Dc | ].
    (* the CONTEXT relation: drop the JUNK pairs and the OPENER pair, then
       widen back to the caller's list *)
    assert (HαfΘ1 : α `notin` ftvar_in_aenv Θ1).
    { assert (Hd : α `notin` dom Θ1) by (clear - Hfr; fsetdec).
      clear - Hd Hftv1. fsetdec. }
    assert (Hincl : forall a b0,
              In (a, b0) (restrict_l (dom Ξ)
                            (ρe ++ restrict_pairs α α2 ρ0)) ->
              In (a, b0) (ρeo ++ ρ)).
    { subst ρeo. apply restrict_l_app_restore.
      intros a b Hin. apply Hρ0incl. eapply restrict_pairs_incl; exact Hin. }
    assert (HrΘfin : rel_aenv (ρeo ++ ρ) V Θ1 Θ1').
    { eapply rel_aenv_mono.
      - eapply rel_aenv_restrict_l; [ | exact HΞf1 ].
        eapply rel_aenv_drop_mid; [exact HrΘ1' | exact HαfΘ1].
      - exact Hincl.
      - intros z Hz; exact Hz. }
    split; [ exact HrΘfin | ].
    assert (Hextfin : rel_ext ρeo (ftvar_in_aenv Θ0) S0).
    { eapply rel_ext_mono;
        [ exact Hext | exact Hρeoincl
        | simpl; clear; fsetdec | clear; fsetdec ]. }
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
    assert (Hdm0 : dom Θ0 [<=] dom Θ1) by (exact (auc_dom_mono_consis Hc)).
    assert (Hdm1 : dom Θ1 [<=] dom Θ2)
      by (exact ((proj1 a_sub_sub_flex_dom_mono) _ _ _ _ _ _ _ Hs)).
    assert (Hblk1 : forall a, a `in` dom Θ1 -> a `notin` dom Θ0 ->
                    a `notin` cols_l ρ)
      by (intros a Ha Hn; apply Hblk; [ clear - Ha Hdm1; fsetdec | exact Hn ]).
    assert (HcovP1 : ftvar_in_pskl P0a2 ∪ ftvar_in_pskl P12 [<=] S0)
      by (simpl in HcovP; clear - HcovP; fsetdec).
    destruct (lift_consis_nil_out Hc HrΘ HrP0a HrP1 Hagr Hinj Hfun Hwf Huq2p
                Hftv2 Hscp Hblk1 HdΘ Hcov HcovP1 Hw0a Hw1a)
      as (S1 & ρe1 & Θ1' & Q1' & D1e & HrΘ1 & Hagr1 & HrQ1 & Hext1 & Hdom1
          & Hgr1 & HdΘ1 & Hftv1 & Huq1' & Hle01 & HwfΘ1).
    destruct (lift_seq_widen Hinj Hfun Hext1 Hdom1 Hwf Hscp Hcov Hblk Hdm0
                Hdm1 Hgr1 HdΘ1)
      as (Hinj1 & Hfun1 & Hscp1 & Hcov1 & Hblk2).
    assert (Hwfp0b1 : {{ Θ1 ⨟ empty ⊢ₚₛ P0b }}a)
      by (eapply a_isub_wf_pskl; [ exact Hle01 | exact Hw0b ]).
    assert (Hwfp21 : {{ Θ1 ⨟ empty ⊢ₚₛ P2 }}a)
      by (eapply a_isub_wf_pskl; [ exact Hle01 | exact Hw1b ]).
    assert (HrP0b' : rel_pskl (ρe1 ++ ρ) V P0b P0b2)
      by (apply rel_pskl_widen; exact HrP0b).
    assert (HrP2' : rel_pskl (ρe1 ++ ρ) V P2 P22)
      by (apply rel_pskl_widen; exact HrP2).
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
    exact (lift_seq_ext Hext1 Hext2 Hdom1 Hdom2 Hwf Hdm0 Hdm1 Hgr1 HdΘ1
             Hdm2').
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
    assert (Hα'd0 : α' `notin` dom Θ0) by (clear - Hα'; solve_notin_auto).
    assert (Hα'Ξ : α' `notin` dom Ξ) by (clear - Hα'; solve_notin_auto).
    assert (Hα'cr : α' `notin` cols_r ρ) by (clear - Hα'S0 Hcov; fsetdec).
    assert (Hα'd0' : α' `notin` dom Θ0') by (clear - Hα'S0 HdΘ; fsetdec).

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
    (* ---- the two pairs, and the extended relation ---- *)
    assert (Ha2V : a2 `notin` V) by (clear - Ha2 Hcov; fsetdec).
    assert (Hb2V : b2 `notin` V) by (clear - Hb2 Hcov; fsetdec).
    assert (Ha2cr : a2 `notin` cols_r ρ) by (clear - Ha2 Hcov; fsetdec).
    assert (Hb2cr : b2 `notin` cols_r ρ) by (clear - Hb2 Hcov; fsetdec).
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
        [ apply rel_inj_push; [ exact Hinj | exact Hb2V | exact Hb2cr ]
        | exact Ha2V | simpl; clear - Ha2cr Hab2; fsetdec ]. }
    assert (Hfun1 : rel_fun ρ1 V
              (dom (Ξ ++ (α0 ~ abind_flex_mono_def
                            (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
                      ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono)
                      ++ Θ0))).
    { subst ρ1. eapply rel_fun_weaken;
        [ apply rel_fun_push;
            [ apply rel_fun_push; [ exact Hfun | exact HβV | exact Hβcl ]
            | exact HαV | simpl; clear - Hαcl Hne; fsetdec ]
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
          [ exact HrΞ | exact Hρ1incl | intros x Hx; exact Hx ].
      - apply rel_aenv__cons.
        + eapply rel_atom_incl; [ exact Hab0 | exact Hρ1incl ].
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
            [ exact Hrest | exact Hρ1incl | intros x Hx; exact Hx ]. }
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
        exact (proj1 Hagr x HxV).
      - intros x y Hin. subst ρ1.
        destruct Hin as [E1 | [E2 | Hin]].
        + injection E1 as -> ->. split; intros _; left; unfold binds;
            apply in_or_app; right; right; right; left; reflexivity.
        + injection E2 as -> ->. split; intros _; left; unfold binds;
            apply in_or_app; right; right; left; reflexivity.
        + assert (Hxα : x <> α)
            by (intros ->; apply Hαcl; eapply cols_l_in; exact Hin).
          assert (Hxβ : x <> β)
            by (intros ->; apply Hβcl; eapply cols_l_in; exact Hin).
          assert (Hya2 : y <> a2)
            by (intros ->; apply Ha2cr; eapply cols_r_in; exact Hin).
          assert (Hyb2 : y <> b2)
            by (intros ->; apply Hb2cr; eapply cols_r_in; exact Hin).
          rewrite (a_flex_tvar_solve_shape Ξ _ _ Θ0 Hxα Hxβ).
          rewrite (a_flex_tvar_solve_shape Ξ' _ _ Θ0'' Hya2 Hyb2).
          exact (proj2 Hagr x y Hin). }
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
      clear - Hc Hnα Hnβ. fsetdec. }
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
                            [ exact HrP0 | intros x y Hx; right; right;
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
    { apply rel_ext_flex_pairs; simpl.
      - clear - Hne; solve_uniq.
      - clear - Hb2; solve_uniq.
      - clear - Hαft Hβft; fsetdec.
      - clear - Ha2 Hb2; fsetdec. }

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
    destruct (lift_drop_mid HrΞ Hrest Hab Hagr Hinj Hfun Hwf Hdec Huq2p Hftv2
                Hscp Hblk Hβd HdΘ Hcov)
      as (VC & HVC & HVCsplit & Hβfun & Hβnd & Hbnd & HrΞC & HrΘ0C & HagrC
          & HinjC & HfunC & HwfC & Huq2C & Hftv2C & HscpC & HblkC & HdΘC & HcovC
          & _ & _).
    assert (HrΘC : rel_aenv ρ VC (Ξ ++ Θ0) (Ξ' ++ Θ0''))
      by (apply rel_aenv_app; [ exact HrΞC | exact HrΘ0C ]).
    assert (HrV : rel_pskl ρ V (pskl_var_f α) (pskl_var_f α'))
      by (constructor; exact Hrα).
    assert (HwfV : {{ (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0) ⨟ empty ⊢ₚₛ
                     (pskl_var_f α) }}a)
      by (apply a_wf_pskl__var; exact HbαM).
    assert (HcovV : ftvar_in_pskl (pskl_var_f α') [<=] S0).
    { simpl. pose proof (rel_atom_r_in Hrα) as Hin. clear - Hin Hcov. fsetdec. }
    destruct (lift_subst_def Hab Hrτ Hinj Hβfun HVCsplit Hwf Hdec Hftv2 HrP0
                Hwfp0 HcovP) as (HrPsubC & HwfPsubC & HcovPs).
    destruct (lift_subst_def Hab Hrτ Hinj Hβfun HVCsplit Hwf Hdec Hftv2 HrV HwfV
                HcovV) as (HrVsubC & HwfVsubC & HcovVs).
    assert (HcovS : ftvar_in_pskl (subst_pskl_in_pskl (ptyp_to_pskl t2) b P0')
                    ∪ ftvar_in_pskl
                        (subst_pskl_in_pskl (ptyp_to_pskl t2) b
                           (pskl_var_f α')) [<=] S0)
      by (clear - HcovPs HcovVs; fsetdec).
    destruct (IH S0 (Ξ' ++ Θ0'')
                (subst_pskl_in_pskl (ptyp_to_pskl t2) b P0')
                (subst_pskl_in_pskl (ptyp_to_pskl t2) b (pskl_var_f α'))
                ρ VC HrΘC HrPsubC HrVsubC HagrC HinjC HfunC HwfC Huq2C
                Hftv2C HscpC HblkC HdΘC HcovC HcovS HwfPsubC HwfVsubC)
      as (S1 & ρe & Θ1' & Q' & D2 & HrΘ1 & Hagr1 & HrQ & Hext1 & Hdom1).
    assert (Hτdom : ftvar_in_abind (abind_flex_mono_def τ) [<=] dom Θ0)
      by (apply a_wf_ptyp_ftv_dom;
          exact (proj1 (@a_wf_aenv_mid_def_inv Ξ β τ Θ0 Hdec Hwf))).
    assert (Hflag : a_flex_tvar ((β ~ abind_flex_mono_def τ) ++ Θ1) β
                    <-> a_flex_tvar ((b ~ abind_flex_mono_def t2) ++ Θ1') b)
      by (split; intros _; apply a_flex_tvar_head_flexish;
          right; eexists; reflexivity).
    destruct (lift_reattach_mid Hab Hbd Hinj Hcov HVC HVCsplit Hβfun Hτdom
                Hflag HrΘ1 Hagr1 Hext1 Hdom1 Hβd)
      as (HrF & HagrF & HextF & HdomF).
    exists S1, ρe, ((b ~ abind_flex_mono_def t2) ++ Θ1'), Q'.
    split; [ apply e_sub_flex__assign with (τ := t2); exact D2 | ].
    split; [ exact HrF | ].
    split; [ exact HagrF | ].
    split.
    { eapply rel_pskl_mono;
        [ exact HrQ | intros x y Hx; exact Hx | exact HVC ]. }
    exact (conj HextF HdomF).
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
