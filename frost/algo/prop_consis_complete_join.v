(* ===================================================================== *)
(*  Consistency COMPLETENESS by induction on the declarative join         *)
(*  (paper: consistency-proofs.tex "Completeness of Consistency", 2226).  *)
(*                                                                        *)
(*  Unlike [a_assign_unify_consis_optimal] (which inducts on the          *)
(*  ALGORITHMIC derivation and TAKES a_consis as input), this PRODUCES     *)
(*  the algorithmic derivation as an output of the join-induction, the way *)
(*  the paper does.  This is the paper-faithful frame in which the ghost / *)
(*  tophole / structural cases dispatch cleanly (see join_precise, whose   *)
(*  8/10 clean cases validated it).  WIP flagship — honest admits.         *)
(* ===================================================================== *)
Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.
Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_decorate.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_precise.
Require Import src.frost.algo.prop_mono_bridge.
Require Import src.frost.algo.prop_metasubst.
Require Import src.frost.algo.prop_consis_sound.
Require Import src.frost.algo.prop_consis_complete.

Set Implicit Arguments.

Lemma consis_complete : forall Ψ Θ S Qb,
  Ψ ⨟ Θ ⊨ₛᵃ S ≈ Qb ->
  forall F Δ1 Δ2 Θ0 P0 P ρ,
    a_wf_aenv Θ0 ->
    Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
    Θ0 ⨟ empty ⊢ₚₛᵃ P ->
    (forall X, X `in` (Δ1 `union` Δ2) -> binds X abind_tvar Θ0) ->
    no_flex_dep (Δ1 `union` Δ2) Θ0 ->
    flex_above_free (Δ1 `union` Δ2) Θ0 ->
    Θ0 ≤[ ρ ] Θ ->
    a_wf_aenv Θ ->
    no_flex_dep (Δ1 `union` Δ2) Θ ->
    Ψ [=] empty ->
    S = pskl_to_uskl (msubst_pskl ρ P) ->
    ad_refine_syn_f Δ1 Θ Δ1 (pskl_to_bskl_inh (msubst_pskl ρ P0)) Qb ->
    ad_refine_pskl_f Δ2 Θ Δ2 (msubst_pskl ρ P) (bskl_to_pskl Qb) ->
    exists P1 Θ1,
      a_consis F Δ1 Δ2 Θ0 P0 P P1 Θ1 /\
      (forall ρ1, is_id_msubst ρ1 -> Θ0 ≤[ ρ1 ] Θ1 ->
         exists ζ,
           Θ1 ≤[ ζ ] Θ /\
           a_inc_equiv Θ0 ρ (msubst_compose ζ ρ1) Θ /\
           Θ ⨟ (Δ1 `union` Δ2) ⊢ₚᵣᵃ
             (msubst_bskl ζ (pskl_to_bskl_syn P1)) ⊑ (bskl_to_pskl Qb)).
Proof.
  intros Ψ Θ S Qb Hj.
  induction Hj; intros F Δ1 Δ2 Θ0 PP0 PP ρ
    Hwf0 HwfP0 HwfP Hrig Hnfd0 Hfaf Hinc Hwfth Hnfdth HΨ HeqS Hrs Hrp.
  (* Each join case does a subject-shape analysis on [P] (via HeqS):
     the CONCRETE shapes produce the matching a_consis structural rule;
     a flexible [P = pskl_var α̂] produces a_consis__flex_l/flex_r (mutual
     with assignment).  Precision comes from the join-induction IH (cf.
     join_precise); factoring from opt_axiom_factor (axiom nodes) / the glue
     (structural) / the assign+unify completeness (flex).  WIP: honest admits. *)
  - (* unit.  Needs input-P0 analysis via Hrs (P0 ∈ {unit,hole,tophole,flex}):
       P0=unit → a_consis__unit; P0=hole → a_consis__ghost_r;
       P0=tophole → a_consis__univ_ghost_r; P0=flex → a_consis__flex_l.
       The subject P is likewise unit or a flexible (FlexL). *)
    admit.
  - admit. (* var (rigid) *)
  - admit. (* arrow *)
  - (* forall_inh_tagged : subject uskl_all_etag ∉ range(pskl_to_uskl) *)
    destruct (msubst_pskl ρ PP); simpl in HeqS; discriminate.
  - admit. (* forall_inh_untagged *)
  - (* forall_syn_tagged : subject uskl_all_etag ∉ range(pskl_to_uskl) *)
    destruct (msubst_pskl ρ PP); simpl in HeqS; discriminate.
  - admit. (* forall_syn *)
  - (* ghostg : subject uskl_holeg ∉ range(pskl_to_uskl) *)
    destruct (msubst_pskl ρ PP); simpl in HeqS; discriminate.
  - (* topholeg : subject uskl_topholeg ∉ range(pskl_to_uskl) *)
    destruct (msubst_pskl ρ PP); simpl in HeqS; discriminate.
  - admit. (* hole *)
  - admit. (* tophole *)
  - admit. (* tophole_inh *)
  - admit. (* tophole_drop *)
  - admit. (* flex_l *)
  - admit. (* flex_r *)
Admitted.
