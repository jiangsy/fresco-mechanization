(** REGRESSION TEST — the two configurations that used to sink [sub_shield] at
    an ARROW payload are now SHIELDED, one by each of the base rows DESIGN §10.5
    added to [flex_apart].

    THIS FILE USED TO BE A COUNTEREXAMPLE.  Before [fa_flexfree] and
    [fa_rho_var] existed, [sub_shield]'s [flex_apart_walk] conjunct was
    UNSATISFIABLE at an arrow [P0] against a tagged-identity guess: Sub-ForallL's
    walk step [fastep_all_r] opens the guess at a fresh β, adds β to Δρ, and
    LEAVES P0 ALONE, so the walk reaches [flex_apart Θ0 {β} (Pa → Pb) (var β)] —
    where [fa_clean] wanted [{β} ∩ {β} = ∅] and every congruence row wanted
    another shape.  That is what forced the repair, and the two witnesses below
    are kept because they say different things:

    · §1 [⟨⟩ → ⟨⟩] is FLEX-FREE — nothing to keep apart — and is now covered by
      [fa_flexfree], the general rule of which [fa_unit] / [fa_var_rigid] /
      [fa_hole] were three special cases;
    · §2 [(∀γ. γ→γ) → α̂] is NOT flex-free and its counterpart is NOT mono-ish,
      so neither [fa_flexfree] nor the mono-counterpart route of
      prop_sub_shield_supply.v reaches it.  It is covered by [fa_rho_var]: the
      guess at that point IS a Δρ-variable, and a ρ-replaced rigid is safe
      opposite ANY payload — P6-Cv's own leaf, which [flex_shield] had stated as
      [fsh_rho_var] all along.

    Keep both: they are what ties the two base rows to the failure they fix. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_extra.
Require Import src.frost.def_tags.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo_sub.
Require Import src.frost.algo.def_decl_algo_sub_hyg.
Require Import src.frost.algo.prop_look_complete.
Require Import src.frost.algo.prop_look_complete_cstr.
Require Import src.frost.algo.prop_look_complete_sub_var.
Require Import src.frost.algo.prop_look_complete_sub_cstr.   (* sub_shield *)

Set Implicit Arguments.

(* ===================================================================== *)
(*  The step that used to strand the walk                                 *)
(* ===================================================================== *)

(** ψa = ∀^ε b. b — the DECORATED identity quantifier: a legitimate ForallL
    guess ([is_tskl], ghost-free, tagged by exactly {ε}). *)
Definition ψid (ε : atom) : uskl := uskl_all_etag ε (uskl_var_b 0).

Lemma ψid_tskl : forall ε, is_tskl (ψid ε).
Proof.
  intros ε; unfold ψid.
  apply is_tskl__all_etag with (L := empty); intros α _; cbn.
  apply is_tskl__var.
Qed.

(* ⭕ [the_step] DELETED (2026-08-05).  It exhibited Sub-ForallL's walk step
   ([fa_walk]) reaching the state that used to be unreachable by any
   [flex_apart] rule.  [fa_walk] itself is gone — P6-Sv no longer takes
   [flex_apart_walk] under the repaired [SolE-FlexR] — so the step has nothing
   to step in.  The two regression THEOREMS below are unaffected: they are
   about [flex_apart]'s base rows [fa_flexfree] / [fa_rho_var] at the state
   itself, which is what this file exists to check, and [flex_apart] is
   untouched.  Coq text at commit `dbb4b2c`. *)

(* ===================================================================== *)
(*  §1  THE FLEX-FREE ARROW — covered by [fa_flexfree]                    *)
(* ===================================================================== *)

Theorem p7_shield_arrow_flexfree_now_covered : forall Θ0 β,
  flex_apart Θ0 (add β empty) (pskl_arrow pskl_unit pskl_unit)
    (uskl_var_f β).
Proof.
  intros Θ0 β. apply fa_flexfree.
  intros α Hα. cbn in Hα. exfalso; clear - Hα; fsetdec.
Qed.

(* ===================================================================== *)
(*  §2  THE ARROW WITH A FLEXIBLE COMPONENT — covered by [fa_rho_var]     *)
(* ===================================================================== *)

(** [(∀γ. γ→γ) → α̂]: NOT flex-free once α̂ is a Θ0-flexible, and its
    counterpart is not mono-ish either (the domain refines from a ∀, hence
    lands on an [all_inh]).  Only [fa_rho_var] reaches it. *)
Definition P0poly (a : atom) : pskl :=
  pskl_arrow (pskl_all_syn (pskl_arrow (pskl_var_b 0) (pskl_var_b 0)))
             (pskl_var_f a).

Theorem p7_shield_arrow_poly_now_covered : forall Θ0 a β,
  flex_apart Θ0 (add β empty) (P0poly a) (uskl_var_f β).
Proof.
  intros Θ0 a β. apply fa_rho_var. clear; fsetdec.
Qed.

(** …and it really is NOT flex-free, so [fa_flexfree] genuinely does not
    suffice — this is why BOTH rows were needed. *)
Lemma p7_shield_arrow_poly_not_flexfree : forall Θ0 a,
  binds a abind_flex_mono Θ0 ->
  ~ pskl_flex_free Θ0 (P0poly a).
Proof.
  intros Θ0 a Hb Hff.
  apply (Hff a); [ cbn; clear; fsetdec | left; exact Hb ].
Qed.

Print Assumptions p7_shield_arrow_flexfree_now_covered.
Print Assumptions p7_shield_arrow_poly_now_covered.
