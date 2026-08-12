(** The ERASURES between [ad_pat_sub]'s completeness mirrors, and the fuel
    monotonicity the ForallR case needs.

    [def_subtyping.v] DEFINES the paper's all-in-one subtyping box
    [ad_pat_sub] and the two mech-internal mirrors the completeness proof
    measures it by — [ad_pat_sub_fuel] (that plus the FUEL) and [ad_pat_sub_v]
    (the fuel existentially closed).  This file proves the maps BETWEEN them.

    ⚙ There used to be a THIRD, [ad_pat_sub_g] — the fuel with the leaf datum
    forgotten — because [ad_pat_sub] itself did not carry the paper's leaf
    presupposition.  It does since 2026-08-12, so [_g] and its forgetful map
    [ad_pat_sub_fuel_forget] are gone.

    ⚙ WHY IT IS THIS EARLY, and not with the completeness files: the
    SOUNDNESS side has to CONCLUDE [_gv] ([ad_pat] / [ad_sd_typing] embed the
    leaf-valid join, so thm:complete-skeleton/type-inference can consume it),
    and [algo/sub/prop_soundness_sub.v] sits BEFORE the completeness files in
    the dependency order.  [algo_decl/] is upstream of all of [algo/sub/], so
    the constraint is met here.

    ⚙ Split out of [def_subtyping.v] 2026-08-11.  It was the ONLY [def_*.v] in
    the tree carrying lemmas; every other has zero, and the naming rule is
    [def_*.v] for definitions, [prop_*.v] for what is proved about them. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_extra.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo_decl.def_consis_refine.
Require Import src.frost.algo_decl.def_subtyping.
Require Import src.frost.deco_algo.def_decorated.

Set Implicit Arguments.

(* the judgement notations below live in this scope; `Open Scope` is not
   transitive through `Require Import`, so a consumer needs it open too *)
Open Scope frost_ad_scope.

(* ===================================================================== *)
(*  The two ERASURES + fuel monotonicity.                                 *)
(*                                                                        *)
(*  ⚙ [ad_pat_sub_of_fuel] and [ad_pat_sub_fuel_weaken] are HERE, not with *)
(*  the completeness files: the SOUNDNESS side has to CONCLUDE [_gv]       *)
(*  ([ad_pat] / [ad_sd_typing] embed the leaf-valid join, so               *)
(*  thm:complete-skeleton/type-inference can consume it), and              *)
(*  algo/prop_soundness_sub.v sits BEFORE both of them in the dependency   *)
(*  order.  Both are plain inductions over the mirrors and need nothing    *)
(*  this file does not already import.                                     *)
(* ===================================================================== *)

(** Fuel monotonicity for the leaf-valid hygienic join.  The fuel is the
    declarative derivation's HEIGHT, so a derivation of height [n] is also
    one of every larger height.  Needed because the permutation below
    returns the family at whatever height the extraction yields, while
    [a_sub_complete_forall_r] wants it at exactly [n] for a conclusion at
    [S n]. *)
Lemma ad_pat_sub_fuel_weaken : forall n NM M Ψ Θ R Q,
  ad_pat_sub_fuel n NM M Ψ Θ R Q ->
  forall m, n <= m -> ad_pat_sub_fuel m NM M Ψ Θ R Q.
Proof.
  intros n NM M Ψ Θ R Q H; induction H; intros m Hle;
    try solve [ econstructor; eauto ].
  - (* forall_r : the conclusion's fuel is [S n] *)
    destruct m as [ | m' ]; [ lia | ].
    apply ad_pat_sub_fuel__forall_r with (L := L).
    intros α Hα. apply H0; [ exact Hα | lia ].
  - (* arrow *)
    destruct m as [ | m' ]; [ lia | ].
    eapply ad_pat_sub_fuel__arrow;
      [ exact H | exact H0 | apply IHad_pat_sub_fuel; lia | assumption ].
  - (* forall_l_tagged *)
    destruct m as [ | m' ]; [ lia | ].
    eapply ad_pat_sub_fuel__forall_l_tagged;
      [ eassumption | eassumption | eassumption | eassumption | eassumption
      | apply IHad_pat_sub_fuel; lia ].
  - (* forall_l_untagged *)
    destruct m as [ | m' ]; [ lia | ].
    eapply ad_pat_sub_fuel__forall_l_untagged;
      [ eassumption | eassumption | eassumption | eassumption | eassumption
      | apply IHad_pat_sub_fuel; lia ].
Qed.

(** The erasure the [ad_pat] / [ad_sd_typing] consumers want: a leaf-valid
    join IS a plain declarative subtyping derivation.

    ⚙ A DIRECT induction on [_gv] since 2026-08-12.  It used to factor through
    [ad_pat_sub_g_of : _g -> ad_pat_sub] and then [ad_pat_sub_fuel_forget], both
    of which are gone: once [ad_pat_sub] itself carries the leaf
    presupposition, the leaf-FORGETTING mirror cannot reach it at all. *)
Lemma ad_pat_sub_of_fuel : forall n NM M Ψ Θ R Q,
  ad_pat_sub_fuel n NM M Ψ Θ R Q ->
  {{ Ψ ⨟ Θ ⊢ˢ[ NM | M ] R ⩽ Q }}ad.
Proof.
  intros n NM M Ψ Θ R Q H; induction H.
  - eapply ad_pat_sub__infer; eauto.
  - eapply ad_pat_sub__check; eauto.
  - eapply ad_pat_sub__forall_r; eauto.
  - eapply ad_pat_sub__univ_ghost_r; eauto.
  - eapply ad_pat_sub__arrow; eauto.
  - eapply ad_pat_sub__forall_l_tagged; eauto.
  - eapply ad_pat_sub__forall_l_untagged; eauto.
  - eapply ad_pat_sub__ghost; eauto.
  - eapply ad_pat_sub__ghostg; eauto.
  - eapply ad_pat_sub__univ_ghost_l; eauto.
  - eapply ad_pat_sub__univ_ghost_lg; eauto.
  - eapply ad_pat_sub__flex_mono; eauto.
Qed.

