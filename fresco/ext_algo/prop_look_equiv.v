(** THE EXTRACT LEVEL'S FOUNDATIONS — structure facts about the look
    judgements' collections and the fold, feeding §8c.9's b-core (the
    fused look-pair/fold-transport lemma; docs/
    HANDOFF-extractable-algo-encoding.md §8c.9).

    The collection is NOT deterministic up to renaming
    (cex/cex_looksub_not_det.v), but two derivations of the same look
    node differ ONLY by fresh names, by the ∀-peel slack at the final
    sub-constraint, and by ◇-EMISSION slack ([≼m ◇] / [eq ◇] vs
    nothing).  This file proves that inventory's foundation facts:

    §1  [a_cstr_is_eq], the PURE-EQ shape of a lookeq collection's
        constraints;
    §2  an α-FREE subject collects NOTHING, through EVERY derivation
        (crossing 4 of §8c.9's inventory: LS/LE-Absent vs a structural
        derivation is no slack at all);
    §3  the fold's head inversions and the PURE-EQ APPEND DECOMPOSITION
        [a_solve_cstr_app_inv], the mirror of [a_solve_cstr_app]
        (algo/sub/look/prop_eq_cstr.v) that the b-core's Arrow case
        splits the given fold with.  ⚙ [a_solve_cstr_sub_inv] /
        [a_solve_cstr_eq_inv] MOVED here from prop_run_complete.v §5
        (2026-08-16, one fact one name one file — this file sits below
        the runner-completeness stack, which now imports it). *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.prop_ln.
Require Import src.fresco.prop_tag.
Require Import src.fresco.def_shapes.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.prop_basic.
Require Import src.fresco.algo.prop_swap.
Require Import src.fresco.algo.sub.prop_looksub.

(* the ∀-quantified inputs are inferable from the derivation arguments, so
   applications read [lemma Hd Habs] — the §8c.6 note on implicit result
   args applies to this file's consumers *)
Set Implicit Arguments.

Open Scope fresco_a_scope.

(* ===================================================================== *)
(*  §1  A lookeq collection is pure-eq                                    *)
(* ===================================================================== *)

Definition a_cstr_is_eq (c : a_cstr) : Prop := exists Q, c = a_cstr_eq Q.

(* ===================================================================== *)
(*  §2  An α-free subject collects nothing                                *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  §3  The fold's head inversions and the pure-eq append decomposition   *)
(* ===================================================================== *)

(** ⚙ Moved from prop_run_complete.v §5 (2026-08-16) — see the header. *)
Lemma a_solve_cstr_sub_inv : forall Θ m Q C P Ξ P',
  {{ Θ ⊩ (a_cstr_sub m Q :: C) ⨾ P ⤳ Ξ ⨾ P' }}a ->
  C = nil /\ {{ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}a.
Proof.
  intros * Hd. inversion Hd; subst. split; [ reflexivity | assumption ].
Qed.

Lemma a_solve_cstr_eq_inv : forall Θ Q C P Ξ P',
  {{ Θ ⊩ (a_cstr_eq Q :: C) ⨾ P ⤳ Ξ ⨾ P' }}a ->
  exists Ξ1 Ξ2 P'',
    Ξ = Ξ2 ++ Ξ1
    /\ {{ Θ ⊢ₑ P ∼ Q ⤳ Ξ1 ⨾ P'' }}a
    /\ {{ (Ξ1 ++ Θ) ⊩ C ⨾ P'' ⤳ Ξ2 ⨾ P' }}a.
Proof.
  intros * Hd. inversion Hd; subst.
  match goal with
  | Hh : a_solve_eq _ _ _ ?X1 ?Pm, Ht : a_solve_cstr _ _ _ ?X2 _ |- _ =>
      exists X1, X2, Pm
  end.
  repeat split; assumption.
Qed.

(** The mirror of [a_solve_cstr_app] (algo/sub/look/prop_eq_cstr.v:155):
    a fold across a pure-eq prefix SPLITS at the seam.  The b-core's
    Arrow case decomposes the derivation-side fold with this, hands the
    halves to the two IHs, and recomposes the runner side with the
    original. *)
Lemma a_solve_cstr_app_inv : forall C1 Θ 𝒞2 P Ξ P',
  Forall a_cstr_is_eq C1 ->
  {{ Θ ⊩ (C1 ++ 𝒞2) ⨾ P ⤳ Ξ ⨾ P' }}a ->
  exists Ξ1 Ξ2 Pmid,
    Ξ = Ξ2 ++ Ξ1
    /\ {{ Θ ⊩ C1 ⨾ P ⤳ Ξ1 ⨾ Pmid }}a
    /\ {{ (Ξ1 ++ Θ) ⊩ 𝒞2 ⨾ Pmid ⤳ Ξ2 ⨾ P' }}a.
Proof.
  induction C1 as [ | c C1' IH ]; intros Θ 𝒞2 P Ξ P' Hall Hd.
  - exists nil, Ξ, P.
    split; [ rewrite app_nil_r; reflexivity | ].
    split; [ apply a_solve_cstr__empty | ].
    simpl. exact Hd.
  - inversion Hall as [ | ? ? [Q ->] Hall' ]; subst.
    simpl in Hd.
    apply a_solve_cstr_eq_inv in Hd
      as (Ξa & Ξb & Pmid0 & -> & Hhead & Htail).
    apply IH in Htail as (Ξ1' & Ξ2 & Pmid & -> & Hpre & Hpost);
      [ | exact Hall' ].
    exists (Ξ1' ++ Ξa), Ξ2, Pmid.
    split;
      [ solve [ apply app_assoc | symmetry; apply app_assoc ] | ].
    split.
    + eapply a_solve_cstr__eq; [ exact Hhead | exact Hpre ].
    + replace ((Ξ1' ++ Ξa) ++ Θ) with (Ξ1' ++ (Ξa ++ Θ))
        by (solve [ apply app_assoc | symmetry; apply app_assoc ]).
      exact Hpost.
Qed.
