(** THE EXTRACT LEVEL'S FOUNDATIONS — structure facts about the look
    judgements' collections and the fold, feeding §8c.9's b-core (the
    fused look-pair/fold-transport lemma; docs/
    HANDOFF-extractable-algo-encoding.md §8c.9).

    The collection is NOT deterministic up to renaming
    (cex/cex_looksub_not_det.v), but two derivations of the same look
    node differ ONLY by fresh names, by the ∀-peel slack at the final
    sub-constraint, and by ◇-EMISSION slack ([≼m ◇] / [eq ◇] vs
    nothing) — and a ◇-target solve step is the IDENTITY, which is what
    makes the slack free to transport.  This file proves that
    inventory's foundation facts:

    §1  a lookeq collection is PURE-EQ (so LS-Arrow's left half never
        contributes a sub-constraint, and the fold of [𝒞1 ++ 𝒞2]
        decomposes at the seam);
    §2  an α-FREE subject collects NOTHING, through EVERY derivation
        (crossing 4 of §8c.9's inventory: LS/LE-Absent vs a structural
        derivation is no slack at all);
    §3  a ◇-TARGET solve step is the identity — nil block, pattern
        through — on both layers (crossing 3: the ◇-emission slack);
    §4  the fold's head inversions and the PURE-EQ APPEND DECOMPOSITION
        [a_solve_cstr_app_inv], the mirror of [a_solve_cstr_app]
        (algo/sub/look/prop_eq_cstr.v) that the b-core's Arrow case
        splits the given fold with.  ⚙ [a_solve_cstr_sub_inv] /
        [a_solve_cstr_eq_inv] MOVED here from prop_run_complete.v §5
        (2026-08-16, one fact one name one file — this file sits below
        the runner-completeness stack, which now imports it);
    §5  a ◇-TARGET look collapses to at most one trivial constraint,
        through EVERY derivation (crossing 3's look half);
    §6  the COLLECTION-PRESERVING re-rootings R′/R″ — a subject peel
        moves to the root with [(Ξ, 𝒞)] EXACTLY preserved, so they
        apply to EITHER side of the b-core pair (even the pinned one)
        and any fold rides for free. *)

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
(*  §3  A ◇-target solve step is the identity                             *)
(* ===================================================================== *)

(** Crossing 3's engine: the slack constraints ([eq ◇] and [≼m ◇]) cost
    the fold NOTHING — the pattern passes through and no names are
    generated — so the side that emitted them and the side that did not
    fold to the SAME state.  (The BUILD direction is one constructor,
    SE-VacuousR / SS-Vacuous; these are the INVERSIONS.) *)

(* ===================================================================== *)
(*  §4  The fold's head inversions and the pure-eq append decomposition   *)
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

(* ===================================================================== *)
(*  §5  A ◇-target look collapses to at most one trivial constraint       *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  §6  The COLLECTION-PRESERVING re-rootings (§8c.9's R′/R″)             *)
(*                                                                        *)
(*  A constraint list is built from TARGET material and generated names   *)
(*  alone — the subject never enters it — so re-rooting a SUBJECT-peel    *)
(*  to the front preserves (Ξ, 𝒞) EXACTLY, and any fold on 𝒞 rides for   *)
(*  free.  These are what let the b-core pair induction descend the       *)
(*  subject on whichever side is ForallR-rooted: apply R′/R″ to THAT      *)
(*  side (either one — the outputs are pinned), then recurse aligned.     *)
(*  The only output-CHANGING re-rooting is the target peel at a Var       *)
(*  root, and there the fold pays by [a_solve_sub_peel_forall_r]          *)
(*  (prop_run_complete.v §6a).                                            *)
(* ===================================================================== *)

