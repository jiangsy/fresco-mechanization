(** PROBE (2026-08-17): the LEVEL-6 overlap audit's one finding —
    [SI-Ghost] fires at [M = TI], where the runner has already committed to
    [SI-Infer]'s shape test and rejects.
    (docs/HANDOFF-extractable-algo-encoding.md §8c.11.)

    ⚠️ [SI-Ghost] carries NO mode restriction.  The paper writes it as an
    axiom over an arbitrary [\M] (full-algo-spec.tex:849)

        ────────────────────────────── SI-Ghost
         Θ0 ⊢[SK][M][P0] ◇ ⩽ P0 ⊣ Θ0

    while its immediate neighbour [SI-UnivGhostL] (:855) spells the
    restriction out — "[\M \neq \TI] % should not inst when \TI".  The mech
    mirrors both faithfully ([e_sub__ghost] / [e_sub__univ_ghost_l],
    ext_algo/def_sub.v; likewise [a_sub__ghost], algo/def_rules.v:1264).

    The RUNNER dispatches on the mode FIRST, and its [mode_ti] arm is
    [SI-Infer]'s and nothing else: it tests the counterpart for [◇] and
    returns [None] otherwise (ext_algo/def_sub_impl.v:509-515).  So at

        NM = SK    M = TI    counterpart P0 ≠ ◇    subject ◇

    the relation derives a judgement the runner rejects — checked below at
    [P0 = 1], for EVERY order proof (the [mode_ti] arm consumes none).

    ⭐ WHAT IT COSTS LEVEL 6.  A runner-sided completeness statement
    quantified over an arbitrary [(NM, M, P0)] is FALSE, and the motive owes
    a premise.  The obvious one — [M = mode_ti -> P0 = pskl_hole] — is what
    the CALLERS satisfy ([e_typing]/[e_pat] reach [TI] only at [◇], and
    [e_typing] never calls the [SK] side at all), and under it the mode is
    settled: at [(TI, ◇)] both [SI-Infer] and [SI-Ghost] fire, and they
    return the SAME triple [(S0, Θ0, P)], so the pair needs no uniqueness
    argument — the level-6 analogue of level 5's [U-Rigid]/[U-Flex] pair,
    which [e_unify_refl] settled the same way.

    ⚠️ BUT THAT PREMISE IS NOT HEREDITARY.  [SI-Arrow] concludes at [FN M]
    and runs its SECOND premise at [M] against the counterpart's CODOMAIN,
    so from

        NM = SK    M = FN TI    P0 = 1 → 1    subject 1 → ◇

    the second premise is exactly the rejected configuration above, with
    [P0b = 1 ≠ ◇].  A root-level premise says nothing there ([FN TI ≠ TI]
    makes it vacuous at the conclusion).  §3 below checks this
    configuration's RELATION half; its runner half is not checked here,
    since reducing the [e_consis_impl] call costs order proofs the probe has
    no other use for.

    ⭐⭐ The invariant to carry instead is the authors' own, and their
    implementation states it in its TYPES: the paper indexes the judgement
    by [M] and [P0] separately, but [type.ml] fuses them and projects [P0]
    back out (paper/artifact/implementation/lib/type.ml:8-11, :395-398 —
    [type mode = Infer | Check of pure_type | Fun of pure_type * mode] with
    [sk_of_mode] sending [Infer] to [Ghost] and [Fun (p, m)] to
    [TArr (p, sk_of_mode m)]).  So [P0 = sk_of_mode M] holds there by
    construction: [TI] pairs with [◇] and cannot do otherwise, and each [FN]
    layer pairs with one arrow of the counterpart.  ⚙ It also THREADS —
    [SI-Flex-Assign] re-enters under [subst τ β P0], but substitution is
    structural, so it maps an arrow to an arrow and [◇] to [◇], the only two
    positions such an invariant inspects.  §8c.11 has the spelling and the
    per-row check. *)

From Coq Require Import Lists.List.
From Metalib Require Import Metatheory.
From Equations Require Import Equations.

From src Require Import frost.notations.
From src Require Import frost.algo.def_rules.
From src Require Import frost.ext_algo.notations.
From src Require Import frost.ext_algo.def_consis.
From src Require Import frost.ext_algo.def_sub.
From src Require Import frost.ext_algo.def_sub_impl.

Open Scope frost_e_scope.

(* ===================================================================== *)
(*  1.  ⭐ RESOLVED (2026-08-17): the RELATION NO LONGER ACCEPTS.          *)
(* ===================================================================== *)

(** [SI-Ghost] now carries the [M <> TI] guard its neighbour always had
    (algo/def_rules.v, and see its header), so at the configuration this
    probe was written about NO rule fires: [SI-Infer] wants the counterpart
    to be [◇] and it is [1]; [SI-Ghost] is barred by the guard; every other
    row fixes the mode to [TC] or [FN _], or wants a non-[◇] subject. *)
Lemma probe_sub_ghost_ti_not_derivable : forall S0 S1 Θ0 Θ1 Q,
  ~ {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_sk | mode_ti | pskl_unit ]
       pskl_hole ⩽ Q ⊣ Θ1 }}e.
Proof. intros * Hd. inversion Hd; subst; congruence. Qed.

(* ===================================================================== *)
(*  2.  The RUNNER rejects — at every order proof.  Now they AGREE.       *)
(* ===================================================================== *)

Lemma probe_sub_ghost_ti_runner_none : forall S0 Θ0 HP HP0 HD H,
  e_sub_impl S0 a_sub_mode_sk mode_ti pskl_unit Θ0 pskl_hole HP HP0 HD H
  = None.
Proof.
  intros. unfold e_sub_impl. simp e_sub_call_impl. reflexivity.
Qed.

(* ===================================================================== *)
(*  3.  ⭐ WHY THE GUARD HAD TO GO ON THE RULE, not on a motive: the       *)
(*      configuration is reached HEREDITARILY, one [SI-Arrow] down, where   *)
(*      a root-level premise is vacuous.  With the guard the inner node is  *)
(*      barred too, so the whole family is gone.                           *)
(* ===================================================================== *)

Lemma probe_sub_ghost_ti_under_arrow_not_derivable : forall S0 S1 Θ0 Θ1 Q,
  ~ {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_sk | (mode_fn mode_ti)
                      | (pskl_arrow pskl_unit pskl_unit) ]
       (pskl_arrow pskl_unit pskl_hole) ⩽ Q ⊣ Θ1 }}e.
Proof.
  intros * Hd. inversion Hd; subst.
  (* the only row at an arrow subject is [SI-Arrow], and its SECOND premise
     IS §1's configuration — barred by the same lemma *)
  eapply probe_sub_ghost_ti_not_derivable; eassumption.
Qed.
