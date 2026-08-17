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

    ⚠️ BUT THAT PREMISE IS NOT HEREDITARY, and that is the part to design
    around.  [SI-Arrow] concludes at [FN M] and runs its SECOND premise at
    [M] against the counterpart's CODOMAIN, so from

        NM = SK    M = FN TI    P0 = 1 → 1    subject 1 → ◇

    the second premise is exactly the rejected configuration above, with
    [P0b = 1 ≠ ◇].  A root-level premise says nothing there ([FN TI ≠ TI]
    makes it vacuous at the conclusion), so the invariant level 6 carries
    must follow the counterpart's arrow spine down alongside the mode —
    [FN]s in [M] matched against arrows in [P0], with [◇] required where the
    mode bottoms out at [TI].  ⚙ [SI-Flex-Assign] is where that has to be
    re-established rather than merely threaded: it re-enters subtyping under
    a substitution, which can turn a counterpart VARIABLE into an arrow.
    (The arrow configuration is stated but NOT machine-checked here — only
    its relation half is, below; the runner half needs the [e_consis_impl]
    call to reduce, which costs order proofs this probe has no use for.) *)

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
(*  1.  The RELATION accepts.                                            *)
(* ===================================================================== *)

Lemma probe_sub_ghost_ti_derivable : forall S0 Θ0,
  {{ S0 ↝ S0 ⊨ Θ0 ⊢[ a_sub_mode_sk | mode_ti | pskl_unit ]
     pskl_hole ⩽ pskl_unit ⊣ Θ0 }}e.
Proof. intros. apply e_sub__ghost. Qed.

(* ===================================================================== *)
(*  2.  The RUNNER rejects — at every order proof.                       *)
(* ===================================================================== *)

Lemma probe_sub_ghost_ti_runner_none : forall S0 Θ0 HP HP0 HD H,
  e_sub_impl S0 a_sub_mode_sk mode_ti pskl_unit Θ0 pskl_hole HP HP0 HD H
  = None.
Proof.
  intros. unfold e_sub_impl. simp e_sub_call_impl. reflexivity.
Qed.

(* ===================================================================== *)
(*  3.  One [SI-Arrow] down — the relation half of the configuration a    *)
(*      root-level premise would NOT exclude.                            *)
(* ===================================================================== *)

Lemma probe_sub_ghost_ti_under_arrow : forall S0 Θ0,
  {{ S0 ↝ S0 ⊨ Θ0 ⊢[ a_sub_mode_sk | (mode_fn mode_ti)
                    | (pskl_arrow pskl_unit pskl_unit) ]
     (pskl_arrow pskl_unit pskl_hole)
     ⩽ (pskl_arrow pskl_unit pskl_unit) ⊣ Θ0 }}e.
Proof.
  intros. apply e_sub__arrow with (S1 := S0) (Θ1 := Θ0).
  - apply e_consis__unit.
  - apply e_sub__ghost.
Qed.
