(** PROBE (2026-08-17): the assignment walk MIGRATES a flexible DOWNWARD,
    so no POSITIONAL context refinement can relate a walk's input to its
    output.  This is the constraint that kills the [ctx_ref] sketch of
    §8c.12c, and any successor design must satisfy it.
    (docs/HANDOFF-close-consis-unrestricted.md.)

    ⚠️ §8c.12c proposed replacing the motive's bare [a_inc] by a STRUCTURAL
    refinement that determines the context's HEAD — rows for "same entry",
    "solved in place" and "fresh entry inserted on the right".  All three
    rows are POSITIONAL: they walk the two contexts in lockstep.  The walk
    does not respect positions.

    [Assign-Depend] moves a flexible the payload MENTIONS into the pending
    block, and [Assign-SolveM] then deposits that block BELOW the solved
    target.  So an entry that was ABOVE the target ends up BELOW it:

        input   β̂, α̂           walk:  α̂ ≔ β̂
        output  α̂ ≔ β̂, β̂       — the two entries have SWAPPED

    ⚙ The migration is forced by well-formedness, not incidental: the
    deposited definition mentions [β̂], so [β̂] must end up below it.  It is
    the same phenomenon that refuted the paper's own optimality claim —
    docs/PAPER-GAPS.md, "flex migration below term binders defeats the
    factoring" — and it is why the paper's information increase is
    non-positional in the first place.

    ⇒ A successor design may NOT assume the two contexts can be walked in
    lockstep.  Either it tolerates migration explicitly, or it recovers the
    head some other way. *)

From Coq Require Import Lists.List.
From Metalib Require Import Metatheory.

From src Require Import fresco.notations.
From src Require Import fresco.def_shapes.
From src Require Import fresco.algo.def_rules.
From src Require Import fresco.ext_algo.notations.
From src Require Import fresco.ext_algo.basic.def_supply.
From src Require Import fresco.ext_algo.basic.def_guess.
From src Require Import fresco.ext_algo.consistency.def_consis.

Open Scope fresco_e_scope.

(** [β̂] starts ABOVE [α̂] and ends BELOW it. *)
Lemma probe_assign_migrates : forall S (α β : atom), α <> β ->
  {{ S ↝ S ⊨ ((β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ nil)
     ⊲[ nil ] α ≔ (pskl_var_f β)
     ⊣ ((α ~ abind_flex_mono_def (ptyp_var_f β))
        ++ (β ~ abind_flex_mono) ++ nil) }}e.
Proof.
  intros S α β Hne.
  (* Assign-Depend: β̂ is mentioned by the payload, so it migrates. *)
  replace ((α ~ abind_flex_mono_def (ptyp_var_f β))
           ++ (β ~ abind_flex_mono) ++ nil)
    with ((α ~ abind_flex_mono_def (ptyp_var_f β))
          ++ nil ++ (nil ++ (β ~ abind_flex_mono)) ++ nil)
    by (simpl_env; reflexivity).
  apply e_assign__depend.
  - exact Hne.
  - simpl. fsetdec.
  - (* Assign-SolveM at the target's own position *)
    apply e_assign__solve_m.
    + simpl. clear - Hne. fsetdec.
    + apply e_guess_mono__var.
    + apply mono_ptyp__var.
Qed.
