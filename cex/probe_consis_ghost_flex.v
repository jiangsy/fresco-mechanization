(** PROBE (2026-08-16): §8c.10's scoped output relation is WRONG — the
    consis trio's runner and its rules diverge at a GHOST-versus-FLEXIBLE
    node, and the divergence is NOT a renaming.
    (docs/HANDOFF-extractable-algo-encoding.md §8c.10, second pass.)

    §8c.10 scoped level 5 as ONE runner-sided induction whose motive
    relates the derivation's output context to the RUNNER's "up to
    renaming" — the renaming being forced only by [Assign-SolveM]'s
    [guess^TY], which invents names.  That is the piece this probe
    refutes: at

        pattern ◇   subject α̂        (α̂ an UNDEFINED flexible)

    BOTH [U-GhostR] (a ghost pattern answers the subject) and [U-FlexL]
    (a [nonflex] pattern is ASSIGNED to the flexible subject) fire —
    [nonflex{P0}] rules out a flexible variable, NOT a ghost — and their
    output CONTEXTS differ:

        U-GhostR    Θ0                                    (unchanged)
        U-FlexL     (α ~ def β̂) ++ (β̂ ~ flex) ++ Θ0'      (α̂ SOLVED)

    because [guess^TY(◇)] invents a fresh flexible (def_guess.v's
    [e_guess_mono__ghost]).  The runner takes [U-GhostR]: the tagged
    block's consistency clause matches the PATTERN first and its
    [pskl_ghost] arm is unconditional in the subject
    (def_consis_impl.v:759).  The mirror pair (pattern α̂, subject ◇)
    diverges the same way, [U-Ghost] against [U-FlexR].

    ⚠️ This is the paper's own system, not an encoding artefact:
    [U-FlexL] / [U-FlexR] carry only [nonflex{P_0}] / [nonflex{P}]
    (algorithmic.tex:757, :764) and [U-GhostR] only
    [Δ1 ∩ ftv(P) = ∅] (:782).  [fresco/algo]'s twin is identical
    (def_rules.v:1127-1137).

    WHY IT BREAKS THE SCOPED DESIGN.  The divergence is
    INFORMATION-FREE — α̂ is solved to a FRESH UNCONSTRAINED flexible —
    but it is not a renaming: the derivation's context has one entry
    MORE than the runner's and binds α̂ where the runner leaves it free.
    The two are equi-general, i.e. related by an ALIAS INDIRECTION, and
    "up to renaming" cannot state that.  The relation is consumed in
    exactly one place, [U-Arrow] — the only row whose premise re-reads a
    threaded output as another premise's INPUT ([Assign-Assign] and
    [Flex-Flex-Assign] re-wrap their premise's output but never re-read
    it) — so what level 5 owes is an ALIAS-ELIMINATION transport:
    a derivation at the alias-extended context yields one at the
    runner's, with alias-related outputs.

    WHAT IS MACHINE-CHECKED HERE:
      (1) [probe_consis_ghostr_route] — the runner's route, U-GhostR;
      (2) [probe_consis_flexl_route]  — U-FlexL, SAME inputs, and its
                                        output context spelled out;
      (3) [probe_consis_runner_ghostr] — the RUNNER, reduced: it really
                                        returns the U-GhostR answer;
      (4) [probe_consis_outputs_differ] — the two contexts are not equal;
      (5) [probe_consis_ghost_route] / [probe_consis_flexr_route] — the
                                        mirror pair.

    ⚙ WHAT IS INSPECTED, NOT CHECKED (the rest of the audit, recorded in
    the handoff): every OTHER (pattern, subject) shape pair admits
    exactly one consistency rule, so the runner's first-match commits to
    the derivation's root everywhere else.  Two further overlaps are
    benign: (pattern ◇, subject ◇) — [U-Ghost] and [U-GhostR] agree on
    both output and join — and, inside [unifyvar], [Flex-Flex-Id] against
    [Flex-Flex-Skip] / [Flex-Flex-Assign] at [α̂ ≈ᵘ α̂], which needs the
    small reflexivity lemma "unifying a variable with ITSELF returns the
    supply and the context unchanged". *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.Sumbool.
Require Import Metalib.Metatheory.
From Equations Require Import Equations.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.def_supply.
Require Import src.fresco.ext_algo.def_guess.
Require Import src.fresco.ext_algo.def_consis.
Require Import src.fresco.ext_algo.def_order.
Require Import src.fresco.ext_algo.prop_termination.
Require Import src.fresco.ext_algo.def_consis_impl.

Open Scope fresco_a_scope.
Open Scope fresco_e_scope.

(** The context: one UNDEFINED flexible, which is all the divergence
    needs.  [aenv_defs_mono] holds of it, so the runner's precondition
    is met. *)
Definition probe_gf_ctx (α : atom) : aenv := (α ~ abind_flex_mono) ++ nil.

(** [U-FlexL]'s output: α̂ solved to the flexible [guess^TY(◇)] invents. *)
Definition probe_gf_ctx_solved (α β : atom) : aenv :=
  (α ~ abind_flex_mono_def (ptyp_var_f β)) ++ (β ~ abind_flex_mono) ++ nil.

Lemma probe_gf_defs_mono : forall α, aenv_defs_mono (probe_gf_ctx α).
Proof.
  intros. unfold probe_gf_ctx. simpl.
  apply List.Forall_cons; [ apply entry_def_mono_flex | apply List.Forall_nil ].
Qed.

(* --------------------------------------------------------------------- *)
(*  (1) + (2)  pattern ◇ against a flexible subject: two routes           *)
(* --------------------------------------------------------------------- *)

(** (1) the route the runner takes — the context is UNCHANGED. *)
Lemma probe_consis_ghostr_route : forall Δ1 Δ2 S α,
  Δ1 ∩ ftvar_in_pskl (pskl_var_f α) [=] empty ->
  {{ S ↝ S ⊨ (probe_gf_ctx α) ⊢[ Δ1 | Δ2 | pskl_ghost ]
     (pskl_var_f α) ∼ (pskl_var_f α) ⊣ (probe_gf_ctx α) }}e.
Proof.
  intros. apply e_consis__ghost_r. assumption.
Qed.

(** The mirror walk, likewise no longer liftable: [U-FlexR] demands
    [P <> ◇]. *)
Lemma probe_consis_flexr_walk : forall S α β,
  β `notin` S ->
  {{ S ↝ (add β S) ⊨ (probe_gf_ctx α) ⊲[ nil ] α ≔ pskl_ghost
     ⊣ (probe_gf_ctx_solved α β) }}e.
Proof.
  intros * Hβ. unfold probe_gf_ctx, probe_gf_ctx_solved.
  replace ((α ~ abind_flex_mono_def (ptyp_var_f β))
             ++ (β ~ abind_flex_mono) ++ nil)
    with ((α ~ abind_flex_mono_def (ptyp_var_f β))
             ++ ((β ~ abind_flex_mono) ++ nil) ++ nil ++ nil)
    by reflexivity.
  apply e_assign__solve_m.
  + simpl. fsetdec.
  + apply e_guess_mono__ghost. assumption.
  + apply mono_ptyp__var.
Qed.
