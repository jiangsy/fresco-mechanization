(** ext_algo — COMPLETENESS OF THE RUNNERS (campaign §8c.3/§8c.5): an
    `a_*` derivation at the runner's committed names means the runner does
    not return [None].  The plan is §8c.3's — ONE induction per judgement,
    on the ORDER, inverting the `a_*` derivation at each level — and the
    runners' unfolding equations (§8c.4) are what make the dispatch
    analysable at all.

    §1 opens the file with the ENTRY-POINT EXHIBIT: the AT-Unit branch at
    infer mode, end to end, through every layer this campaign depends on —
    [simp e_typing_impl] (the derived clause equation), the [e_sub_impl]
    wrapper, [simp e_sub_call_impl] (the tagged block's §8c.4 equation),
    the term-level dispatch reducing at concrete mode/shape, and
    [pskl_readback] computing.  ⚙ No [vm_compute]/[Eval] can do this: the
    runners recurse on a Qed-opaque totality proof, so plain reduction is
    stuck by design — the equations are quantified over the domain proof,
    which is exactly why the chain goes through (§8c.3's "insensitive to
    which domain proof was supplied").

    The check-mode twin runs one layer deeper — SI-Check calls
    [e_consis_impl], so it additionally exercises the consistency block's
    §8c.4 equations ([simp e_consis_call_impl]; U-Unit answers).  It
    became provable the moment def_consis_impl.v flipped, and it is the
    end-to-end witness that ALL TWELVE runner blocks are now
    computationally analysable. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.
From Equations Require Import Equations.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_shapes.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.
Require Import src.frost.ext_algo.notations.
Require Import src.frost.ext_algo.def_supply.
Require Import src.frost.ext_algo.def_sub.
Require Import src.frost.ext_algo.def_order.
Require Import src.frost.ext_algo.def_consis_impl.
Require Import src.frost.ext_algo.def_sub_impl.
Require Import src.frost.ext_algo.def_pat_impl.
Require Import src.frost.ext_algo.def_typing_impl.

Open Scope frost_e_scope.

(* ===================================================================== *)
(*  §1  The entry-point exhibit: AT-Unit, infer mode                      *)
(* ===================================================================== *)

Lemma e_typing_run_complete_unit_infer : forall S0,
  e_typing_run S0 mode_ti nil pskl_hole exp_unit
  = Some (mk_typing_result S0 nil ptyp_unit).
Proof.
  intros. unfold e_typing_run.
  simp e_typing_impl.
  cbn.
  unfold e_sub_impl.
  simp e_sub_call_impl.
  cbn.
  reflexivity.
Qed.

(** The check-mode twin, at the paper's own pattern shape [⌈unit⌉]: one
    layer deeper — SI-Check runs the consistency block, whose U-Unit row
    answers. *)
Lemma e_typing_run_complete_unit_check : forall S0,
  e_typing_run S0 mode_tc nil (ptyp_to_pskl ptyp_unit) exp_unit
  = Some (mk_typing_result S0 nil ptyp_unit).
Proof.
  intros. unfold e_typing_run.
  simp e_typing_impl.
  cbn.
  unfold e_sub_impl.
  simp e_sub_call_impl.
  cbn.
  unfold e_consis_impl.
  simp e_consis_call_impl.
  cbn.
  reflexivity.
Qed.
