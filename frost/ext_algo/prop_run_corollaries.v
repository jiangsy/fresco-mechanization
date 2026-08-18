(** ext_algo — ⭐ WHAT THE EXTRACTED PROGRAM PROVES, at a closed program.

    The whole chain, composed once and for all: if the RUNNER — the OCaml
    function [extraction/extracted/frost_guess.ml] actually contains — answers
    [Some r] on a closed program, then the PAPER'S OWN DECLARATIVE JUDGEMENT
    types that program at the answer.  Nothing algorithmic survives in the
    conclusion.

    Four links, each already closed elsewhere and none re-derived here:

      e_typing_run_sound   (def_typing_impl.v §5)  the runner answers only
                                                   what the threaded relation
                                                   derives
      e_typing_sound_init  (prop_typing.v §2)      a threaded run at the entry
                                                   supply IS an [algo/] run,
                                                   over the SAME contexts
      a_typing_sound       (algo/typing/…)         thm:sound-type-inference
      a_typing_sound_infer / _check                the conservativity
                           (algo/typing/prop_closed.v)  corollaries: at a
                                                   flexible-free context the
                                                   decl-in-algo layer IS the
                                                   plain declarative system

    §1  inference mode — input the ghost [□]
    §2  checking mode — input a closed type [A0]

    ⚙ THE ENTRY SUPPLY IS NOT A PARAMETER OF THE CLAIM.  Both corollaries fix
    it at [ftvar_in_pskl P0 ∪ fvar_in_exp e ∪ ftvar_in_exp e], which is the
    supply [e_typing_sound_init] chooses and the reason that corollary is
    hypothesis-free: coverage becomes [reflexivity] and the context is [nil],
    so [uniq] is [uniq_nil].  It is also what [type.ml] does at its own entry
    point — start the counter, start the context empty.

    §3  ⭐ the COMPLETENESS half, at the same entry point (2026-08-19)
    §4  ⭐⭐ DECIDABILITY — the corollary §5 of the hand-off predicted

    ⚙ §1/§2 were SOUNDNESS ONLY when they were written: [None] meant "no rule
    applied" and was justified by nothing (§8b.7's result shape).  §3 closes
    that — the completeness ladder (campaign levels 1–8) is finished — and §4
    is the two-line consequence.

    ⚠️⚠️ READ §4's SCOPE BEFORE CITING IT.  What [None] refutes is a
    derivation of the THREADED relation [e_typing], which is the relation
    every rung of the ladder is stated over.  Turning that into a refutation
    of [algo/]'s own [a_typing] needs the converse of the bridge
    ([a_typing] ⟹ [e_typing] at a covering supply), and the campaign does NOT
    have it: §8c.3's obstruction — a derivation opens its binder wherever it
    likes and the threaded rules open at the SUPPLY — is what made every level
    quantify over [e_*] in the first place.  The two directions of §4 are
    therefore not symmetric in reach: the POSITIVE branch composes with
    §1/§2 all the way down to the paper's declarative judgement, the NEGATIVE
    branch stops at [e_typing]. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_shapes.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo_decl.def_consis_refine.
Require Import src.frost.algo_decl.def_typing.
(* [a_wf_exp] and its [{{ Θ ⊢ᵉ e }}a] notation live here, not in def_rules.v. *)
Require Import src.frost.algo.pat.prop_soundness_pat.
Require Import src.frost.algo.typing.prop_closed.
Require Import src.frost.ext_algo.notations.
Require Import src.frost.ext_algo.def_supply.
Require Import src.frost.ext_algo.def_typing.
Require Import src.frost.ext_algo.prop_typing.
Require Import src.frost.ext_algo.def_typing_impl.
Require Import src.frost.algo.prop_inc.            (* [lc_aenv] *)
Require Import src.frost.ext_algo.prop_termination. (* [aenv_defs_mono] *)
Require Import src.frost.ext_algo.prop_solve_det.   (* the [swaps_*] family *)
Require Import src.frost.ext_algo.prop_typing_complete.

Open Scope frost_e_scope.

(* ===================================================================== *)
(*  §1  INFERENCE mode                                                    *)
(* ===================================================================== *)

(** ⭐ THE EXTRACTED PROGRAM IS SOUND FOR THE PAPER'S DECLARATIVE SYSTEM.
    Run [e_typing_run] at [TI] on a closed, well-formed program with the
    ghost [□] as its input skeleton; if it answers [Some r], then [r]'s type,
    closed off by the metasubstitution [ζ] that instantiates the run's
    residual flexibles, is a declarative type of [e] — in BOTH the
    syntax-directed and the original declarative systems.

    The one hypothesis beside the answer is well-formedness of the subject,
    which is [a_typing_sound_infer]'s and is expected: a runner may be handed
    a term with free variables, and nothing about the supply makes that
    term typable. *)
Corollary e_typing_run_sound_infer : forall e r,
  {{ nil ⊢ᵉ e }}a ->
  e_typing_run (ftvar_in_pskl pskl_hole ∪ fvar_in_exp e ∪ ftvar_in_exp e)
    mode_ti nil pskl_hole e = Some r ->
  nil ⊴ (ty_ctx r) /\ {{ ⊢ (ty_ctx r) }}a /\ a_wf_ptyp (ty_ctx r) (ty_out r) /\
  ({{ (ty_ctx r) ⨟ empty ⊢ᵣ bskl_hole
      ⊳ (btyp_to_bskl (ptyp_to_btyp_syn (ty_out r))) }}ad) /\
  exists ζ, ζ ∷ (ty_ctx r) ⊑ nil /\
    ({{ nil ⊢ˢᵈ[ mode_ti ]
        e ⦂ (ptyp_to_btyp_syn (msubst_ptyp ζ (ty_out r))) }}d) /\
    ({{ nil ⊢[ mode_ti ]
        e ⦂ (ptyp_to_btyp_syn (msubst_ptyp ζ (ty_out r))) }}d).
Proof.
  intros e r Hexp Hrun.
  apply e_typing_run_sound in Hrun.
  apply e_typing_sound_init in Hrun.
  apply a_typing_sound_infer; assumption.
Qed.

(* ===================================================================== *)
(*  §2  CHECKING mode                                                     *)
(* ===================================================================== *)

(** ⭐ The same, at [TC] against a closed type [A0].  The input skeleton is
    [A0]'s painting [ptyp_to_pskl A0], which is what the entry supply is
    computed from, and the answer's colouring is forced the other way — the
    general statement's existential is [inh{A}]. *)
Corollary e_typing_run_sound_check : forall e A0 r,
  {{ nil ⊢ᵉ e }}a ->
  a_wf_ptyp nil A0 ->
  e_typing_run (ftvar_in_pskl (ptyp_to_pskl A0) ∪ fvar_in_exp e
                ∪ ftvar_in_exp e)
    mode_tc nil (ptyp_to_pskl A0) e = Some r ->
  nil ⊴ (ty_ctx r) /\ {{ ⊢ (ty_ctx r) }}a /\ a_wf_ptyp (ty_ctx r) (ty_out r) /\
  ({{ (ty_ctx r) ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (ptyp_to_pskl A0))
      ⊳ (btyp_to_bskl (ptyp_to_btyp_inh (ty_out r))) }}ad) /\
  exists ζ, ζ ∷ (ty_ctx r) ⊑ nil /\
    ({{ nil ⊢ˢᵈ[ mode_tc ]
        e ⦂ (ptyp_to_btyp_inh (msubst_ptyp ζ (ty_out r))) }}d) /\
    ({{ nil ⊢[ mode_tc ]
        e ⦂ (ptyp_to_btyp_inh (msubst_ptyp ζ (ty_out r))) }}d).
Proof.
  intros e A0 r Hexp HwfA0 Hrun.
  apply e_typing_run_sound in Hrun.
  apply e_typing_sound_init in Hrun.
  apply a_typing_sound_check; assumption.
Qed.

(* ===================================================================== *)
(*  §3  ⭐ THE COMPLETENESS HALF, at the same entry point                  *)
(*                                                                        *)
(*  The twin of [e_typing_sound_init]: at the entry supply and the empty   *)
(*  context every side condition of [e_typing_run_complete] except local   *)
(*  closure of the two INPUTS is [reflexivity] — coverage because the      *)
(*  supply IS the union it has to contain, [uniq]/[lc_aenv]/[defs_mono]    *)
(*  because the context is [nil].                                         *)
(* ===================================================================== *)

Corollary e_typing_run_complete_init : forall m P0 e Sd Θd Bd,
  {{ (ftvar_in_pskl P0 ∪ fvar_in_exp e ∪ ftvar_in_exp e) ↝ Sd
     ⊨ nil ⊢[ m ; P0 ] e ⦂ Bd ⊣ Θd }}e ->
  lc_pskl P0 -> lc_exp e ->
  exists r,
    e_typing_run (ftvar_in_pskl P0 ∪ fvar_in_exp e ∪ ftvar_in_exp e)
      m nil P0 e = Some r.
Proof.
  intros * Hd HP0 He.
  destruct (e_typing_run_complete Hd HP0 He lc_aenv_nil
              (List.Forall_nil _) (uniq_nil _)
              ltac:(simpl; fsetdec)) as [r [ps [Heq _]]].
  exists r. exact Heq.
Qed.

(* ===================================================================== *)
(*  §4  ⭐⭐ DECIDABILITY                                                   *)
(*                                                                        *)
(*  §5 of docs/HANDOFF-extractable-algo-encoding.md, verbatim: case on the *)
(*  runner's answer.  [Some r] is a derivation by soundness; [None] would  *)
(*  be contradicted by completeness if one existed.  ⭐ The step that makes *)
(*  it work is the runner being TOTAL — [e_typing_order_total] is what     *)
(*  makes [None] mean "rejected", not "out of fuel", and it is why the     *)
(*  termination campaign had to come first.                               *)
(*                                                                        *)
(*  ⚠️ The scope note in this file's header is part of the statement's      *)
(*  meaning: the refuted relation is the THREADED one.                     *)
(* ===================================================================== *)

Definition e_typable (S0 : supply) (m : mode) (Θ0 : aenv) (P0 : pskl)
    (e : exp) : Prop :=
  exists Sd Θd Bd, {{ S0 ↝ Sd ⊨ Θ0 ⊢[ m ; P0 ] e ⦂ Bd ⊣ Θd }}e.

Corollary e_typing_dec : forall S0 m Θ0 P0 e,
  lc_pskl P0 -> lc_exp e -> lc_aenv Θ0 -> aenv_defs_mono Θ0 -> uniq Θ0 ->
  ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 ∪ fvar_in_exp e ∪ ftvar_in_exp e
    [<=] S0 ->
  (* ⚠️ Written in APPLICATION form: the tree's meta-level substitution
     notations claim the [{ term …] prefix, so Coq's own [sumbool] notation
     no longer parses (def_guess_impl.v's header records the same trap for
     [sig]). *)
  sumbool (e_typable S0 m Θ0 P0 e) (~ e_typable S0 m Θ0 P0 e).
Proof.
  intros S0 m Θ0 P0 e HP0 He HΘ HD Hu Hcov.
  destruct (e_typing_run S0 m Θ0 P0 e) as [ r | ] eqn:Hrun.
  - (* the runner answered — SOUNDNESS turns the answer into a derivation *)
    left. exists (ty_supply r), (ty_ctx r), (ty_out r).
    exact (e_typing_run_sound _ _ _ _ _ _ Hrun).
  - (* the runner rejected — COMPLETENESS says no derivation exists *)
    right. intros [Sd [Θd [Bd Hd]]].
    destruct (e_typing_run_complete Hd HP0 He HΘ HD Hu Hcov)
      as [r [ps [Heq _]]].
    rewrite Hrun in Heq. discriminate.
Qed.

(** ⭐⭐ THE ENTRY-POINT INSTANCE — the claim worth putting in [README.v].
    A closed program at a locally-closed input skeleton either has a run of
    the threaded algorithm or provably has none, and the decision is the
    EXTRACTED FUNCTION's own answer.  ⚙ The two remaining hypotheses are
    inputs, not obligations: a dangling de Bruijn index is not a program. *)
Corollary e_typing_dec_init : forall m P0 e,
  lc_pskl P0 -> lc_exp e ->
  sumbool
    (e_typable (ftvar_in_pskl P0 ∪ fvar_in_exp e ∪ ftvar_in_exp e) m nil P0 e)
    (~ e_typable (ftvar_in_pskl P0 ∪ fvar_in_exp e ∪ ftvar_in_exp e)
         m nil P0 e).
Proof.
  intros m P0 e HP0 He.
  apply e_typing_dec; try assumption;
    [ apply lc_aenv_nil | apply (List.Forall_nil _) | apply (uniq_nil _)
    | simpl; fsetdec ].
Qed.
