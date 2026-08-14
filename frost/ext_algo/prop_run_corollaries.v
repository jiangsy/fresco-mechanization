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

    ⚠️ SOUNDNESS ONLY.  [None] still means "no rule applied" and is justified
    by nothing (§8b.7's result shape); that [None] means UNTYPABLE is runner
    completeness, and with totality it is what yields decidability.  These two
    corollaries are the [Some] half of that argument and are stated so the
    second half can be composed onto them without restatement.

    ⚙ Deliberately NOT in README.v: the paper index carries the paper's own
    labelled statements, and these are the extracted program's contract.  The
    README-worthy claim on this line is DECIDABILITY, which is owed the
    completeness direction first. *)

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
