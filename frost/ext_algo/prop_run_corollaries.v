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

    ⚠️ §4's SCOPE NOTE, KEPT FOR HISTORY AND NOW DISCHARGED (2026-08-22).
    What §4's [None] refutes is a derivation of the THREADED relation
    [e_typing], which is the relation every rung of the ladder is stated
    over.  Turning that into a refutation of the paper's own judgement
    needed the converse of the bridge ([a_typing] ⟹ [e_typing] at a
    covering supply) — §8c.3's obstruction.  THE LIFT IS NOW BUILT
    ([a_typing_rel_e], prop_lift.v §13), and §5 composes it with the
    closed-program completeness corollaries: a declaratively-typed closed
    program makes the runner answer [Some], so [None] refutes the
    DECLARATIVE judgement itself.  §6 is the headline consequence —
    decidability of the paper's own type inference, decided by the
    extracted function's answer.

    §5  ⭐⭐⭐ completeness at the paper's judgement (the lift, composed)
    §6  ⭐⭐⭐ decidability of the paper's type inference *)

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
Require Import src.frost.algo_decl.prop_conserv.  (* [d_wf_exp] + the nil bridges *)
Require Import src.frost.ext_algo.notations.
Require Import src.frost.ext_algo.def_supply.
Require Import src.frost.ext_algo.def_typing.
Require Import src.frost.ext_algo.prop_typing.
Require Import src.frost.ext_algo.def_typing_impl.
Require Import src.frost.algo.prop_inc.            (* [lc_aenv] *)
Require Import src.frost.ext_algo.prop_termination. (* [aenv_defs_mono] *)
Require Import src.frost.ext_algo.prop_solve_det.   (* the [swaps_*] family *)
Require Import src.frost.ext_algo.prop_typing_complete.
Require Import src.frost.prop_basic.
Require Import src.frost.algo.prop_basic.
Require Import src.frost.algo.typing.prop_soundness_typing.
Require Import src.frost.ext_algo.prop_solve_rel.
Require Import src.frost.ext_algo.prop_lift.
Require Import src.frost.algo.prop_precise.   (* [a_wf_ptyp_to_wf_pskl] *)

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

(* ===================================================================== *)
(*  §5  ⭐⭐⭐ THE NEGATIVE BRANCH REACHES THE PAPER'S OWN JUDGEMENT         *)
(*                                                                        *)
(*  The lift ([a_typing_rel_e], prop_lift.v §13) composed with the        *)
(*  closed-program completeness corollaries: a declaratively-typed        *)
(*  closed program HAS a threaded run, so [e_typing_run]'s [None] now     *)
(*  refutes the paper's own declarative judgement — README §VI's scope    *)
(*  caveat is discharged.  At a CLOSED program the lift's relation is     *)
(*  instantiated at the EMPTY pair list and support: reflexivity on       *)
(*  anything the support covers ([rel_exp_refl] / [rel_pskl_refl]), and   *)
(*  every side condition is either [nil]-trivial or the emptiness of the  *)
(*  program's free variables — term variables by [a_typing_fvar_binds]    *)
(*  on the completeness run, type variables by [a_wf_exp_ftv_dom].        *)
(* ===================================================================== *)

(** ⚙ The relation's three vacuous side conditions, at the empty instance. *)
Lemma lift_typing_nil_instance :
  rel_inj (@nil (atom * atom)%type) empty /\
  rel_fun (@nil (atom * atom)%type) empty (dom (@nil (atom * abind)%type)) /\
  flex_agree_rel (@nil (atom * atom)%type) empty
    (@nil (atom * abind)%type) (@nil (atom * abind)%type).
Proof.
  split; [ | split ].
  - intros a1 a2 b H1 H2.
    inversion H1 as [ u1 v1 Hp | u1 Hv ]; subst; [ inversion Hp | ].
    inversion H2 as [ u2 v2 Hp2 | u2 Hv2 ]; subst;
      [ inversion Hp2 | reflexivity ].
  - intros a b1 b2 Hd0 H1 H2.
    inversion H1 as [ u1 v1 Hp | u1 Hv ]; subst; [ inversion Hp | ].
    inversion H2 as [ u2 v2 Hp2 | u2 Hv2 ]; subst;
      [ inversion Hp2 | reflexivity ].
  - split;
      [ intros v Hv; exfalso; clear - Hv; fsetdec
      | intros a b Hin; inversion Hin ].
Qed.

Corollary e_typing_run_complete_decl_infer : forall e (B : btyp),
  {{ nil ⊢ᵉ e }}d ->
  {{ nil ⊢[ mode_ti ] e ⦂ B }}d ->
  exists r,
    e_typing_run (ftvar_in_pskl pskl_hole ∪ fvar_in_exp e ∪ ftvar_in_exp e)
      mode_ti nil pskl_hole e = Some r.
Proof.
  intros e B Hwfd Hd.
  (* the subject's algorithmic wf and local closure are DERIVED, not
     hypotheses: the nil bridge, then [a_wf_exp_lc] *)
  pose proof (d_wf_exp_to_a _ _ Hwfd) as Hwfe. simpl in Hwfe.
  pose proof (a_wf_exp_lc Hwfe) as Hlc.
  destruct (a_typing_complete_decl_infer Hwfe Hd) as (A1 & Θ1 & Ha & _).
  destruct lift_typing_nil_instance as (Hinj & Hfun & Hagr).
  assert (Hfv : fvar_in_exp e [<=] empty).
  { intros z Hz. destruct (a_typing_fvar_binds Ha Hz) as (bd & Hb & _).
    inversion Hb. }
  assert (Hftv : ftvar_in_exp e [<=] empty).
  { pose proof (a_wf_exp_ftv_dom Hwfe) as Hb. simpl in Hb. exact Hb. }
  (* ⚠️ the theorem's mid ∀-block (S0 … V) is IMPLICIT (the §8c.46 trap):
     pass hypotheses only, each pre-asserted with an EXPLICIT type so the
     block is pinned and no fsetdec meets an evar. *)
  assert (H1 : rel_aenv (@nil (atom * atom)%type) empty
                 (@nil (atom * abind)%type) (@nil (atom * abind)%type))
    by apply rel_aenv__nil.
  assert (H2 : rel_pskl (@nil (atom * atom)%type) empty
                 pskl_hole pskl_hole)
    by apply rel_pskl__hole.
  assert (H3 : rel_exp (@nil (atom * atom)%type) empty e e)
    by (apply rel_exp_refl; clear - Hfv Hftv; fsetdec).
  assert (H7 : {{ ⊢ (@nil (atom * abind)%type) }}a) by apply a_wf_aenv__nil.
  assert (H8 : uniq (@nil (atom * abind)%type)) by apply uniq_nil.
  assert (H9 : ftvar_in_aenv (@nil (atom * abind)%type)
               [<=] ftvar_in_pskl pskl_hole ∪ fvar_in_exp e
                    ∪ ftvar_in_exp e)
    by (simpl; clear; fsetdec).
  assert (H10 : empty [<=] ftvar_in_aenv (@nil (atom * abind)%type))
    by (clear; fsetdec).
  assert (H11 : forall a, a `in` dom Θ1 ->
                a `notin` dom (@nil (atom * abind)%type) ->
                a `notin` cols_l (@nil (atom * atom)%type))
    by (intros a Hx Hy Hc; simpl in Hc; clear - Hc; fsetdec).
  assert (H12 : dom (@nil (atom * abind)%type)
                [<=] ftvar_in_pskl pskl_hole ∪ fvar_in_exp e
                     ∪ ftvar_in_exp e)
    by (simpl; clear; fsetdec).
  assert (H13 : empty ∪ cols_r (@nil (atom * atom)%type)
                [<=] ftvar_in_pskl pskl_hole ∪ fvar_in_exp e
                     ∪ ftvar_in_exp e)
    by (simpl; clear; fsetdec).
  assert (H14 : ftvar_in_pskl pskl_hole ∪ ftvar_in_exp e ∪ fvar_in_exp e
                [<=] ftvar_in_pskl pskl_hole ∪ fvar_in_exp e
                     ∪ ftvar_in_exp e)
    by (clear; fsetdec).
  assert (H15 : {{ (@nil (atom * abind)%type) ⨟ empty ⊢ₚₛ pskl_hole }}a)
    by apply a_wf_pskl__hole.
  destruct (a_typing_rel_e Ha H1 H2 H3 Hagr Hinj Hfun H7 H8 H9 H10 H11
              H12 H13 H14 H15 Hwfe a_ty_mode_compat__ti)
    as (S1 & ρe & Θ1e & Be & De & _).
  eapply e_typing_run_complete_init;
    [ exact De | exact lc_pskl_hole | exact Hlc ].
Qed.

(** The CHECK twin, against a closed well-formed [B].  The extra
    hypothesis mirrors [e_typing_run_sound_check]'s. *)
Corollary e_typing_run_complete_decl_check : forall e (B : btyp),
  {{ nil ⊢ᵉ e }}d ->
  d_wf_ptyp nil (btyp_to_ptyp B) ->
  {{ nil ⊢[ mode_tc ] e ⦂ B }}d ->
  exists r,
    e_typing_run (ftvar_in_pskl (ptyp_to_pskl (btyp_to_ptyp B))
                  ∪ fvar_in_exp e ∪ ftvar_in_exp e)
      mode_tc nil (ptyp_to_pskl (btyp_to_ptyp B)) e = Some r.
Proof.
  intros e B Hwfd HwfBd Hd.
  pose proof (d_wf_exp_to_a _ _ Hwfd) as Hwfe. simpl in Hwfe.
  pose proof (a_wf_exp_lc Hwfe) as Hlc.
  pose proof (d_wf_ptyp_to_a _ _ HwfBd) as HwfB. simpl in HwfB.
  destruct (a_typing_complete_decl_check Hwfe Hd) as (A1 & Θ1 & Ha & _).
  destruct lift_typing_nil_instance as (Hinj & Hfun & Hagr).
  assert (Hfv : fvar_in_exp e [<=] empty).
  { intros z Hz. destruct (a_typing_fvar_binds Ha Hz) as (bd & Hb & _).
    inversion Hb. }
  assert (Hftv : ftvar_in_exp e [<=] empty).
  { pose proof (a_wf_exp_ftv_dom Hwfe) as Hb. simpl in Hb. exact Hb. }
  assert (HftB : ftvar_in_pskl (ptyp_to_pskl (btyp_to_ptyp B)) [<=] empty).
  { pose proof (ftvar_ptyp_to_pskl (btyp_to_ptyp B)) as He.
    pose proof (a_wf_ptyp_ftv_dom HwfB) as Hb. simpl in Hb.
    clear - He Hb. fsetdec. }
  assert (H1 : rel_aenv (@nil (atom * atom)%type) empty
                 (@nil (atom * abind)%type) (@nil (atom * abind)%type))
    by apply rel_aenv__nil.
  assert (H2 : rel_pskl (@nil (atom * atom)%type) empty
                 (ptyp_to_pskl (btyp_to_ptyp B))
                 (ptyp_to_pskl (btyp_to_ptyp B)))
    by (apply rel_pskl_refl; clear - HftB; fsetdec).
  assert (H3 : rel_exp (@nil (atom * atom)%type) empty e e)
    by (apply rel_exp_refl; clear - Hfv Hftv; fsetdec).
  assert (H7 : {{ ⊢ (@nil (atom * abind)%type) }}a) by apply a_wf_aenv__nil.
  assert (H8 : uniq (@nil (atom * abind)%type)) by apply uniq_nil.
  assert (H9 : ftvar_in_aenv (@nil (atom * abind)%type)
               [<=] ftvar_in_pskl (ptyp_to_pskl (btyp_to_ptyp B))
                    ∪ fvar_in_exp e ∪ ftvar_in_exp e)
    by (simpl; clear; fsetdec).
  assert (H10 : empty [<=] ftvar_in_aenv (@nil (atom * abind)%type))
    by (clear; fsetdec).
  assert (H11 : forall a, a `in` dom Θ1 ->
                a `notin` dom (@nil (atom * abind)%type) ->
                a `notin` cols_l (@nil (atom * atom)%type))
    by (intros a Hx Hy Hc; simpl in Hc; clear - Hc; fsetdec).
  assert (H12 : dom (@nil (atom * abind)%type)
                [<=] ftvar_in_pskl (ptyp_to_pskl (btyp_to_ptyp B))
                     ∪ fvar_in_exp e ∪ ftvar_in_exp e)
    by (simpl; clear; fsetdec).
  assert (H13 : empty ∪ cols_r (@nil (atom * atom)%type)
                [<=] ftvar_in_pskl (ptyp_to_pskl (btyp_to_ptyp B))
                     ∪ fvar_in_exp e ∪ ftvar_in_exp e)
    by (simpl; clear; fsetdec).
  assert (H14 : ftvar_in_pskl (ptyp_to_pskl (btyp_to_ptyp B))
                ∪ ftvar_in_exp e ∪ fvar_in_exp e
                [<=] ftvar_in_pskl (ptyp_to_pskl (btyp_to_ptyp B))
                     ∪ fvar_in_exp e ∪ ftvar_in_exp e)
    by (clear; fsetdec).
  assert (H15 : {{ (@nil (atom * abind)%type) ⨟ empty ⊢ₚₛ
                  (ptyp_to_pskl (btyp_to_ptyp B)) }}a)
    by (apply a_wf_ptyp_to_wf_pskl; exact HwfB).
  destruct (a_typing_rel_e Ha H1 H2 H3 Hagr Hinj Hfun H7 H8 H9 H10 H11
              H12 H13 H14 H15 Hwfe
              (a_ty_mode_compat__tc (btyp_to_ptyp B)))
    as (S1 & ρe & Θ1e & Be & De & _).
  eapply e_typing_run_complete_init;
    [ exact De
    | apply ptyp_to_pskl_lc; eapply a_wf_ptyp_lc; exact HwfB
    | exact Hlc ].
Qed.

(* ===================================================================== *)
(*  §6  ⭐⭐⭐ DECIDABILITY OF THE PAPER'S TYPE INFERENCE                    *)
(*                                                                        *)
(*  The headline: for a closed program, "does SOME declarative type       *)
(*  exist at TI?" is decided by the extracted runner itself.  [Some r]    *)
(*  is a declarative derivation by §1's soundness; [None] refutes one by  *)
(*  §5's completeness.  This is the claim the paper's "never guess        *)
(*  polytypes out of thin air" principle promises (README §VI); with the  *)
(*  lift closed it is now stated over the paper's OWN judgement, not the  *)
(*  threaded mirror.                                                      *)
(* ===================================================================== *)

Corollary d_typing_infer_dec : forall e,
  {{ nil ⊢ᵉ e }}d ->
  sumbool (exists B : btyp, {{ nil ⊢[ mode_ti ] e ⦂ B }}d)
          (~ exists B : btyp, {{ nil ⊢[ mode_ti ] e ⦂ B }}d).
Proof.
  intros e Hwfd.
  pose proof (d_wf_exp_to_a _ _ Hwfd) as Hwfe. simpl in Hwfe.
  destruct (e_typing_run (ftvar_in_pskl pskl_hole ∪ fvar_in_exp e
              ∪ ftvar_in_exp e) mode_ti nil pskl_hole e) as [ r | ] eqn:Hrun.
  - left.
    destruct (e_typing_run_sound_infer _ _ Hwfe Hrun)
      as (_ & _ & _ & _ & ζ & _ & _ & Hdd).
    eexists. exact Hdd.
  - right. intros [B Hd].
    destruct (e_typing_run_complete_decl_infer _ _ Hwfd Hd) as [r Hr].
    rewrite Hrun in Hr. discriminate.
Qed.

(* ===================================================================== *)
(*  §7  ⭐⭐⭐ THE CERTIFIED ENTRY POINT — McTT's idiom, on the stdlib's     *)
(*  PLAIN UNION                                                           *)
(*                                                                        *)
(*  McTT's [type_check_closed] answers in [{ P } + { ~ P }]; Frost's      *)
(*  inference also PRODUCES data, so the entry point answers in the       *)
(*  stdlib's [sumor] of a [sig]: LEFT is the runner's answer [r] packaged *)
(*  with its meaning — the run equation, and the declarative typing it    *)
(*  implies — RIGHT is the proof that NO declarative type exists.  The    *)
(*  proofs erase at extraction and [ExtrOcamlBasic] maps [sig] to its     *)
(*  carrier and [sumor] to [option], so the OCaml side sees               *)
(*                                                                        *)
(*      val frost_infer : exp -> typing_result option                     *)
(*                                                                        *)
(*  — the SAME type [e_typing_run]'s answer has, but with the paper's     *)
(*  reading certified on both constructors.  The wf hypothesis is [Prop]  *)
(*  and vanishes, exactly like McTT's [user_exp] hypotheses.              *)
(*                                                                        *)
(*  ⚠️ Written in APPLICATION form ([sumor]/[sig], not [{ _ | _ } + …]):   *)
(*  the tree's meta-level substitution notations claim the [{ term …]     *)
(*  prefix (def_guess_impl.v's header records the trap; [e_typing_dec]    *)
(*  spells [sumbool] for the same reason).                                *)
(*                                                                        *)
(*  ⚙ [e_typing_run] itself stays exported unchanged — the §8 bar (diff   *)
(*  against type.ml) is its job; [frost_infer] sits BESIDE it.            *)
(* ===================================================================== *)

Definition frost_infer (e : exp) (Hwf : {{ nil ⊢ᵉ e }}d) :
  sumor
    (sig (fun r : typing_result =>
       e_typing_run (ftvar_in_pskl pskl_hole ∪ fvar_in_exp e
                     ∪ ftvar_in_exp e)
         mode_ti nil pskl_hole e = Some r /\
       exists ζ, ζ ∷ (ty_ctx r) ⊑ nil /\
         {{ nil ⊢[ mode_ti ]
            e ⦂ (ptyp_to_btyp_syn (msubst_ptyp ζ (ty_out r))) }}d))
    (~ exists B : btyp, {{ nil ⊢[ mode_ti ] e ⦂ B }}d).
Proof.
  destruct (e_typing_run
              (ftvar_in_pskl pskl_hole ∪ fvar_in_exp e ∪ ftvar_in_exp e)
              mode_ti nil pskl_hole e) as [ r | ] eqn:Hrun.
  - (* the runner answered — §1's soundness stamps the certificate *)
    apply inleft.
    (* the [eqn:] destruct rewrote the goal's runner call to [Some r],
       so the recorded equation is [eq_refl] there; [Hrun] still names
       the honest equation for the soundness call below *)
    refine (exist _ r (conj eq_refl _)).
    pose proof (d_wf_exp_to_a _ _ Hwf) as Hwfe. simpl in Hwfe.
    destruct (e_typing_run_sound_infer _ _ Hwfe Hrun)
      as (_ & _ & _ & _ & ζ & Hinc & _ & Hdd).
    exact (ex_intro _ ζ (conj Hinc Hdd)).
  - (* the runner rejected — §5's completeness stamps the certificate *)
    apply inright.
    intros [B Hd].
    destruct (e_typing_run_complete_decl_infer _ _ Hwf Hd) as [r Hr].
    rewrite Hrun in Hr. discriminate.
Defined.

(** McTT's [type_check_closed_complete], verbatim shape: a typable
    program always lands on the LEFT. *)
Lemma frost_infer_complete : forall e (Hwf : {{ nil ⊢ᵉ e }}d) (B : btyp),
  {{ nil ⊢[ mode_ti ] e ⦂ B }}d ->
  exists H', frost_infer e Hwf = inleft H'.
Proof.
  intros e Hwf B Hd.
  destruct (frost_infer e Hwf) as [ H' | Hno ];
    [ exists H'; reflexivity | exfalso; exact (Hno (ex_intro _ B Hd)) ].
Qed.
