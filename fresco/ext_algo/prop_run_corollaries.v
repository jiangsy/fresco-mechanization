(** ext_algo — ⭐ WHAT THE EXTRACTED PROGRAM PROVES, at a closed program.

    The whole chain, composed once and for all: if the RUNNER — the OCaml
    function [extraction/extracted/fresco_guess.ml] actually contains — answers
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
                           (algo/typing/prop_typing_closed.v)  corollaries: at a
                                                   flexible-free context the
                                                   decl-in-algo layer IS the
                                                   plain declarative system

    §1  inference mode — input the ghost [□]           SOUNDNESS
    §2  the entry-point exhibit: AT-Unit, end to end
    §3  the COMPLETENESS half, at the same entry point (2026-08-19)
    §4  DECIDABILITY of the THREADED relation
    §5  ⭐⭐⭐ COMPLETENESS AT THE PAPER'S JUDGEMENT — the lift, composed
    §6  ⭐⭐⭐ THE CERTIFIED ENTRY POINT ([fresco_infer], extracted)
    §7  ⭐⭐⭐ DECIDABILITY OF THE PAPER'S TYPE INFERENCE

    ⚙ THE ENTRY SUPPLY IS NOT A PARAMETER OF THE CLAIM.  Every entry-point
    statement fixes it at [entry_supply P0 e] (prop_typing.v §2) — the atoms
    the inputs already mention, which is the supply [e_typing_sound_init]
    chooses and the reason that corollary is hypothesis-free: coverage
    becomes [reflexivity] and the context is [nil], so [uniq] is [uniq_nil].
    It is also what [type.ml] does at its own entry point — start the
    counter, start the context empty.

    ⚙ §1 was SOUNDNESS ONLY when it was written: [None] meant "no rule
    applied" and was justified by nothing (§8b.7's result shape).  §3 closes
    that — the completeness ladder (campaign levels 1–8) is finished — and §4
    is the two-line consequence.

    ⚠️ §4's SCOPE NOTE, KEPT FOR HISTORY AND NOW DISCHARGED (2026-08-22).
    What §4's [None] refutes is a derivation of the THREADED relation
    [e_typing]; turning that into a refutation of the paper's own judgement
    needed the converse of the bridge ([a_typing] ⟹ [e_typing] at a covering
    supply) — §8c.3's obstruction, now built ([a_typing_rel_e], prop_lift.v
    §13).  §5 composes it with the closed-program completeness corollaries,
    §6 packages the pair as the extracted entry point, and §7 is the
    headline: decidability of the paper's own type inference. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.
From Equations Require Import Equations.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.algo_decl.def_typing.
(* [a_wf_exp] and its [{{ Θ ⊢ᵉ e }}a] notation live here, not in def_rules.v. *)
Require Import src.fresco.algo.typing.prop_soundness_pat.
Require Import src.fresco.algo.typing.prop_typing_closed.
Require Import src.fresco.algo_decl.prop_conservativity.  (* [d_wf_exp] + the nil bridges *)
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.basic.def_supply.
Require Import src.fresco.ext_algo.typing.def_typing.
Require Import src.fresco.ext_algo.typing.prop_typing.
Require Import src.fresco.ext_algo.consistency.def_consis_impl.
Require Import src.fresco.ext_algo.subtyping.def_sub_impl.
Require Import src.fresco.ext_algo.typing.def_typing_impl.
Require Import src.fresco.algo.basic.prop_inc.            (* [lc_aenv] *)
Require Import src.fresco.ext_algo.basic.prop_termination. (* [aenv_defs_mono] *)
Require Import src.fresco.ext_algo.subtyping.prop_solve_det.   (* the [swaps_*] family *)
Require Import src.fresco.ext_algo.typing.prop_typing_complete.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo.typing.prop_soundness_typing.
Require Import src.fresco.ext_algo.subtyping.prop_solve_rel.
Require Import src.fresco.ext_algo.lifting.prop_lift_context.
Require Import src.fresco.ext_algo.lifting.prop_lift.
Require Import src.fresco.ext_algo.lifting.prop_lift_typing.  (* §13, [a_typing_rel_e] *)
Require Import src.fresco.algo_decl.prop_precision.   (* [a_wf_ptyp_to_wf_pskl] *)

Open Scope fresco_e_scope.

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
  e_typing_run (entry_supply pskl_ghost e)
    mode_ti nil pskl_ghost e = Some r ->
  nil ⊴ (ty_ctx r) /\ {{ ⊢ (ty_ctx r) }}a /\ a_wf_ptyp (ty_ctx r) (ty_out r) /\
  ({{ (ty_ctx r) ⨟ empty ⊢ᵣ bskl_ghost
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
(*  §2  The entry-point exhibit: AT-Unit, end to end                      *)
(* ===================================================================== *)

(** The AT-Unit branch at infer mode, end to end, through every layer the
    runners depend on —
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

Lemma e_typing_run_complete_unit_infer : forall S0,
  e_typing_run S0 mode_ti nil pskl_ghost exp_unit
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
  {{ (entry_supply P0 e) ↝ Sd
     ⊨ nil ⊢[ m ; P0 ] e ⦂ Bd ⊣ Θd }}e ->
  lc_pskl P0 -> lc_exp e ->
  exists r,
    e_typing_run (entry_supply P0 e)
      m nil P0 e = Some r.
Proof.
  intros * Hd HP0 He.
  (* ⚙ [fsetdec] does not see through a [Definition]; the coverage
     obligation is [reflexivity]-shaped once the name is unfolded. *)
  unfold entry_supply in Hd |- *.
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
  sumbool (e_typable (entry_supply P0 e) m nil P0 e)
          (~ e_typable (entry_supply P0 e) m nil P0 e).
Proof.
  intros m P0 e HP0 He.
  unfold entry_supply.
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

(** The two corollaries' common tail: a CLOSED algorithmic derivation —
    empty context, closed pattern — lifts onto the runner's entry supply
    (prop_lift_typing.v's [a_typing_rel_e] at the empty relation), so the
    runner answers. *)
Lemma e_typing_run_complete_closed {m P e B Θ1} :
  {{ nil ⊢ᵉ e }}a ->
  {{ (@nil (atom * abind)%type) ⨟ empty ⊢ₚₛ P }}a -> lc_pskl P ->
  ftvar_in_pskl P [<=] empty -> a_ty_mode_compat m P ->
  {{ nil ⊢[ m ; P ] e ⦂ B ⊣ Θ1 }}a ->
  exists r, e_typing_run (entry_supply P e) m nil P e = Some r.
Proof.
  intros Hwfe HwfP HlcP HftP Hmod Ha.
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
  assert (H2 : rel_pskl (@nil (atom * atom)%type) empty P P)
    by (apply rel_pskl_refl; clear - HftP; fsetdec).
  assert (H3 : rel_exp (@nil (atom * atom)%type) empty e e)
    by (apply rel_exp_refl; clear - Hfv Hftv; fsetdec).
  assert (H7 : {{ ⊢ (@nil (atom * abind)%type) }}a) by apply a_wf_aenv__nil.
  assert (H8 : uniq (@nil (atom * abind)%type)) by apply uniq_nil.
  assert (H9 : ftvar_in_aenv (@nil (atom * abind)%type)
               [<=] ftvar_in_pskl P ∪ fvar_in_exp e ∪ ftvar_in_exp e)
    by (simpl; clear; fsetdec).
  assert (H10 : empty [<=] ftvar_in_aenv (@nil (atom * abind)%type))
    by (clear; fsetdec).
  assert (H11 : forall a, a `in` dom Θ1 ->
                a `notin` dom (@nil (atom * abind)%type) ->
                a `notin` cols_l (@nil (atom * atom)%type))
    by (intros a Hx Hy Hc; simpl in Hc; clear - Hc; fsetdec).
  assert (H12 : dom (@nil (atom * abind)%type)
                [<=] ftvar_in_pskl P ∪ fvar_in_exp e ∪ ftvar_in_exp e)
    by (simpl; clear; fsetdec).
  assert (H13 : empty ∪ cols_r (@nil (atom * atom)%type)
                [<=] ftvar_in_pskl P ∪ fvar_in_exp e ∪ ftvar_in_exp e)
    by (simpl; clear; fsetdec).
  assert (H14 : ftvar_in_pskl P ∪ ftvar_in_exp e ∪ fvar_in_exp e
                [<=] ftvar_in_pskl P ∪ fvar_in_exp e ∪ ftvar_in_exp e)
    by (clear; fsetdec).
  destruct (a_typing_rel_e Ha H1 H2 H3 Hagr Hinj Hfun H7 H8 H9 H10 H11
              H12 H13 H14 HwfP Hwfe Hmod)
    as (S1 & ρe & Θ1e & Be & De & _).
  exact (e_typing_run_complete_init _ _ _ _ _ _ De HlcP (a_wf_exp_lc Hwfe)).
Qed.

Corollary e_typing_run_complete_decl_infer : forall e (B : btyp),
  {{ nil ⊢ᵉ e }}d ->
  {{ nil ⊢[ mode_ti ] e ⦂ B }}d ->
  exists r,
    e_typing_run (entry_supply pskl_ghost e)
      mode_ti nil pskl_ghost e = Some r.
Proof.
  intros e B Hwfd Hd.
  (* the subject's algorithmic wf and local closure are DERIVED, not
     hypotheses: the nil bridge, then [a_wf_exp_lc] *)
  pose proof (d_wf_exp_to_a _ _ Hwfd) as Hwfe. simpl in Hwfe.
  destruct (a_typing_complete_decl_infer Hwfe Hd) as (A1 & Θ1 & Ha & _).
  assert (Hft : ftvar_in_pskl pskl_ghost [<=] empty) by (simpl; fsetdec).
  exact (e_typing_run_complete_closed Hwfe (a_wf_pskl__ghost _ _)
           lc_pskl_ghost Hft a_ty_mode_compat__ti Ha).
Qed.

(** The CHECK twin, against a closed well-formed [B]. *)
Corollary e_typing_run_complete_decl_check : forall e (B : btyp),
  {{ nil ⊢ᵉ e }}d ->
  d_wf_ptyp nil (btyp_to_ptyp B) ->
  {{ nil ⊢[ mode_tc ] e ⦂ B }}d ->
  exists r,
    e_typing_run (entry_supply (ptyp_to_pskl (btyp_to_ptyp B)) e)
      mode_tc nil (ptyp_to_pskl (btyp_to_ptyp B)) e = Some r.
Proof.
  intros e B Hwfd HwfBd Hd.
  pose proof (d_wf_exp_to_a _ _ Hwfd) as Hwfe. simpl in Hwfe.
  pose proof (d_wf_ptyp_to_a _ _ HwfBd) as HwfB. simpl in HwfB.
  destruct (a_typing_complete_decl_check Hwfe Hd) as (A1 & Θ1 & Ha & _).
  assert (HftB : ftvar_in_pskl (ptyp_to_pskl (btyp_to_ptyp B)) [<=] empty).
  { pose proof (ftvar_ptyp_to_pskl (btyp_to_ptyp B)) as He.
    pose proof (a_wf_ptyp_ftv_dom HwfB) as Hb. simpl in Hb.
    clear - He Hb. fsetdec. }
  exact (e_typing_run_complete_closed Hwfe (a_wf_ptyp_to_wf_pskl empty HwfB)
           (ptyp_to_pskl_lc (a_wf_ptyp_lc HwfB)) HftB
           (a_ty_mode_compat__tc _) Ha).
Qed.

(* ===================================================================== *)
(*  §6  ⭐⭐⭐ THE CERTIFIED ENTRY POINT — McTT's idiom, on the stdlib's     *)
(*  PLAIN UNION                                                           *)
(*                                                                        *)
(*  McTT's [type_check_closed] answers in [{ P } + { ~ P }]; Fresco's      *)
(*  inference also PRODUCES data, so the entry point answers in the       *)
(*  stdlib's [sumor] of a [sig]: LEFT is the runner's answer [r] packaged *)
(*  with its meaning — the run equation, and the declarative typing it    *)
(*  implies — RIGHT is the proof that NO declarative type exists.  The    *)
(*  proofs erase at extraction and [ExtrOcamlBasic] maps [sig] to its     *)
(*  carrier and [sumor] to [option], so the OCaml side sees               *)
(*                                                                        *)
(*      val fresco_infer : exp -> typing_result option                     *)
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
(*  against type.ml) is its job; [fresco_infer] sits BESIDE it.            *)
(* ===================================================================== *)

Definition fresco_infer (e : exp) (Hwf : {{ nil ⊢ᵉ e }}d) :
  sumor
    (sig (fun r : typing_result =>
       e_typing_run (entry_supply pskl_ghost e)
         mode_ti nil pskl_ghost e = Some r /\
       exists ζ, ζ ∷ (ty_ctx r) ⊑ nil /\
         {{ nil ⊢[ mode_ti ]
            e ⦂ (ptyp_to_btyp_syn (msubst_ptyp ζ (ty_out r))) }}d))
    (~ exists B : btyp, {{ nil ⊢[ mode_ti ] e ⦂ B }}d).
Proof.
  destruct (e_typing_run
              (entry_supply pskl_ghost e)
              mode_ti nil pskl_ghost e) as [ r | ] eqn:Hrun.
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
Lemma fresco_infer_complete : forall e (Hwf : {{ nil ⊢ᵉ e }}d) (B : btyp),
  {{ nil ⊢[ mode_ti ] e ⦂ B }}d ->
  exists H', fresco_infer e Hwf = inleft H'.
Proof.
  intros e Hwf B Hd.
  destruct (fresco_infer e Hwf) as [ H' | Hno ];
    [ exists H'; reflexivity | exfalso; exact (Hno (ex_intro _ B Hd)) ].
Qed.

(* ===================================================================== *)
(*  §7  ⭐⭐⭐ DECIDABILITY OF THE PAPER'S TYPE INFERENCE                    *)
(*                                                                        *)
(*  The headline, and now a THREE-LINE consequence of §6: forget the      *)
(*  entry point's payload and keep the disjunction.  For a closed,        *)
(*  declaratively well-formed program, "does SOME declarative type exist  *)
(*  at TI?" is decided by the extracted runner itself.  This is the claim *)
(*  the paper's "never guess polytypes out of thin air" principle         *)
(*  promises (README §VI); with the lift closed it is stated over the     *)
(*  paper's OWN judgement, not the threaded mirror.                       *)
(* ===================================================================== *)

Corollary d_typing_infer_dec : forall e,
  {{ nil ⊢ᵉ e }}d ->
  sumbool (exists B : btyp, {{ nil ⊢[ mode_ti ] e ⦂ B }}d)
          (~ exists B : btyp, {{ nil ⊢[ mode_ti ] e ⦂ B }}d).
Proof.
  intros e Hwf.
  (* ⚙ the branch CHOICE first: [sumbool] is in [Set], so the [Prop]
     payload may only be opened once the goal is a [Prop] again. *)
  destruct (fresco_infer e Hwf) as [ [r Hfact] | Hno ];
    [ left | right; exact Hno ].
  destruct Hfact as [_ [ζ [_ Hdd]]].
  exists (ptyp_to_btyp_syn (msubst_ptyp ζ (ty_out r))). exact Hdd.
Qed.
