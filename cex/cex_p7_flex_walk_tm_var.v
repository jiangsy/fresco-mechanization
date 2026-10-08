(** ⚠️ [thm:complete-subtyping] IS FALSE FOR THE RULE SET AS PRINTED — the
    flexible SUBTYPING walk has NO rule for a TERM-VARIABLE head.

    ⭐ REPAIRED 2026-08-03: [a_sub_flex__skip_tm_var] / [__skip_tm_skl] are now
    in algo/def_rules.v (with decorated mirrors in algo/def_decorated.v),
    verbatim mirrors of the twin walk's [Assign-SkipTmVar].  This file is
    stated so that it survives the repair and keeps recording WHY the rules
    are needed: §1 shows the new rule is the ONLY one that fires at a term
    head, and the witness below is a solvable problem EVERY run of which goes
    through it — so with the five printed rules it has no run at all.

    [fig:alg-subtyping]'s second box (full-algo-spec.tex:883-912) has exactly
    five rules — Flex-Solve / Flex-Assign / Flex-Depend / Flex-Skip /
    Flex-SkipRigid — and every one of them matches a TYPE-variable entry.
    None matches a term entry [x : P].  The paper's TWIN walk, the assignment
    walk of [fig:alg-consistency], DOES have the corresponding rule
    (Assign-SkipTmVar, full-algo-spec.tex:1791; here [a_assign__skip_tm_var] /
    [a_assign__skip_tm_skl]), so the omission is almost certainly a typo — but
    as printed it makes the walk STUCK, and completeness demands a run.

    ⭐ WHAT IS MACHINE-CHECKED HERE, at the smallest possible witness

        Θ0 = x : (), α̂          P0 = ◇ → ◇         P = α̂        N = SK
        M  = FN TI              κ  = α̂ ↦ () → ()   Θ  = x : ()
        R' = () → ()            Q  = () → ()       Ψ  = ∅

    (i)  [tm_var_problem_is_a_problem] — the completeness theorem's PROBLEM
         side holds: Θ0 is well formed, P0 and P are well formed in it, and
         [skmod[SK]{P0}{FN TI}].
    (ii) [tm_var_solution_exists] — a SOLUTION exists: the increase, the
         (leaf-valid) join, the fill, and the counterpart's external wf.
         So every hypothesis of [sub_complete_concl] is satisfied.
    (iii)[tm_var_run_must_use_skip_tm_var] — and EVERY run goes through the
         added rule: at an FN mode the only [a_sub] rule whose subject is a
         bare variable is FlexMono, and at the term entry the walk has exactly
         one applicable rule ([a_sub_flex_tm_var_head_is_skip_tm_var]).  Take
         the rule away and the run is gone.

    ⭐⭐⭐ AND IT IS NOT AN EXOTIC CONFIGURATION — THE REFERENCE
    IMPLEMENTATION CRASHES ON IT.  [a_typing__abs] pushes the lambda binder
    ABOVE the flexibles [a_guess_mono] just invented
    ([(x ~ abind_var_typ A) ++ αs ++ Θ1], algo/def_rules.v), and
    [a_typing__var] hands that very flexible to SUBTYPING as the subject
    ([a_typing__var]'s premise is at [ptyp_to_pskl A] for [x : A]), at an FN
    mode when the variable is applied ([a_typing__app]).  So this context is
    what `fun x -> x 1` builds, and the walk's FIRST step is across the binder.
    Run against paper/artifact/implementation (met.exe --debug):

        let f = fun x -> x 1                   (* OCaml's  fun x -> x 1 *)
        - I-Abs
        -- I-App
        --- PI-Int  ---- SI-UnivGhostR
        --- I-Var
        ---- SI-FlexMono                       ← subtyping enters the walk
        Fatal error: exception Failure("broom_flex_poly: should not happen")

    `fun g -> fun y -> g y` and `fun g y -> g (g y)` crash identically, as does
    every literal argument.  `fun x -> x` is fine (no application, so no
    FN-mode subtyping on the flexible), and so is any version where the
    applied variable's type is CONCRETE (give `f` a `val` signature) — the
    trigger is exactly "apply a lambda-bound variable whose type is still an
    unsolved flexible".
    [tm_var_context_is_the_lambda_shape] records the shape correspondence.

    ⭐ THE GAP IS EXACTLY "CHECKING WORKS, INFERENCE DOES NOT".  The spec DOES
    type these terms: `fun x -> x 1` CHECKS against `(int -> int) -> int` and
    against `forall b . [] ((int -> b) -> b)` (and is then usable at two
    result types), and `fun g y -> g y` checks against
    `forall a b . [] ((a -> b) -> a -> b)`.  Checking never reaches the walk,
    because there `x`'s type is CONCRETE.  So the missing rule costs exactly
    the INFERENCE of any term that applies a lambda-bound variable.

    ⚠️ But inference is NOT checking-minus-the-annotation.  Declarative [Abs]
    (full-decl-spec.tex:210) guesses the argument type in an INHERITED
    position, [inh{A} → bid{B}], and the paper says why (declarative.tex:577):
    "We require the argument type to be inherited to avoid guessing
    quantifiers without restricting it to monotypes".  So inference derives
    [(unit → τ) → τ] for each MONOTYPE τ — an open family, no quantifier
    (there is no Gen rule; the [∀ᾱ] prefix comes only from [AbsCheck], in
    CHECKING mode).  The algorithm represents the family by the unsolved
    flexible, [(unit → γ̂) → γ̂], and every solution instantiates γ̂ with a
    MONOTYPE ([a_inc__flex]'s [mono_ptyp] premise).  [∀b. (unit → b) → b] is a
    different, stronger statement, reachable only by annotation.

    ⚙ The impl reaches [failwith] rather than [Errors.type_mismatch] because
    its contexts also carry [Marker] / [Lock] entries, which `assign` skips
    ([U-Assign-SkipOthers], type.ml:386-390) and `sub_flex` does not.  Same
    omission, one entry sort further out than the paper's [x : P].

    THE REPAIR, as landed: two rules on [a_sub_flex] and two on
    [a_subtag_flex], plus the mirroring cases in the three mutual inductions
    over the pair (prop_sub_sound.v's soundness bundle, prop_soundness_sub.v's
    decoration bundle, prop_swap.v's equivariance) and two new P7a rows.  The
    one thing the rules do NOT carry, and the twin walk's does not either, is
    a freshness premise for [P0]: a term entry is never [a_binds_tvar], so
    [x ∉ ftv P0] is DERIVED from wf + uniq at each consumer.
    See docs/PAPER-GAPS.md. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.def_shapes.
Require Import src.fresco.coercions.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.def_meta.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.algo_decl.def_subtyping.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo.sub.prop_sub_msubst_equiv.
Require Import src.fresco.algo.consis.prop_soundness_consis.

Set Implicit Arguments.

(* ===================================================================== *)
(*  §1  THE WALK IS STUCK — no rule matches a term-variable head           *)
(* ===================================================================== *)

(** ⭐ THE FIVE-RULE SET IS INCOMPLETE, stated so that it survives the repair:
    at a term-variable head the ONLY rule that fires is [Flex-SkipTmVar].
    Delete it — i.e. go back to fig:alg-subtyping as printed — and the walk
    has no rule at all there. *)
Lemma a_sub_flex_tm_var_head_is_skip_tm_var :
  forall NM M P0 Θ0 Ξ α A Θ1 x B,
  a_sub_flex NM M P0 ((x ~ abind_var_typ B) ++ Θ0) Ξ α A Θ1 ->
  exists Θ1', Θ1 = (x ~ abind_var_typ B) ++ Θ1'
              /\ x `notin` dom Θ1'
              /\ a_sub_flex NM M P0 Θ0 Ξ α A Θ1'.
Proof. intros * Hrun; inversion Hrun; subst; eauto. Qed.

Lemma a_sub_flex_tm_skl_head_is_skip_tm_skl :
  forall NM M P0 Θ0 Ξ α A Θ1 x P,
  a_sub_flex NM M P0 ((x ~ abind_var_skl P) ++ Θ0) Ξ α A Θ1 ->
  exists Θ1', Θ1 = (x ~ abind_var_skl P) ++ Θ1'
              /\ x `notin` dom Θ1'
              /\ a_sub_flex NM M P0 Θ0 Ξ α A Θ1'.
Proof. intros * Hrun; inversion Hrun; subst; eauto. Qed.

(** …and at an FN mode a bare-variable subject has nowhere else to go. *)
Lemma a_sub_var_subject_fn_is_flex_mono : forall NM M P0 Θ0 α A Θ1,
  a_sub NM (mode_fn M) P0 Θ0 (pskl_var_f α) A Θ1 ->
  a_sub_flex NM M P0 Θ0 nil α A Θ1.
Proof. intros * Hrun; inversion Hrun; subst; assumption. Qed.

(* ===================================================================== *)
(*  §2  THE WITNESS                                                       *)
(* ===================================================================== *)

Section TmVarWitness.

Variable x α : atom.
Hypothesis Hxα : x <> α.

(** Θ0 = α̂ , x : ()  (list head = the paper's RIGHTMOST / most recent entry) *)
Definition Θ0w : aenv :=
  (x ~ abind_var_typ ptyp_unit) ++ (α ~ abind_flex_mono) ++ nil.

Definition P0w : pskl := pskl_arrow pskl_hole pskl_hole.   (* ◇ → ◇ *)
Definition Pw  : pskl := pskl_var_f α.                     (* the subject α̂ *)
Definition Rw  : uskl := uskl_var_f α.

Definition κw  : metasubst :=
  (α, ptyp_arrow ptyp_unit ptyp_unit) :: nil.              (* α̂ ↦ () → () *)
Definition Θw  : aenv := (x ~ abind_var_typ ptyp_unit) ++ nil.

Definition R'w : uskl := uskl_arrow uskl_unit uskl_unit.
Definition Qw  : bskl := bskl_arrow bskl_unit bskl_unit.

(* --------------------------------------------------------------------- *)
(*  (i) the PROBLEM side of [thm:complete-subtyping]                      *)
(* --------------------------------------------------------------------- *)

Lemma tm_var_problem_is_a_problem :
  {{ ⊢ Θ0w }}a /\
  {{ Θ0w ⨟ empty ⊢ₚₛ P0w }}a /\
  {{ Θ0w ⨟ empty ⊢ₚₛ Pw }}a /\
  a_sk_mode_compat (mode_fn mode_ti) P0w.
Proof.
  unfold Θ0w, P0w, Pw. repeat split.
  - apply a_wf_aenv__var_typ;
      [ simpl; clear - Hxα; fsetdec
      | apply a_wf_ptyp__unit
      | apply a_wf_aenv__flex; [ simpl; clear; fsetdec | apply a_wf_aenv__nil ] ].
  - apply a_wf_pskl__arrow; apply a_wf_pskl__hole.
  - apply a_wf_pskl__var. right. left.
    unfold binds; simpl; right; left; reflexivity.
  - apply a_sk_mode_compat__fn. apply a_sk_mode_compat__ti.
Qed.

(* --------------------------------------------------------------------- *)
(*  (ii) a SOLUTION exists — every hypothesis of [sub_complete_concl]      *)
(* --------------------------------------------------------------------- *)

(** ⚙ [repeat split] would CLOSE the reflexive [⌊Rw⌋ˢ = Pw] goal and silently
    shift every bullet after it, so the solution's seven components are
    separate lemmas and the bundle below just pairs them up. *)

Lemma tm_var_wf_target : {{ ⊢ Θw }}a.
Proof.
  unfold Θw. apply a_wf_aenv__var_typ;
    [ simpl; clear; fsetdec | apply a_wf_ptyp__unit | apply a_wf_aenv__nil ].
Qed.

Lemma tm_var_erase : ⌊ Rw ⌋ˢ = Pw.
Proof. reflexivity. Qed.

Lemma tm_var_inc : κw ∷ Θ0w ⊑ Θw.
Proof.
  unfold κw, Θ0w, Θw.
  change ((x ~ abind_var_typ ptyp_unit) ++ nil)
    with (nil ++ (x ~ abind_var_typ ptyp_unit) ++ (@nil (atom * abind))).
  apply a_inc__var;
    [ apply a_inc__flex;
        [ apply a_inc__empty; apply a_suffix__nil
        | apply a_wf_ptyp__arrow; apply a_wf_ptyp__unit
        | apply mono_ptyp__arrow; apply mono_ptyp__unit ]
    | simpl; apply a_tyequiv__refl; apply lc_ptyp_unit
    | apply a_suffix__nil ].
Qed.

Lemma tm_var_slack : {{ Θw ⊢ R'w ≡ᵘ (msubst_uskl_syn κw Rw) }}a.
Proof.
  unfold R'w, Rw, κw. simpl.
  destruct (α == α) as [_ | Hne]; [ | exfalso; apply Hne; reflexivity ].
  simpl. apply a_uskl_tyequiv_refl. apply lc_uskl_arrow; apply lc_uskl_unit.
Qed.

Lemma tm_var_join :
  ad_pat_sub_fuel 1 a_sub_mode_sk (mode_fn mode_ti) empty Θw R'w Qw.
Proof.
  unfold R'w, Qw.
  eapply ad_pat_sub_fuel__arrow with (Ψ1 := empty) (Ψ2 := empty);
    [ split;
        [ apply ad_pat_consis__unit; clear; fsetdec
        | simpl; apply ad_refine_pskl__unit ]
    | apply ad_pat_sub_fuel__infer;
        [ clear; fsetdec
        | split;
            [ apply ad_pat_consis__unit; clear; fsetdec
            | simpl; apply ad_refine_pskl__unit ]
        | apply is_sskl__unit ]
    | clear; fsetdec ].
Qed.

Lemma tm_var_wf_counterpart : {{ Θw ⨟ empty ⊢ₚₛ (bskl_to_pskl Qw) }}a.
Proof. unfold Qw. simpl. apply a_wf_pskl__arrow; apply a_wf_pskl__unit. Qed.

Lemma tm_var_fill :
  ad_refine_syn_f empty Θw empty (pskl_to_bskl_inh (msubst_pskl κw P0w)) Qw.
Proof.
    unfold P0w, Qw, κw. simpl.
    apply ad_refine_syn_f__arrow;
      (change bskl_unit with (pskl_to_bskl_syn pskl_unit);
       apply ad_refine_syn_f__hole;
         [ clear; fsetdec | clear; fsetdec ]).
Qed.

(* --------------------------------------------------------------------- *)
(*  (iii) …and yet NO algorithmic run exists                              *)
(* --------------------------------------------------------------------- *)

(** …and EVERY run at this configuration goes through [Flex-SkipTmVar]: the
    subject is a bare variable at an FN mode, so the main judgment can only
    fire FlexMono, and the walk then meets the term entry, where only the new
    rule applies.  Delete the rule and this solvable problem has NO run — that
    is the failure of [thm:complete-subtyping] for the printed rule set. *)
Lemma tm_var_run_must_use_skip_tm_var :
  forall P1 Θ1, a_sub a_sub_mode_sk (mode_fn mode_ti) P0w Θ0w Pw P1 Θ1 ->
  exists Θ1',
    Θ1 = (x ~ abind_var_typ ptyp_unit) ++ Θ1'
    /\ a_sub_flex a_sub_mode_sk mode_ti P0w ((α ~ abind_flex_mono) ++ nil)
         nil α P1 Θ1'.
Proof.
  intros P1 Θ1 Hrun. unfold Pw, Θ0w in Hrun.
  apply a_sub_var_subject_fn_is_flex_mono in Hrun.
  destruct (a_sub_flex_tm_var_head_is_skip_tm_var Hrun)
    as [Θ1' [-> [_ Hwalk]]].
  exists Θ1'. split; [ reflexivity | exact Hwalk ].
Qed.

(** ⭐ THE HEADLINE.  The problem is a problem, it HAS a solution, and every
    run of it goes through [Flex-SkipTmVar] — so WITHOUT that rule (i.e. for
    fig:alg-subtyping's five rules as printed) there is no run at all, which
    is exactly the negation of [thm:complete-subtyping]. *)
Theorem complete_subtyping_needs_flex_skip_tm_var :
  (* problem *)
  ({{ ⊢ Θ0w }}a /\ {{ Θ0w ⨟ empty ⊢ₚₛ P0w }}a /\ {{ Θ0w ⨟ empty ⊢ₚₛ Pw }}a /\
   a_sk_mode_compat (mode_fn mode_ti) P0w)
  /\
  (* solution *)
  ({{ ⊢ Θw }}a /\ ⌊ Rw ⌋ˢ = Pw /\ κw ∷ Θ0w ⊑ Θw /\
   {{ Θw ⊢ R'w ≡ᵘ (msubst_uskl_syn κw Rw) }}a /\
   ad_pat_sub_fuel 1 a_sub_mode_sk (mode_fn mode_ti) empty Θw R'w Qw /\
   ad_refine_syn_f empty Θw empty
     (pskl_to_bskl_inh (msubst_pskl κw P0w)) Qw /\
   {{ Θw ⨟ empty ⊢ₚₛ (bskl_to_pskl Qw) }}a)
  /\
  (* …and every run of it uses the rule the paper's figure omits *)
  (forall P1 Θ1, a_sub a_sub_mode_sk (mode_fn mode_ti) P0w Θ0w Pw P1 Θ1 ->
     exists Θ1',
       Θ1 = (x ~ abind_var_typ ptyp_unit) ++ Θ1'
       /\ a_sub_flex a_sub_mode_sk mode_ti P0w ((α ~ abind_flex_mono) ++ nil)
            nil α P1 Θ1').
Proof.
  split; [ exact tm_var_problem_is_a_problem | ].
  split; [ | exact tm_var_run_must_use_skip_tm_var ].
  split; [ exact tm_var_wf_target | ].
  split; [ exact tm_var_erase | ].
  split; [ exact tm_var_inc | ].
  split; [ exact tm_var_slack | ].
  split; [ exact tm_var_join | ].
  split; [ exact tm_var_fill | exact tm_var_wf_counterpart ].
Qed.

(** ⭐⭐ AND THE SHAPE IS THE ORDINARY ONE.  [a_typing__abs] pushes the lambda
    binder ABOVE the flexibles [a_guess_mono] just invented, so the context in
    a lambda body has exactly [Θ0w]'s shape: a term entry, then the guessed
    flexible.  [a_typing__var] then hands that flexible to SUBTYPING as the
    subject, and [a_typing__app] does it at an FN mode.  So `\x. x ()` walks
    across a term variable on its very first step. *)
Lemma tm_var_context_is_the_lambda_shape :
  Θ0w = (x ~ abind_var_typ ptyp_unit) ++ (α ~ abind_flex_mono) ++ nil.
Proof. reflexivity. Qed.

End TmVarWitness.

