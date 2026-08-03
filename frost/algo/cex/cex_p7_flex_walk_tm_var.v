(** ⚠️ [thm:complete-subtyping] IS FALSE FOR THE RULE SET AS PRINTED — the
    flexible SUBTYPING walk has NO rule for a TERM-VARIABLE head.

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
    (iii)[tm_var_no_run] — but NO algorithmic run exists: at an FN mode the
         only [a_sub] rule whose subject is a bare variable is FlexMono, and
         the walk it hands off to is stuck on the term entry immediately
         ([a_sub_flex_stuck_at_tm_var]).

    ⭐⭐⭐ AND IT IS NOT AN EXOTIC CONFIGURATION — THE REFERENCE
    IMPLEMENTATION CRASHES ON IT.  [a_typing__abs] pushes the lambda binder
    ABOVE the flexibles [a_guess_mono] just invented
    ([(x ~ abind_var_typ A) ++ αs ++ Θ1], algo/def_extra.v), and
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

    ⚙ The impl reaches [failwith] rather than [Errors.type_mismatch] because
    its contexts also carry [Marker] / [Lock] entries, which `assign` skips
    ([U-Assign-SkipOthers], type.ml:386-390) and `sub_flex` does not.  Same
    omission, one entry sort further out than the paper's [x : P].

    THE REPAIR is Flex-SkipTmVar in the paper's own idiom, mirroring
    Assign-SkipTmVar.  It is NOT applied here: it is a change to the paper's
    rule set with a tree-wide blast radius (see docs/PAPER-GAPS.md).  Until
    the authors decide, P7c's flex half carries the explicit premise
    [a_sub_flex_walkable Θ0] (prop_sub_complete_dispatch.v §6/§7). *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_extra.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decl_algo_sub.
Require Import src.frost.algo.def_decl_algo_sub_hyg.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.prop_sub_msubst_equiv.
Require Import src.frost.def_tags.
Require Import src.frost.algo.prop_consis_sound.

Set Implicit Arguments.

(* ===================================================================== *)
(*  §1  THE WALK IS STUCK — no rule matches a term-variable head           *)
(* ===================================================================== *)

Lemma a_sub_flex_stuck_at_tm_var : forall NM M P0 Θ0 Ξ α A Θ1 x B,
  ~ a_sub_flex NM M P0 ((x ~ abind_var_typ B) ++ Θ0) Ξ α A Θ1.
Proof. intros * Hrun; inversion Hrun. Qed.

Lemma a_sub_flex_stuck_at_tm_skl : forall NM M P0 Θ0 Ξ α A Θ1 x P,
  ~ a_sub_flex NM M P0 ((x ~ abind_var_skl P) ++ Θ0) Ξ α A Θ1.
Proof. intros * Hrun; inversion Hrun. Qed.

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
  a_wf_aenv Θ0w /\
  Θ0w ⨟ empty ⊢ₚₛᵃ P0w /\
  Θ0w ⨟ empty ⊢ₚₛᵃ Pw /\
  a_sk_mode_compat (mode_fn mode_ti) P0w.
Proof.
  unfold Θ0w, P0w, Pw. repeat split.
  - apply a_wf_aenv__var_typ;
      [ simpl; clear - Hxα; fsetdec
      | apply a_wf_ptyp__unit
      | apply a_wf_aenv__flex; [ simpl; clear; fsetdec | apply a_wf_aenv__nil ] ].
  - apply a_wf_pskl__arrow; apply a_wf_pskl__hole.
  - apply a_wf_pskl__var. right. right. left.
    unfold binds; simpl; right; left; reflexivity.
  - apply a_sk_mode_compat__fn. apply a_sk_mode_compat__ti.
Qed.

(* --------------------------------------------------------------------- *)
(*  (ii) a SOLUTION exists — every hypothesis of [sub_complete_concl]      *)
(* --------------------------------------------------------------------- *)

(** ⚙ [repeat split] would CLOSE the reflexive [⌊Rw⌋ˢ = Pw] goal and silently
    shift every bullet after it, so the solution's seven components are
    separate lemmas and the bundle below just pairs them up. *)

Lemma tm_var_wf_target : a_wf_aenv Θw.
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

Lemma tm_var_slack : Θw ⊢ R'w ≡ᵘ (msubst_uskl_syn κw Rw).
Proof.
  unfold R'w, Rw, κw. simpl.
  destruct (α == α) as [_ | Hne]; [ | exfalso; apply Hne; reflexivity ].
  simpl. apply a_uskl_tyequiv_refl. apply lc_uskl_arrow; apply lc_uskl_unit.
Qed.

Lemma tm_var_join :
  ad_pat_sub_gv 1 a_sub_mode_sk (mode_fn mode_ti) empty Θw R'w Qw.
Proof.
  unfold R'w, Qw.
  eapply ad_pat_sub_gv__arrow with (Ψ1 := empty) (Ψ2 := empty);
    [ apply ad_pat_consis__unit; clear; fsetdec
    | simpl; apply ad_refine_pskl__unit
    | apply ad_pat_sub_gv__infer;
        [ clear; fsetdec
        | apply ad_pat_consis__unit; clear; fsetdec
        | apply is_sskl__unit
        | simpl; apply ad_refine_pskl__unit ]
    | clear; fsetdec ].
Qed.

Lemma tm_var_wf_counterpart : Θw ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Qw).
Proof. unfold Qw. simpl. apply a_wf_pskl__arrow; apply a_wf_pskl__unit. Qed.

Lemma tm_var_fill :
  ad_refine_syn_f empty Θw empty (pskl_to_bskl_inh (msubst_pskl κw P0w)) Qw.
Proof.
    unfold P0w, Qw, κw. simpl.
    apply ad_refine_syn_f__arrow;
      (change bskl_unit with (pskl_to_bskl_syn pskl_unit);
       apply ad_refine_syn_f__hole;
         [ clear; fsetdec | apply a_wf_pskl__unit ]).
Qed.

(* --------------------------------------------------------------------- *)
(*  (iii) …and yet NO algorithmic run exists                              *)
(* --------------------------------------------------------------------- *)

Lemma tm_var_no_run :
  ~ (exists P1 Θ1, a_sub a_sub_mode_sk (mode_fn mode_ti) P0w Θ0w Pw P1 Θ1).
Proof.
  intros [P1 [Θ1 Hrun]].
  unfold Pw, Θ0w in Hrun.
  apply a_sub_var_subject_fn_is_flex_mono in Hrun.
  eapply a_sub_flex_stuck_at_tm_var; exact Hrun.
Qed.

(** ⭐ THE HEADLINE.  The problem is a problem, it HAS a solution, and the
    algorithm has NO run — which is exactly the negation of
    [thm:complete-subtyping] for the rule set as printed. *)
Theorem complete_subtyping_false_at_a_term_variable_head :
  (* problem *)
  (a_wf_aenv Θ0w /\ Θ0w ⨟ empty ⊢ₚₛᵃ P0w /\ Θ0w ⨟ empty ⊢ₚₛᵃ Pw /\
   a_sk_mode_compat (mode_fn mode_ti) P0w)
  /\
  (* solution *)
  (a_wf_aenv Θw /\ ⌊ Rw ⌋ˢ = Pw /\ κw ∷ Θ0w ⊑ Θw /\
   Θw ⊢ R'w ≡ᵘ (msubst_uskl_syn κw Rw) /\
   ad_pat_sub_gv 1 a_sub_mode_sk (mode_fn mode_ti) empty Θw R'w Qw /\
   ad_refine_syn_f empty Θw empty
     (pskl_to_bskl_inh (msubst_pskl κw P0w)) Qw /\
   Θw ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Qw))
  /\
  (* …but no run *)
  ~ (exists P1 Θ1, a_sub a_sub_mode_sk (mode_fn mode_ti) P0w Θ0w Pw P1 Θ1).
Proof.
  split; [ exact tm_var_problem_is_a_problem | ].
  split; [ | exact tm_var_no_run ].
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

Print Assumptions complete_subtyping_false_at_a_term_variable_head.
Print Assumptions a_sub_flex_stuck_at_tm_var.
