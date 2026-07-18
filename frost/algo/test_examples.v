(** Acceptance tests: worked examples from the paper's appendix benchmark
    (fig:comparison-table-QL / fig:comparison-table-new, appendix
    "Comparison of Type Systems for FCP"), run against the algorithmic
    rules — an ENCODING CHECK that the mechanized rules accept the
    programs the paper claims Frost accepts.

    Encoding conventions (the calculus has only [1], [→], [∀]):
    - [Int]/[Bool] are RIGID type variables bound [abind_tvar] in the
      library context [Θlib];
    - [Int × Bool] is Church-encoded ([∀c.(Int→Bool→c)→c]), matching the
      paper's "Ch." column;
    - library functions ([id], [choose], [poly], …,
      fig:function-signatures) are term constants bound [abind_var_typ]
      in [Θlib].

    Each test constructs the full algorithmic derivation
    [Θlib ⊢ₐ[TI;□] e ⦂ B ⊣ Θ'] — with the CONCRETE result type and
    output context, so the tests also pin down what the algorithm
    computes, not just acceptance.  Rejected examples (A8, C1a, E2a, …)
    are not testable this way (non-derivability needs a decidability
    argument), so only accepted ones appear.

    Covered: A1, A2, A4, A5, A10a, A10b, C2, E2b — together they
    exercise AT-Abs/AT-AbsAnno + split/guess^TY, AP-Var/AP-AbsCheck,
    AT-AbsCheck step/base, ForallL + look/constraint-solving/guess
    (both the ghost-input and rigid-input paths), ForallR, Check/Infer,
    the flex machinery (fresh α̂→β̂ guesses, Flex-Flex unification
    α̂ := β̂), and consistency incl. ForallSyn/ForallInh/UnivGhostR/
    Ghost/GhostR/Flex.
    Deferred (need more encoding plumbing, not blocked): the List-based
    rows (A3, A9, B*, E4, F*; Church lists work but each derivation is
    large), the pair-CONSTRUCTOR rows (A11, C1b/C1c, F4/F5: [(e1,e2)]
    must be encoded through the [pair] constant, nesting three apps),
    and the freeze rows (E3b, E7, F2, F4, F7, F11b: same app-nesting
    plus AP-Freeze/AT-Freeze). *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.ltac_utils.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.

(* ===================================================================== *)
(*  Tactic kit                                                            *)
(* ===================================================================== *)

(** Compute concrete opens / coercions in the goal. *)
Ltac simpl_open :=
  unfold open_exp_wrt_exp, open_pskl_wrt_pskl, open_ptyp_wrt_ptyp;
  simpl.

(** Discharge [lc_*] / [guarded_pskl] side conditions on concrete
    (closed) syntax. *)
Ltac crush_lc :=
  repeat match goal with
  | |- guarded_pskl _ => constructor
  | |- lc_pskl (pskl_all_syn _) =>
      apply lc_pskl_all_syn; intros ?; simpl_open
  | |- lc_pskl _ => constructor
  end.

(** [a_non_flex Θ P] for a concrete non-variable [P]. *)
Ltac crush_non_flex :=
  split; [ crush_lc | let H := fresh in intro H; inversion H ].

(** [binds x b Θ] on a concrete context: membership. *)
Ltac crush_binds :=
  unfold binds; simpl;
  first [ tauto | repeat (first [ left; reflexivity | right ]) ].

(** [a_binds_tvar X Θ] (rigid / flex / defined flex). *)
Ltac crush_btvar :=
  unfold a_binds_tvar;
  first [ left; solve [ crush_binds ]
        | right; left; solve [ crush_binds ]
        | right; right; eexists; solve [ crush_binds ] ].

(** [a_wf_pskl Θ P] on concrete syntax. *)
Ltac crush_wf :=
  repeat (first [ apply a_wf_pskl__arrow
                | apply a_wf_pskl__unit
                | apply a_wf_pskl__hole
                | apply a_wf_pskl__tophole
                | apply a_wf_pskl__var; crush_btvar
                | eapply a_wf_pskl__all with (L := {});
                  intros ? _; simpl_open
                (* disciplined twin (ForallL's instantiation premise) *)
                | apply ad_wf_pskl__arrow
                | apply ad_wf_pskl__unit
                | apply ad_wf_pskl__hole
                | apply ad_wf_pskl__tophole; [ crush_lc | ]
                | apply ad_wf_pskl__var;
                  first [ left; fsetdec | right; crush_btvar ]
                | eapply ad_wf_pskl__all with (L := {});
                  intros ? _; simpl_open ]).

Section BenchmarkExamples.

(* Rigid base types: Int, Bool. *)
Variables aInt aBool : atom.
(* Library term constants. *)
Variables x_id x_choose x_auto x_poly x_r : atom.
(* Fresh flexible variables consumed by runs that guess monotypes.
   The relations do not police freshness of guessed names themselves
   (cf. the NB at [a_guess_mono]); distinctness is all the derivations
   below need. *)
Variables fa fb : atom.
Hypothesis Hfafb : fa <> fb.

Notation tInt := (ptyp_var_f aInt).
Notation tBool := (ptyp_var_f aBool).
Notation b0 := (ptyp_var_b 0).

(* fig:function-signatures *)
Definition σ_id := ptyp_all (ptyp_arrow b0 b0).                (* ∀a.a→a *)
Definition σ_choose :=
  ptyp_all (ptyp_arrow b0 (ptyp_arrow b0 b0)).                 (* ∀a.a→a→a *)
Definition σ_auto := ptyp_arrow σ_id σ_id.                     (* σid→σid *)
Definition σ_prodIB :=                                         (* Int×Bool, Church *)
  ptyp_all (ptyp_arrow (ptyp_arrow tInt (ptyp_arrow tBool b0)) b0).
Definition σ_poly := ptyp_arrow σ_id σ_prodIB.
Definition σ_r :=                                              (* (∀a.a→∀b.b→b)→Int *)
  ptyp_arrow (ptyp_all (ptyp_arrow b0 (ptyp_all (ptyp_arrow b0 b0)))) tInt.

Definition Θlib : aenv :=
  (x_id ~ abind_var_typ σ_id) ++
  (x_choose ~ abind_var_typ σ_choose) ++
  (x_auto ~ abind_var_typ σ_auto) ++
  (x_poly ~ abind_var_typ σ_poly) ++
  (x_r ~ abind_var_typ σ_r) ++
  (aInt ~ abind_tvar) ++
  (aBool ~ abind_tvar) ++ nil.

(* The freshness the relations now police (the ForallL prose-completion):
   guessed names must avoid the ambient context. *)
Hypothesis Hfa_lib : fa `notin` dom Θlib.
Hypothesis Hfb_lib : fb `notin` dom Θlib.
Hypothesis HΘlib_uniq : uniq Θlib.

(* Discharge the ForallL freshness premise [uniq (Ξ ++ Θ0)]: peel the
   fresh entries structurally, close the ambient tail by assumption. *)
Ltac crush_uniq :=
  first [ assumption
        | simpl_env;
          first [ assumption
                | repeat (first [ assumption | apply uniq_push ]);
                  simpl_env; fsetdec ] ].

(* ===================================================================== *)
(*  Shared sub-derivations                                                *)
(* ===================================================================== *)

(** Skeleton inference of a [σ_id]-typed variable in checking mode with
    no input skeleton: [Θ ⊢ₐ[TC;□] x ⇨ ⊤.(□→□) ⊣ Θ]
    (ForallL instantiates [a := □], then UnivGhostR guards the result). *)
Lemma pat_var_sigid : forall Θ x,
  uniq Θ ->
  binds x (abind_var_typ σ_id) Θ ->
  Θ ⊢ₐ[ mode_tc ; pskl_hole ] (exp_var_f x)
    ⇨ (pskl_tophole (pskl_arrow pskl_hole pskl_hole)) ⊣ Θ.
Proof.
  intros Θ x Hu Hb.
  eapply a_pat__var; [ exact Hb | ].
  unfold σ_id; simpl.
  eapply a_sub__forall_l with (L := {}) (Ξ := nil) (P1 := pskl_hole).
  - discriminate.
  - right; reflexivity.
  - intros α _.
    eapply a_extract__solve with (Ξ := nil) (C := nil) (Q := pskl_hole).
    + simpl_open. apply a_looksub__vacuous.
    + apply a_solve_cstr__empty.
    + apply a_guess__sk.
  - crush_uniq.
  - apply ad_wf_pskl__hole.
  - simpl_open. apply a_sub__univ_ghost_r. crush_lc.
Qed.

(** Consistency reflexivity instances (any Δ1/Δ2 — only ForallInh /
    Arrow / Rigid are used, none of which tests the Δs). *)
Lemma consis_sigid_refl : forall F Δ1 Δ2 Θ,
  a_consis F Δ1 Δ2 Θ (ptyp_to_pskl σ_id)
    (ptyp_to_pskl σ_id) (ptyp_to_pskl σ_id) Θ.
Proof.
  intros. unfold σ_id; simpl.
  apply a_consis__forall_inh with (L := {}).
  intros α _. simpl_open.
  eapply a_consis__arrow; apply a_consis__rigid; crush_binds.
Qed.

Lemma consis_sigauto_refl : forall F Δ1 Δ2 Θ,
  a_consis F Δ1 Δ2 Θ (ptyp_to_pskl σ_auto)
    (ptyp_to_pskl σ_auto) (ptyp_to_pskl σ_auto) Θ.
Proof.
  intros. unfold σ_auto; simpl.
  eapply a_consis__arrow; apply consis_sigid_refl.
Qed.

(** [σ_id] against the guessed input skeleton [⊤.(□→□)]
    (ForallSyn, then the ghosts absorb the rigid binder). *)
Lemma consis_sigid_tophole : forall F Δ2 Θ,
  a_consis F empty Δ2 Θ (pskl_tophole (pskl_arrow pskl_hole pskl_hole))
    (ptyp_to_pskl σ_id) (ptyp_to_pskl σ_id) Θ.
Proof.
  intros. unfold σ_id; simpl.
  apply a_consis__forall_syn with (L := {}).
  intros α _. simpl_open.
  apply a_consis__univ_ghost_r; [ crush_lc | crush_non_flex | ].
  eapply a_consis__arrow; apply a_consis__ghost_r; fsetdec.
Qed.

(** Checking a [σ_id]-typed term against [σ_id] itself:
    ForallR, then ForallL instantiates with the rigid skolem. *)
Lemma sub_sigid_check_sigid : forall Θ,
  uniq Θ ->
  a_sub a_sub_mode_ty mode_tc (ptyp_to_pskl σ_id) Θ
        (ptyp_to_pskl σ_id) (ptyp_to_pskl σ_id) Θ.
Proof.
  intros Θ Hu. unfold σ_id; simpl ptyp_to_pskl.
  apply a_sub__forall_r with (L := dom Θ) (Ξ := nil)
    (B := pskl_arrow (pskl_var_b 0) (pskl_var_b 0)).
  { constructor. }
  intros α Hα. simpl_open.
  eapply a_sub__forall_l with (L := {}) (Ξ := nil) (P1 := pskl_var_f α).
  - discriminate.
  - left. crush_lc.
  - intros β _.
    eapply a_extract__solve with (Ξ := nil)
      (C := a_cstr_eq (pskl_var_f α) :: a_cstr_eq (pskl_var_f α) :: nil)
      (Q := pskl_var_f α).
    + simpl_open.
      apply a_looksub__check;
        [ discriminate | crush_lc | crush_lc | ].
      apply a_lookeq__arrow with (Ξ1 := nil) (Ξ2 := nil)
        (C1 := a_cstr_eq (pskl_var_f α) :: nil)
        (C2 := a_cstr_eq (pskl_var_f α) :: nil);
        apply a_lookeq__var.
    + eapply a_solve_cstr__eq.
      { apply a_solve_eq__hole_l. }
      eapply a_solve_cstr__eq.
      { apply a_solve_eq__var. }
      apply a_solve_cstr__empty.
    + apply (a_guess__ty (A := ptyp_var_f α)).
      apply a_guess_mono__var.
  - crush_uniq.
  - crush_wf.
  - simpl_open.
    apply a_sub__check; [ crush_lc | crush_lc | ].
    eexists. eapply a_consis__arrow; apply a_consis__rigid; crush_binds.
Qed.

(* ===================================================================== *)
(*  A1   λx.λy.y   (TI)   ⇒   α̂ → β̂ → β̂                                  *)
(* ===================================================================== *)

Example ex_A1 :
  Θlib ⊢ₐ[ mode_ti ; pskl_hole ]
    (exp_abs (exp_abs (exp_var_b 0)))
    ⦂ (ptyp_arrow (ptyp_var_f fa)
        (ptyp_arrow (ptyp_var_f fb) (ptyp_var_f fb)))
    ⊣ ((fb ~ abind_flex_mono) ++ (fa ~ abind_flex_mono) ++ Θlib).
Proof.
  eapply a_typing__abs with (L := dom Θlib `union` singleton fa `union` singleton fb)
    (Ξ := (fb ~ abind_flex_mono))
    (Θ2 := (fa ~ abind_flex_mono) ++ Θlib).
  - discriminate.
  - apply a_split__hole.
  - apply a_guess_mono__hole.
  - repeat constructor.
  - intros x Hx. simpl_open.
    eapply a_typing__abs with (L := dom Θlib `union` singleton fa `union` singleton fb) (Ξ := nil)
      (Θ2 := (fb ~ abind_flex_mono)
             ++ (x ~ abind_var_typ (ptyp_var_f fa))
             ++ (fa ~ abind_flex_mono) ++ Θlib).
    + discriminate.
    + apply a_split__hole.
    + apply a_guess_mono__hole.
    + constructor.
    + intros y _. simpl_open.
      eapply a_typing__var; [ crush_binds | ].
      apply a_sub__infer.
Qed.

(* ===================================================================== *)
(*  A5   id auto   (TI)   ⇒   σ_auto                                      *)
(*  (impredicative instantiation a := σ_auto, recovered by look/solve)    *)
(* ===================================================================== *)

Example ex_A5 :
  Θlib ⊢ₐ[ mode_ti ; pskl_hole ]
    (exp_app (exp_var_f x_id) (exp_var_f x_auto))
    ⦂ σ_auto ⊣ Θlib.
Proof.
  eapply a_typing__app with (A := σ_auto)
    (P := pskl_tophole (ptyp_to_pskl σ_auto)) (Θ2 := Θlib).
  - (* auto ⇨[TC;□] ⊤.(σ_auto's skeleton) *)
    eapply a_pat__var; [ crush_binds | ].
    apply a_sub__univ_ghost_r.
    unfold σ_auto, σ_id; simpl. crush_lc.
  - (* id ⦂[FN TI; ⊤.skel(σ_auto) → □]  σ_auto → σ_auto *)
    eapply a_typing__var; [ crush_binds | ].
    unfold σ_id at 1; simpl ptyp_to_pskl.
    eapply a_sub__forall_l with (L := {}) (Ξ := nil)
      (P1 := ptyp_to_pskl σ_auto).
    + discriminate.
    + left. crush_lc.
    + intros α _.
      eapply a_extract__solve with (Ξ := nil)
        (C := (a_cstr_eq (pskl_tophole (ptyp_to_pskl σ_auto)) :: nil))
        (Q := pskl_tophole (ptyp_to_pskl σ_auto)).
      * simpl_open.
        apply a_looksub__arrow with (Ξ1 := nil) (Ξ2 := nil)
          (C1 := a_cstr_eq (pskl_tophole (ptyp_to_pskl σ_auto)) :: nil)
          (C2 := nil).
        { apply a_lookeq__var. }
        { apply a_looksub__vacuous. }
      * eapply a_solve_cstr__eq.
        { apply a_solve_eq__hole_l. }
        { apply a_solve_cstr__empty. }
      * apply (a_guess__ty (Ξ := nil) (A := σ_auto)).
        apply a_guess_mono__tophole.
        unfold σ_auto, σ_id; simpl.
        apply a_guess_mono__arrow with (Ξ1 := nil) (Ξ2 := nil);
          apply a_guess_mono__forall with (L := {});
          intros β _; simpl_open;
          apply a_guess_mono__arrow with (Ξ1 := nil) (Ξ2 := nil);
          apply a_guess_mono__var.
    + crush_uniq.
    + unfold σ_auto, σ_id; simpl. crush_wf.
    + simpl_open.
      apply a_sub__arrow with (Θ1 := Θlib).
      * (* skel σ_auto against ⊤.skel σ_auto *)
        apply a_consis__univ_ghost_r;
          [ unfold σ_auto, σ_id; simpl; crush_lc
          | unfold σ_auto, σ_id; simpl; crush_non_flex
          | apply consis_sigauto_refl ].
      * apply a_sub__infer.
  - (* auto ⦂[TC; skel σ_auto]  σ_auto *)
    eapply a_typing__var with (B := σ_auto); [ crush_binds | ].
    apply a_sub__check.
    + unfold σ_auto, σ_id; simpl; crush_lc.
    + unfold σ_auto, σ_id; simpl; crush_lc.
    + eexists. apply consis_sigauto_refl.
Qed.

(* ===================================================================== *)
(*  A10b   poly (λx.x)   (TI)   ⇒   Int × Bool (Church)                   *)
(* ===================================================================== *)

Example ex_A10b :
  Θlib ⊢ₐ[ mode_ti ; pskl_hole ]
    (exp_app (exp_var_f x_poly) (exp_abs (exp_var_b 0)))
    ⦂ σ_prodIB ⊣ Θlib.
Proof.
  eapply a_typing__app with (A := σ_id)
    (P := pskl_tophole (pskl_arrow pskl_hole pskl_hole)) (Θ2 := Θlib).
  - (* λx.x ⇨[TC;□] ⊤.(□→□) *)
    eapply a_pat__abs_check with (L := dom Θlib `union` singleton fa `union` singleton fb) (Ξ := nil) (Θ1 := Θlib).
    + constructor.
    + intros x Hx. simpl_open.
      eapply a_pat__var_skl; [ crush_binds | ].
      apply a_sub__ghost.
  - (* poly ⦂[FN TI; ⊤.(□→□) → □]  σ_id → σ_prodIB *)
    eapply a_typing__var; [ crush_binds | ].
    unfold σ_poly at 1; simpl ptyp_to_pskl.
    apply a_sub__arrow with (Θ1 := Θlib).
    + apply consis_sigid_tophole.
    + apply a_sub__infer.
  - (* λx.x ⦂[TC; skel σ_id]  σ_id *)
    eapply a_typing__abs_check_step with (L := {}) (Ξ := nil)
      (A0 := ptyp_arrow b0 b0) (A := ptyp_arrow b0 b0) (Θ1 := Θlib).
    + constructor.
    + intros X _. simpl_open.
      eapply a_typing__abs_check_base with (L := dom Θlib `union` singleton fa `union` singleton fb) (Ξ := nil)
        (A0 := ptyp_arrow (ptyp_var_f X) (ptyp_var_f X))
        (A := ptyp_var_f X) (B := ptyp_var_f X)
        (Θ2 := (X ~ abind_tvar) ++ Θlib).
      * apply a_split__arrow.
      * constructor.
      * intros x Hx. simpl_open.
        eapply a_typing__var; [ crush_binds | ].
        apply a_sub__check.
        { crush_lc. }
        { crush_lc. }
        { eexists. apply a_consis__rigid. crush_binds. }
Qed.

(* ===================================================================== *)
(*  A2   choose id   (TI)   ⇒   (α̂→β̂) → α̂→β̂   with α̂ := β̂                *)
(*  (choose's ∀-var is guessed as a fresh monotype arrow α̂→β̂; checking    *)
(*   id against it solves α̂ := β̂)                                         *)
(* ===================================================================== *)

Example ex_A2 :
  Θlib ⊢ₐ[ mode_ti ; pskl_hole ]
    (exp_app (exp_var_f x_choose) (exp_var_f x_id))
    ⦂ (ptyp_arrow (ptyp_arrow (ptyp_var_f fa) (ptyp_var_f fb))
                  (ptyp_arrow (ptyp_var_f fa) (ptyp_var_f fb)))
    ⊣ ((fa ~ abind_flex_mono_def (ptyp_var_f fb))
       ++ (fb ~ abind_flex_mono) ++ Θlib).
Proof.
  eapply a_typing__app
    with (A := ptyp_arrow (ptyp_var_f fa) (ptyp_var_f fb))
         (P := pskl_tophole (pskl_arrow pskl_hole pskl_hole))
         (Θ2 := (fa ~ abind_flex_mono) ++ (fb ~ abind_flex_mono) ++ Θlib).
  - (* id ⇨[TC;□] ⊤.(□→□) *)
    apply pat_var_sigid; [ crush_uniq | crush_binds ].
  - (* choose ⦂[FN TI; ⊤.(□→□) → □]  (α̂→β̂) → (α̂→β̂) → α̂→β̂ *)
    eapply a_typing__var; [ crush_binds | ].
    unfold σ_choose; simpl ptyp_to_pskl.
    eapply a_sub__forall_l with (L := {})
      (Ξ := (fa ~ abind_flex_mono) ++ (fb ~ abind_flex_mono))
      (P1 := pskl_arrow (pskl_var_f fa) (pskl_var_f fb)).
    + discriminate.
    + left. crush_lc.
    + intros α _.
      eapply a_extract__solve with (Ξ := nil)
        (C := a_cstr_eq (pskl_tophole (pskl_arrow pskl_hole pskl_hole)) :: nil)
        (Q := pskl_tophole (pskl_arrow pskl_hole pskl_hole)).
      * simpl_open.
        apply a_looksub__arrow with (Ξ1 := nil) (Ξ2 := nil)
          (C1 := a_cstr_eq (pskl_tophole (pskl_arrow pskl_hole pskl_hole)) :: nil)
          (C2 := nil).
        { apply a_lookeq__var. }
        { apply a_looksub__vacuous. }
      * eapply a_solve_cstr__eq.
        { apply a_solve_eq__hole_l. }
        { apply a_solve_cstr__empty. }
      * apply (a_guess__ty
                 (A := ptyp_arrow (ptyp_var_f fa) (ptyp_var_f fb))).
        apply a_guess_mono__tophole.
        apply a_guess_mono__arrow
          with (Ξ1 := (fa ~ abind_flex_mono) ++ nil)
               (Ξ2 := (fb ~ abind_flex_mono) ++ nil);
          apply a_guess_mono__hole.
    + crush_uniq.
    + crush_wf.
    + simpl_open.
      apply a_sub__arrow
        with (Θ1 := (fa ~ abind_flex_mono) ++ (fb ~ abind_flex_mono) ++ Θlib).
      * apply a_consis__univ_ghost_r; [ crush_lc | crush_non_flex | ].
        eapply a_consis__arrow; apply a_consis__ghost_r; fsetdec.
      * apply a_sub__infer.
  - (* id ⦂[TC; α̂→β̂]  α̂→β̂   solving α̂ := β̂ *)
    eapply a_typing__var
      with (B := ptyp_arrow (ptyp_var_f fa) (ptyp_var_f fb));
      [ crush_binds | ].
    unfold σ_id; simpl ptyp_to_pskl.
    eapply a_sub__forall_l with (L := {}) (Ξ := nil) (P1 := pskl_var_f fa).
    + discriminate.
    + left. crush_lc.
    + intros β _.
      eapply a_extract__solve with (Ξ := nil)
        (C := a_cstr_eq (pskl_var_f fa) :: a_cstr_eq (pskl_var_f fb) :: nil)
        (Q := pskl_var_f fa).
      * simpl_open.
        apply a_looksub__check.
        { discriminate. }
        { crush_lc. }
        { crush_lc. }
        { apply a_lookeq__arrow with (Ξ1 := nil) (Ξ2 := nil)
            (C1 := a_cstr_eq (pskl_var_f fa) :: nil)
            (C2 := a_cstr_eq (pskl_var_f fb) :: nil);
            apply a_lookeq__var. }
      * eapply a_solve_cstr__eq.
        { apply a_solve_eq__hole_l. }
        { eapply a_solve_cstr__eq.
          { apply a_solve_eq__var. }
          { apply a_solve_cstr__empty. } }
      * apply (a_guess__ty (A := ptyp_var_f fa)).
        apply a_guess_mono__var.
    + crush_uniq.
    + crush_wf.
    + simpl_open.
      apply a_sub__check; [ crush_lc | crush_lc | ].
      eexists.
      eapply a_consis__arrow
        with (Θ1 := (fa ~ abind_flex_mono) ++ (fb ~ abind_flex_mono) ++ Θlib).
      * apply a_consis__flex. apply a_unify__flex_id.
        (* [a_unify__flex_id]'s premise is now [a_flex_tvar] (was [binds]) *)
        unfold a_flex_tvar. left. crush_binds.
      * apply a_consis__flex. apply a_unify__flex_l;
          [ exact Hfafb | unfold a_flex_tvar; left; crush_binds ].
Qed.

(* ===================================================================== *)
(*  A4   λ(x:∀a.a→a). x x   (TI)   ⇒   σ_id → α̂→β̂   with α̂ := β̂          *)
(* ===================================================================== *)

Example ex_A4 :
  Θlib ⊢ₐ[ mode_ti ; pskl_hole ]
    (exp_abs_anno σ_id (exp_app (exp_var_b 0) (exp_var_b 0)))
    ⦂ (ptyp_arrow σ_id (ptyp_arrow (ptyp_var_f fa) (ptyp_var_f fb)))
    ⊣ ((fa ~ abind_flex_mono_def (ptyp_var_f fb))
       ++ (fb ~ abind_flex_mono) ++ Θlib).
Proof.
  eapply a_typing__abs_anno with (L := dom Θlib `union` singleton fa `union` singleton fb)
    (Ξ := (fa ~ abind_flex_mono_def (ptyp_var_f fb))
          ++ (fb ~ abind_flex_mono))
    (P := pskl_hole) (Q := pskl_hole)
    (Θ1 := Θlib) (Θ2 := Θlib) (Θ3 := Θlib).
  - discriminate.
  - apply a_split__hole.
  - eexists. apply a_consis__ghost_r. fsetdec.
  - repeat constructor.
  - intros x Hx. simpl_open. cbn [decr_mode].
    eapply a_typing__app
      with (A := ptyp_arrow (ptyp_var_f fa) (ptyp_var_f fb))
           (P := pskl_tophole (pskl_arrow pskl_hole pskl_hole))
           (Θ2 := (fa ~ abind_flex_mono) ++ (fb ~ abind_flex_mono)
                  ++ (x ~ abind_var_typ σ_id) ++ Θlib).
    + (* x ⇨[TC;□] ⊤.(□→□) *)
      apply pat_var_sigid; [ crush_uniq | crush_binds ].
    + (* x ⦂[FN TI; ⊤.(□→□) → □]  (α̂→β̂) → α̂→β̂ *)
      eapply a_typing__var; [ crush_binds | ].
      unfold σ_id; simpl ptyp_to_pskl.
      eapply a_sub__forall_l with (L := {})
        (Ξ := (fa ~ abind_flex_mono) ++ (fb ~ abind_flex_mono))
        (P1 := pskl_arrow (pskl_var_f fa) (pskl_var_f fb)).
      * discriminate.
      * left. crush_lc.
      * intros α _.
        eapply a_extract__solve with (Ξ := nil)
          (C := a_cstr_eq (pskl_tophole (pskl_arrow pskl_hole pskl_hole)) :: nil)
          (Q := pskl_tophole (pskl_arrow pskl_hole pskl_hole)).
        { simpl_open.
          apply a_looksub__arrow with (Ξ1 := nil) (Ξ2 := nil)
            (C1 := a_cstr_eq (pskl_tophole (pskl_arrow pskl_hole pskl_hole)) :: nil)
            (C2 := nil).
          - apply a_lookeq__var.
          - apply a_looksub__vacuous. }
        { eapply a_solve_cstr__eq.
          - apply a_solve_eq__hole_l.
          - apply a_solve_cstr__empty. }
        { apply (a_guess__ty
                   (A := ptyp_arrow (ptyp_var_f fa) (ptyp_var_f fb))).
          apply a_guess_mono__tophole.
          apply a_guess_mono__arrow
            with (Ξ1 := (fa ~ abind_flex_mono) ++ nil)
                 (Ξ2 := (fb ~ abind_flex_mono) ++ nil);
            apply a_guess_mono__hole. }
      * crush_uniq.
      * crush_wf.
      * simpl_open.
        apply a_sub__arrow
          with (Θ1 := (fa ~ abind_flex_mono) ++ (fb ~ abind_flex_mono)
                      ++ (x ~ abind_var_typ σ_id) ++ Θlib).
        { apply a_consis__univ_ghost_r; [ crush_lc | crush_non_flex | ].
          eapply a_consis__arrow; apply a_consis__ghost_r; fsetdec. }
        { apply a_sub__infer. }
    + (* x ⦂[TC; α̂→β̂]  α̂→β̂   solving α̂ := β̂ *)
      eapply a_typing__var
        with (B := ptyp_arrow (ptyp_var_f fa) (ptyp_var_f fb));
        [ crush_binds | ].
      unfold σ_id; simpl ptyp_to_pskl.
      eapply a_sub__forall_l with (L := {}) (Ξ := nil) (P1 := pskl_var_f fa).
      * discriminate.
      * left. crush_lc.
      * intros β _.
        eapply a_extract__solve with (Ξ := nil)
          (C := a_cstr_eq (pskl_var_f fa) :: a_cstr_eq (pskl_var_f fb) :: nil)
          (Q := pskl_var_f fa).
        { simpl_open.
          apply a_looksub__check.
          - discriminate.
          - crush_lc.
          - crush_lc.
          - apply a_lookeq__arrow with (Ξ1 := nil) (Ξ2 := nil)
              (C1 := a_cstr_eq (pskl_var_f fa) :: nil)
              (C2 := a_cstr_eq (pskl_var_f fb) :: nil);
              apply a_lookeq__var. }
        { eapply a_solve_cstr__eq.
          - apply a_solve_eq__hole_l.
          - eapply a_solve_cstr__eq.
            + apply a_solve_eq__var.
            + apply a_solve_cstr__empty. }
        { apply (a_guess__ty (A := ptyp_var_f fa)).
          apply a_guess_mono__var. }
      * crush_uniq.
      * crush_wf.
      * simpl_open.
        apply a_sub__check; [ crush_lc | crush_lc | ].
        eexists.
        eapply a_consis__arrow
          with (Θ1 := (fa ~ abind_flex_mono) ++ (fb ~ abind_flex_mono)
                      ++ (x ~ abind_var_typ σ_id) ++ Θlib).
        { apply a_consis__flex. apply a_unify__flex_id.
          (* [a_unify__flex_id]'s premise is now [a_flex_tvar] (was [binds]) *)
          unfold a_flex_tvar. left. crush_binds. }
        { apply a_consis__flex. apply a_unify__flex_l;
          [ exact Hfafb | unfold a_flex_tvar; left; crush_binds ]. }
Qed.

(* ===================================================================== *)
(*  A10a   poly id   (TI)   ⇒   Int × Bool (Church)                       *)
(* ===================================================================== *)

Example ex_A10a :
  Θlib ⊢ₐ[ mode_ti ; pskl_hole ]
    (exp_app (exp_var_f x_poly) (exp_var_f x_id))
    ⦂ σ_prodIB ⊣ Θlib.
Proof.
  eapply a_typing__app with (A := σ_id)
    (P := pskl_tophole (pskl_arrow pskl_hole pskl_hole)) (Θ2 := Θlib).
  - (* id ⇨[TC;□] ⊤.(□→□) *)
    apply pat_var_sigid; [ crush_uniq | crush_binds ].
  - (* poly ⦂[FN TI; ⊤.(□→□) → □]  σ_id → σ_prodIB *)
    eapply a_typing__var; [ crush_binds | ].
    unfold σ_poly; simpl ptyp_to_pskl.
    apply a_sub__arrow with (Θ1 := Θlib).
    + apply consis_sigid_tophole.
    + apply a_sub__infer.
  - (* id ⦂[TC; skel σ_id]  σ_id *)
    eapply a_typing__var with (B := σ_id); [ crush_binds | ].
    apply sub_sigid_check_sigid. crush_uniq.
Qed.

(* ===================================================================== *)
(*  C2   r (λx.λy.y)   where r : (∀a.a→∀b.b→b)→Int   (TI)   ⇒   Int       *)
(*  (polymorphic λ-binder inference through the checked skeleton)         *)
(* ===================================================================== *)

Example ex_C2 :
  Θlib ⊢ₐ[ mode_ti ; pskl_hole ]
    (exp_app (exp_var_f x_r) (exp_abs (exp_abs (exp_var_b 0))))
    ⦂ tInt ⊣ Θlib.
Proof.
  eapply a_typing__app
    with (A := ptyp_all (ptyp_arrow b0 (ptyp_all (ptyp_arrow b0 b0))))
         (P := pskl_tophole (pskl_arrow pskl_hole
                 (pskl_tophole (pskl_arrow pskl_hole pskl_hole))))
         (Θ2 := Θlib).
  - (* λx.λy.y ⇨[TC;□] ⊤.(□ → ⊤.(□→□)) *)
    eapply a_pat__abs_check with (L := dom Θlib `union` singleton fa `union` singleton fb) (Ξ := nil) (Θ1 := Θlib).
    + constructor.
    + intros x Hx. simpl_open.
      eapply a_pat__abs_check with (L := dom Θlib `union` singleton fa `union` singleton fb) (Ξ := nil)
        (Θ1 := (x ~ abind_var_skl pskl_hole) ++ Θlib).
      * constructor.
      * intros y _. simpl_open.
        eapply a_pat__var_skl; [ crush_binds | ].
        apply a_sub__ghost.
  - (* r ⦂[FN TI; ⊤.(□→⊤.(□→□)) → □]  (∀a.a→∀b.b→b) → Int *)
    eapply a_typing__var; [ crush_binds | ].
    unfold σ_r; simpl ptyp_to_pskl.
    apply a_sub__arrow with (Θ1 := Θlib).
    + (* skel(∀a.a→∀b.b→b) against ⊤.(□→⊤.(□→□)) *)
      apply a_consis__forall_syn with (L := {}).
      intros α _. simpl_open.
      apply a_consis__univ_ghost_r; [ crush_lc | crush_non_flex | ].
      eapply a_consis__arrow with (Θ1 := (α ~ abind_tvar) ++ Θlib).
      * apply a_consis__ghost_r. fsetdec.
      * apply a_consis__forall_syn with (L := {}).
        intros β _. simpl_open.
        apply a_consis__univ_ghost_r; [ crush_lc | crush_non_flex | ].
        eapply a_consis__arrow; apply a_consis__ghost_r; fsetdec.
    + apply a_sub__infer.
  - (* λx.λy.y ⦂[TC; skel(∀a.a→∀b.b→b)]  ∀a.a→∀b.b→b *)
    eapply a_typing__abs_check_step with (L := {}) (Ξ := nil)
      (A0 := ptyp_arrow b0 (ptyp_all (ptyp_arrow b0 b0)))
      (A := ptyp_arrow b0 (ptyp_all (ptyp_arrow b0 b0)))
      (Θ1 := Θlib).
    + constructor.
    + intros X _. simpl_open.
      eapply a_typing__abs_check_base with (L := dom Θlib `union` singleton fa `union` singleton fb) (Ξ := nil)
        (A0 := ptyp_arrow (ptyp_var_f X) (ptyp_all (ptyp_arrow b0 b0)))
        (A := ptyp_var_f X) (B := ptyp_all (ptyp_arrow b0 b0))
        (Θ2 := (X ~ abind_tvar) ++ Θlib).
      * apply a_split__arrow.
      * constructor.
      * intros x Hx. simpl_open.
        eapply a_typing__abs_check_step with (L := {}) (Ξ := nil)
          (A0 := ptyp_arrow b0 b0) (A := ptyp_arrow b0 b0)
          (Θ1 := (x ~ abind_var_typ (ptyp_var_f X))
                 ++ (X ~ abind_tvar) ++ Θlib).
        { constructor. }
        { intros Y _. simpl_open.
          eapply a_typing__abs_check_base with (L := dom Θlib `union` singleton fa `union` singleton fb) (Ξ := nil)
            (A0 := ptyp_arrow (ptyp_var_f Y) (ptyp_var_f Y))
            (A := ptyp_var_f Y) (B := ptyp_var_f Y)
            (Θ2 := (Y ~ abind_tvar) ++ (x ~ abind_var_typ (ptyp_var_f X))
                   ++ (X ~ abind_tvar) ++ Θlib).
          - apply a_split__arrow.
          - constructor.
          - intros y _. simpl_open.
            eapply a_typing__var; [ crush_binds | ].
            apply a_sub__check; [ crush_lc | crush_lc | ].
            eexists. apply a_consis__rigid. crush_binds. }
Qed.

(* ===================================================================== *)
(*  E2b   (λx. poly x) : (∀a.a→a) → Int×Bool   (TI)                       *)
(*  (annotated η-expansion; ForallR + rigid look/solve, no flex vars)      *)
(* ===================================================================== *)

Example ex_E2b :
  Θlib ⊢ₐ[ mode_ti ; pskl_hole ]
    (exp_anno (exp_abs (exp_app (exp_var_f x_poly) (exp_var_b 0)))
              (ptyp_arrow σ_id σ_prodIB))
    ⦂ (ptyp_arrow σ_id σ_prodIB) ⊣ Θlib.
Proof.
  eapply a_typing__anno with (Θ1 := Θlib).
  - (* λx. poly x ⦂[TC; skel(σ_id→σ_prodIB)]  σ_id→σ_prodIB *)
    eapply a_typing__abs_check_base with (L := dom Θlib `union` singleton fa `union` singleton fb) (Ξ := nil)
      (A0 := ptyp_arrow σ_id σ_prodIB) (A := σ_id) (B := σ_prodIB)
      (Θ2 := Θlib).
    + apply a_split__arrow.
    + constructor.
    + intros x Hx. simpl_open.
      eapply a_typing__app
        with (A := σ_id)
             (P := pskl_tophole (pskl_arrow pskl_hole pskl_hole))
             (Θ2 := (x ~ abind_var_typ σ_id) ++ Θlib).
      * (* x ⇨[TC;□] ⊤.(□→□) *)
        apply pat_var_sigid; [ crush_uniq | crush_binds ].
      * (* poly ⦂[FN TC; ⊤.(□→□) → skel σ_prodIB] *)
        eapply a_typing__var; [ crush_binds | ].
        unfold σ_poly; simpl ptyp_to_pskl.
        apply a_sub__arrow with (Θ1 := (x ~ abind_var_typ σ_id) ++ Θlib).
        { apply consis_sigid_tophole. }
        (* codomain: skel σ_prodIB ⊑[TC; skel σ_prodIB] itself *)
        apply a_sub__forall_r with (L := dom Θlib `union` singleton aInt `union` singleton fa `union` singleton fb `union` singleton x) (Ξ := nil)
          (B := ptyp_to_pskl
                  (ptyp_arrow (ptyp_arrow tInt (ptyp_arrow tBool b0)) b0)).
        { constructor. }
        intros α Hα. simpl_open.
        eapply a_sub__forall_l
          with (L := singleton aInt `union` singleton aBool
                     `union` singleton α)
               (Ξ := nil) (P1 := pskl_var_f α).
        { discriminate. }
        { left. crush_lc. }
        { intros β Hβ.
          eapply a_extract__solve with (Ξ := nil)
            (C := a_cstr_eq (pskl_var_f α) :: a_cstr_eq (pskl_var_f α) :: nil)
            (Q := pskl_var_f α).
          - simpl_open.
            apply a_looksub__check;
              [ discriminate | crush_lc | crush_lc | ].
            apply a_lookeq__arrow with (Ξ1 := nil) (Ξ2 := nil)
              (C1 := a_cstr_eq (pskl_var_f α) :: nil)
              (C2 := a_cstr_eq (pskl_var_f α) :: nil).
            + apply a_lookeq__arrow with (Ξ1 := nil) (Ξ2 := nil)
                (C1 := nil) (C2 := a_cstr_eq (pskl_var_f α) :: nil).
              * apply a_lookeq__absent. simpl. fsetdec.
              * apply a_lookeq__arrow with (Ξ1 := nil) (Ξ2 := nil)
                  (C1 := nil) (C2 := a_cstr_eq (pskl_var_f α) :: nil).
                { apply a_lookeq__absent. simpl. fsetdec. }
                { apply a_lookeq__var. }
            + apply a_lookeq__var.
          - eapply a_solve_cstr__eq.
            { apply a_solve_eq__hole_l. }
            eapply a_solve_cstr__eq.
            { apply a_solve_eq__var. }
            apply a_solve_cstr__empty.
          - apply (a_guess__ty (A := ptyp_var_f α)).
            apply a_guess_mono__var. }
        { crush_uniq. }
        { crush_wf. }
        { simpl_open.
          apply a_sub__check; [ crush_lc | crush_lc | ].
          eexists.
          eapply a_consis__arrow.
          - eapply a_consis__arrow.
            + apply a_consis__rigid. crush_binds.
            + eapply a_consis__arrow;
                apply a_consis__rigid; crush_binds.
          - apply a_consis__rigid. crush_binds. }
      * (* x ⦂[TC; skel σ_id]  σ_id *)
        eapply a_typing__var with (B := σ_id); [ crush_binds | ].
        unfold σ_id; simpl ptyp_to_pskl.
        apply a_sub__forall_r with
          (L := dom Θlib `union` singleton aInt `union` singleton aBool
                `union` singleton fa `union` singleton fb
                `union` singleton x) (Ξ := nil)
          (B := pskl_arrow (pskl_var_b 0) (pskl_var_b 0)).
        { constructor. }
        intros α Hα. simpl_open.
        eapply a_sub__forall_l with (L := {}) (Ξ := nil)
          (P1 := pskl_var_f α).
        { discriminate. }
        { left. crush_lc. }
        { intros β _.
          eapply a_extract__solve with (Ξ := nil)
            (C := a_cstr_eq (pskl_var_f α) :: a_cstr_eq (pskl_var_f α) :: nil)
            (Q := pskl_var_f α).
          - simpl_open.
            apply a_looksub__check;
              [ discriminate | crush_lc | crush_lc | ].
            apply a_lookeq__arrow with (Ξ1 := nil) (Ξ2 := nil)
              (C1 := a_cstr_eq (pskl_var_f α) :: nil)
              (C2 := a_cstr_eq (pskl_var_f α) :: nil);
              apply a_lookeq__var.
          - eapply a_solve_cstr__eq.
            { apply a_solve_eq__hole_l. }
            eapply a_solve_cstr__eq.
            { apply a_solve_eq__var. }
            apply a_solve_cstr__empty.
          - apply (a_guess__ty (A := ptyp_var_f α)).
            apply a_guess_mono__var. }
        { crush_uniq. }
        { crush_wf. }
        { simpl_open.
          apply a_sub__check; [ crush_lc | crush_lc | ].
          eexists.
          eapply a_consis__arrow; apply a_consis__rigid; crush_binds. }
  - (* outer TI subtyping: Infer *)
    apply a_sub__infer.
Qed.

End BenchmarkExamples.
