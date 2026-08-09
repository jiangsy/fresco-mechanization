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

    PIH: A1, A2, A4, A5, A10a, A10b, C2, E2b — together they
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
Require Import src.frost.def_extra.
Require Import src.frost.ltac_utils.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.prop_flex.   (* the guess freshness kit *)
(* cluster 4: the ∀ rows are exists-fresh + close now, so these concrete
   examples go through the cofinite ADMISSIBILITY lemmas (§9) *)
Require Import src.frost.algo.prop_consis_rename.

(* ===================================================================== *)
(*  Tactic kit                                                            *)
(* ===================================================================== *)

(** Compute concrete opens / coercions in the goal. *)
Ltac simpl_open :=
  unfold open_exp_wrt_exp, open_pskl_wrt_pskl, open_ptyp_wrt_ptyp;
  simpl.

(** [a_sub__forall_l] is EXISTS-FRESH (campaign cluster 5): pick the
    rule's opener away from the INPUTS, exactly as its side condition
    demands.  Replaces the old cofinite [with (L := {})]. *)
Ltac pick_forall_l a Ha :=
  match goal with
  | |- a_sub _ _ ?P0 ?Th0 (pskl_all_syn ?P) _ _ =>
      destruct (atom_fresh (ftvar_in_aenv Th0 `union` ftvar_in_pskl P
                              `union` ftvar_in_pskl P0)) as [a Ha]
  end.

(** Read an atomic [β <> γ] off [pick_forall_l]'s hypothesis.  ⚙ SCOPED
    deliberately: the hypothesis is a 3-way union over an [ftvar_in_aenv],
    and leaving a shattered copy in the ambient context makes every later
    [fsetdec] (inside [crush_uniq] / [crush_wf]) blow up. *)
Ltac forall_l_absent Ha :=
  cbn [ftvar_in_pskl]; clear - Ha; cbn [ftvar_in_pskl] in Ha; fsetdec.

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

(** [a_binds_tvar α Θ] (rigid / flex / defined flex). *)
Ltac crush_btvar :=
  unfold a_binds_tvar;
  first [ left; solve [ crush_binds ]
        | right; left; solve [ crush_binds ]
        | right; right; eexists; solve [ crush_binds ] ].

(** [a_scope_pskl Θ P] on concrete syntax. *)
Ltac crush_wf :=
  repeat (first [ apply a_scope_pskl__arrow
                | apply a_scope_pskl__unit
                | apply a_scope_pskl__hole
                | apply a_scope_pskl__tophole
                | apply a_scope_pskl__var; crush_btvar
                | eapply a_scope_pskl__all with (L := {});
                  intros ? _; simpl_open
                (* disciplined twin (ForallL's instantiation premise) *)
                | apply a_wf_pskl__arrow
                | apply a_wf_pskl__unit
                | apply a_wf_pskl__hole
                | apply a_wf_pskl__tophole; [ crush_lc | ]
                | apply a_wf_pskl__var;
                  first [ left; fsetdec | right; crush_btvar ]
                | eapply a_wf_pskl__all with (L := {});
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

(* The freshness the relations now police: guessed names must avoid
   everything the ambient context MENTIONS (freshness campaign,
   DESIGN.md §4.3 — [a_guess_mono__hole] takes [∉ ftvar_in_aenv Θ]),
   on top of the ForallL prose-completion's dom-avoidance. *)
Hypothesis Hfa_lib : fa `notin` dom Θlib.
Hypothesis Hfb_lib : fb `notin` dom Θlib.
Hypothesis Hfa_libf : fa `notin` ftvar_in_aenv Θlib.
Hypothesis Hfb_libf : fb `notin` ftvar_in_aenv Θlib.

(* Discharge [α ∉ ftvar_in_aenv Θ] at whatever context the derivation has
   reached.  Keep [Θlib] OPAQUE — a bare [simpl in *] unfolds the library
   and its σ-types and does not terminate in reasonable time; rewrite only
   the [ftvar_in_aenv] structure. *)
Ltac crush_guess_fresh :=
  repeat rewrite ftvar_in_aenv_app;
  repeat rewrite ftvar_in_aenv_one;
  repeat rewrite ftvar_in_aenv_cons;
  cbn [ftvar_in_abind ftvar_in_ptyp];
  solve [ assumption | fsetdec ].
Hypothesis HΘlib_uniq : uniq Θlib.

(* Discharge the ForallL freshness premise [uniq (Ξ ++ Θ0)]: peel the
   fresh entries structurally, close the ambient tail by assumption.

   ⚠️⚠️ THIS TACTIC IS THE TREE'S #1 BUILD HOT SPOT, AND IT IS NOT YET FIXED.
   Profiled 2026-08-09 ([Set Ltac Profiling] on [ex_C2] alone):

     crush_uniq   99.9% of the proof, in FOUR calls
       -> fsetdec -> tauto -> simplif, 15.5 M is_conj + 13 M is_disj calls

   That is 442 s in [ex_C2] — 36% of the whole tree's proof time — and since
   this file is a LEAF that depends on nearly everything, it is 442 s sitting
   on the build's CRITICAL PATH (wall clock ≈ 646 s at -j8 for a tree whose
   total serial proof time is ≈ 1229 s).  Fixing it is the single biggest
   available build-time win.

   ROOT CAUSE (measured, not guessed): [fsetdec] calls [tauto] internally, and
   to discharge these goals it must UNFOLD [dom Θlib] — seven entries carrying
   full σ-types.  Marking [Θlib] [Opaque] makes [fsetdec] fail outright in 6 s
   with "the goal is beyond the scope of this tactic", which is the proof that
   the unfolding is load-bearing rather than incidental.

   ⛔ FOUR FIXES TRIED AND REFUTED — do not re-try these blind:
     1. [solve_notin]                      — FAILS on all three residual goals
                                             (they are [fb ∉ {x} ∪ {fa} ∪ dom Θlib];
                                             its closing [auto; try tauto] cannot
                                             bridge them).
     2. [destruct_notin] first, then [fsetdec] / [solve_notin] / [auto]
                                           — all FAIL fast (5-16 s).
     3. adding disequality SYMMETRY ([Hfafb : fa <> fb] is needed as [fb <> fa];
        [destruct_notin] never flips a [<>])  — still FAILS.
     4. scoping the context — both a generic "keep only atom-set facts" pass and
        USE-SITE [clear - Hα Hx Hβ Hy Hfa_lib Hfb_lib Hfafb HΘlib_uniq] at each
        of the four call sites — still ≥250 s.  So the blow-up is NOT driven by
        the number of ambient hypotheses; it is the [dom Θlib] expansion.
     5. characterising [dom Θlib] as a union of seven singletons + [Opaque Θlib]
        + rewriting before [fsetdec]  — still ≥250 s.

   NEXT LEAD: keep [Θlib] opaque and supply the needed [dom]/[∉] facts as
   pre-proved lemmas so [fsetdec] never sees the library term at all — i.e.
   discharge these goals WITHOUT [fsetdec] (the goals are all of the shape
   [v ∉ <concrete union of singletons> ∪ dom Θlib]).  See
   docs/REPORT-remech-cleanup-audit.md §PERF. *)
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
    no input skeleton: [Θ ⊢ₐ[TC;□] x ⇨ ∀◇(□→□) ⊣ Θ]
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
  pick_forall_l α Hα.
  eapply a_sub__forall_l with (α := α) (Ξ := nil) (P1 := pskl_hole).
  - discriminate.
  - right; reflexivity.
  - clear - Hα; fsetdec.
  - eapply a_extract__solve with (Ξ := nil) (Ξs := nil)
                                 (C := nil) (Q := pskl_hole).
    + simpl_open. apply a_looksub__vacuous.
    + apply a_solve_cstr__empty.
    + apply a_guess__sk.
  - crush_uniq.
  - apply a_wf_pskl__hole.
  - simpl_open. apply a_sub__univ_ghost_r. crush_lc.
Qed.

(** Consistency reflexivity instances (any Δ1/Δ2 — only ForallInh /
    Arrow / Rigid are used, none of which tests the Δs). *)
Lemma consis_sigid_refl : forall Δ1 Δ2 Θ,
  a_consis Δ1 Δ2 Θ (ptyp_to_pskl σ_id)
    (ptyp_to_pskl σ_id) (ptyp_to_pskl σ_id) Θ.
Proof.
  intros. unfold σ_id; simpl.
  apply a_consis_forall_inh_cofinite with (L := {}).
  intros α _. simpl_open.
  eapply a_consis__arrow; apply a_consis__rigid; crush_binds.
Qed.

Lemma consis_sigauto_refl : forall Δ1 Δ2 Θ,
  a_consis Δ1 Δ2 Θ (ptyp_to_pskl σ_auto)
    (ptyp_to_pskl σ_auto) (ptyp_to_pskl σ_auto) Θ.
Proof.
  intros. unfold σ_auto; simpl.
  eapply a_consis__arrow; apply consis_sigid_refl.
Qed.

(** [σ_id] against the guessed input skeleton [∀◇(□→□)]
    (ForallSyn, then the ghosts absorb the rigid binder). *)
Lemma consis_sigid_tophole : forall Δ2 Θ,
  a_consis empty Δ2 Θ (pskl_tophole (pskl_arrow pskl_hole pskl_hole))
    (ptyp_to_pskl σ_id) (ptyp_to_pskl σ_id) Θ.
Proof.
  intros. unfold σ_id; simpl.
  apply a_consis_forall_syn_cofinite with (L := {}).
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
  destruct (atom_fresh (dom Θ)) as [α Hα].
  apply a_sub__forall_r with (α := α) (Ξ := nil)
    (B := pskl_arrow (pskl_var_b 0) (pskl_var_b 0)).
  { simpl; intuition. }
  { constructor. }
  { crush_uniq. }
  { simpl. simpl in Hα. clear - Hα. fsetdec. }
  simpl_open.
  pick_forall_l β Hβ.
  eapply a_sub__forall_l with (α := β) (Ξ := nil) (P1 := pskl_var_f α).
  - discriminate.
  - left. crush_lc.
  - clear - Hβ; fsetdec.
  - eapply a_extract__solve with (Ξ := nil) (Ξs := nil)
      (C := a_cstr_eq (pskl_var_f α) :: a_cstr_eq (pskl_var_f α) :: nil)
      (Q := pskl_var_f α).
    + simpl_open.
      apply a_looksub__check;
        [ simpl; intuition | discriminate | crush_lc | crush_lc | ].
      apply a_lookeq__arrow with (Ξ1 := nil) (Ξ2 := nil)
        (C1 := a_cstr_eq (pskl_var_f α) :: nil)
        (C2 := a_cstr_eq (pskl_var_f α) :: nil);
        apply a_lookeq__var.
    + eapply a_solve_cstr__eq with (Ξ1 := nil) (Ξ2 := nil).
      { apply a_solve_eq__hole_l. }
      eapply a_solve_cstr__eq with (Ξ1 := nil) (Ξ2 := nil).
      { apply a_solve_eq__var. }
      apply a_solve_cstr__empty.
    + apply (a_guess__ty (A := ptyp_var_f α)).
      apply a_guess_mono__var.
  - crush_uniq.
  - crush_wf.
  - simpl_open.
    apply a_sub__check; [ simpl; intuition | simpl; intuition | crush_lc | crush_lc | ].
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
  destruct (atom_fresh (dom Θlib `union` singleton fa `union` singleton fb))
    as [x Hx].
  eapply a_typing__abs with (x := x)
    (Ξ := (fb ~ abind_flex_mono))
    (Θ2 := (fa ~ abind_flex_mono) ++ Θlib).
  - discriminate.
  - apply a_split__hole.
  - apply a_guess_mono__hole. crush_guess_fresh.
  - crush_uniq.
  - repeat constructor.
  - simpl_env; simpl fvar_in_exp; clear - Hx; fsetdec.
  - simpl_open.
    destruct (atom_fresh (dom Θlib `union` singleton fa `union` singleton fb
                `union` singleton x)) as [y Hy].
    eapply a_typing__abs with (x := y) (Ξ := nil)
      (Θ2 := (fb ~ abind_flex_mono)
             ++ (x ~ abind_var_typ (ptyp_var_f fa))
             ++ (fa ~ abind_flex_mono) ++ Θlib).
    + discriminate.
    + apply a_split__hole.
    + apply a_guess_mono__hole. crush_guess_fresh.
    + crush_uniq.
    + constructor.
    + simpl_env; simpl fvar_in_exp; clear - Hy; fsetdec.
    + simpl_open.
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
  - (* auto ⇨[TC;□] ∀◇(σ_auto's skeleton) *)
    eapply a_pat__var; [ crush_binds | ].
    apply a_sub__univ_ghost_r.
    unfold σ_auto, σ_id; simpl. crush_lc.
  - (* id ⦂[FN TI; ∀◇skel(σ_auto) → □]  σ_auto → σ_auto *)
    eapply a_typing__var; [ crush_binds | ].
    unfold σ_id at 1; simpl ptyp_to_pskl.
    pick_forall_l α Hα.
    eapply a_sub__forall_l with (α := α) (Ξ := nil)
      (P1 := ptyp_to_pskl σ_auto).
    + discriminate.
    + left. crush_lc.
    + clear - Hα; fsetdec.
    + eapply a_extract__solve with (Ξ := nil) (Ξs := nil)
        (C := (a_cstr_eq (pskl_tophole (ptyp_to_pskl σ_auto)) :: nil))
        (Q := pskl_tophole (ptyp_to_pskl σ_auto)).
      * simpl_open.
        apply a_looksub__arrow with (Ξ1 := nil) (Ξ2 := nil)
          (C1 := a_cstr_eq (pskl_tophole (ptyp_to_pskl σ_auto)) :: nil)
          (C2 := nil).
        { apply a_lookeq__var. }
        { apply a_looksub__vacuous. }
      * eapply a_solve_cstr__eq with (Ξ1 := nil) (Ξ2 := nil).
        { apply a_solve_eq__hole_l. }
        { apply a_solve_cstr__empty. }
      * apply (a_guess__ty (Ξ := nil) (A := σ_auto)).
        apply a_guess_mono__tophole.
        unfold σ_auto, σ_id; simpl.
        (* exists-fresh + close: enter through the OPENED form
           ([a_guess_mono_all_of_one]); the bodies are variable-only, so any
           fresh atom serves *)
        apply a_guess_mono__arrow with (Ξ1 := nil) (Ξ2 := nil);
          (pick fresh β;
           apply a_guess_mono_all_of_one with (β := β);
           [ | simpl; fsetdec | simpl; fsetdec | simpl; fsetdec ]);
          simpl_open;
          apply a_guess_mono__arrow with (Ξ1 := nil) (Ξ2 := nil);
          apply a_guess_mono__var.
    + crush_uniq.
    + unfold σ_auto, σ_id; simpl. crush_wf.
    + simpl_open.
      apply a_sub__arrow with (Θ1 := Θlib).
      * (* skel σ_auto against ∀◇skel σ_auto *)
        apply a_consis__univ_ghost_r;
          [ unfold σ_auto, σ_id; simpl; crush_lc
          | unfold σ_auto, σ_id; simpl; crush_non_flex
          | apply consis_sigauto_refl ].
      * apply a_sub__infer.
  - (* auto ⦂[TC; skel σ_auto]  σ_auto *)
    eapply a_typing__var with (B := σ_auto); [ crush_binds | ].
    apply a_sub__check.
    + unfold σ_auto, σ_id; simpl; intuition.
    + unfold σ_auto, σ_id; simpl; intuition.
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
  - (* λx.x ⇨[TC;□] ∀◇(□→□) *)
    eapply a_pat__abs_check with (L := dom Θlib `union` singleton fa `union` singleton fb) (Ξ := nil) (Θ1 := Θlib).
    + constructor.
    + intros x Hx. simpl_open.
      eapply a_pat__var_skl; [ crush_binds | ].
      apply a_sub__ghost.
  - (* poly ⦂[FN TI; ∀◇(□→□) → □]  σ_id → σ_prodIB *)
    eapply a_typing__var; [ crush_binds | ].
    unfold σ_poly at 1; simpl ptyp_to_pskl.
    apply a_sub__arrow with (Θ1 := Θlib).
    + apply consis_sigid_tophole.
    + apply a_sub__infer.
  - (* λx.x ⦂[TC; skel σ_id]  σ_id *)
    destruct (atom_fresh (dom Θlib `union` singleton fa `union` singleton fb))
      as [α Hα].
    eapply a_typing__abs_check_step with (α := α) (Ξ := nil)
      (A0 := ptyp_arrow b0 b0) (A := ptyp_arrow b0 b0) (Θ1 := Θlib).
    + constructor.
    + crush_uniq.
    + intros γ Hγ; simpl in Hγ; clear - Hγ; fsetdec.
    + simpl_env; simpl ftvar_in_ptyp; simpl ftvar_in_exp; clear - Hα; fsetdec.
    + simpl_open.
      destruct (atom_fresh (dom Θlib `union` singleton fa
                  `union` singleton fb `union` singleton α)) as [x Hx].
      eapply a_typing__abs_check_base
        with (x := x) (Ξ := nil)
        (A0 := ptyp_arrow (ptyp_var_f α) (ptyp_var_f α))
        (A := ptyp_var_f α) (B := ptyp_var_f α)
        (Θ2 := (α ~ abind_tvar) ++ Θlib).
      * apply a_split__arrow.
      * constructor.
      * crush_uniq.
      * intros γ Hγ; simpl in Hγ; clear - Hγ; fsetdec.
      * simpl_env; simpl fvar_in_exp; clear - Hx; fsetdec.
      * simpl_open.
        eapply a_typing__var; [ crush_binds | ].
        apply a_sub__check.
        { simpl; intuition. }
        { simpl; intuition. }
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
  - (* id ⇨[TC;□] ∀◇(□→□) *)
    apply pat_var_sigid; [ crush_uniq | crush_binds ].
  - (* choose ⦂[FN TI; ∀◇(□→□) → □]  (α̂→β̂) → (α̂→β̂) → α̂→β̂ *)
    eapply a_typing__var; [ crush_binds | ].
    unfold σ_choose; simpl ptyp_to_pskl.
    pick_forall_l α Hα.
    eapply a_sub__forall_l with (α := α)
      (Ξ := (fa ~ abind_flex_mono) ++ (fb ~ abind_flex_mono))
      (P1 := pskl_arrow (pskl_var_f fa) (pskl_var_f fb)).
    + discriminate.
    + left. crush_lc.
    + clear - Hα; fsetdec.
    + eapply a_extract__solve with (Ξ := nil) (Ξs := nil)
        (C := a_cstr_eq (pskl_tophole (pskl_arrow pskl_hole pskl_hole)) :: nil)
        (Q := pskl_tophole (pskl_arrow pskl_hole pskl_hole)).
      * simpl_open.
        apply a_looksub__arrow with (Ξ1 := nil) (Ξ2 := nil)
          (C1 := a_cstr_eq (pskl_tophole (pskl_arrow pskl_hole pskl_hole)) :: nil)
          (C2 := nil).
        { apply a_lookeq__var. }
        { apply a_looksub__vacuous. }
      * eapply a_solve_cstr__eq with (Ξ1 := nil) (Ξ2 := nil).
        { apply a_solve_eq__hole_l. }
        { apply a_solve_cstr__empty. }
      * apply (a_guess__ty
                 (A := ptyp_arrow (ptyp_var_f fa) (ptyp_var_f fb))).
        apply a_guess_mono__tophole.
        apply a_guess_mono__arrow
          with (Ξ1 := (fa ~ abind_flex_mono) ++ nil)
               (Ξ2 := (fb ~ abind_flex_mono) ++ nil);
          apply a_guess_mono__hole; crush_guess_fresh.
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
    pick_forall_l β Hβ.
    eapply a_sub__forall_l with (α := β) (Ξ := nil) (P1 := pskl_var_f fa).
    + discriminate.
    + left. crush_lc.
    + clear - Hβ; fsetdec.
    + eapply a_extract__solve with (Ξ := nil) (Ξs := nil)
        (C := a_cstr_eq (pskl_var_f fa) :: a_cstr_eq (pskl_var_f fb) :: nil)
        (Q := pskl_var_f fa).
      * simpl_open.
        apply a_looksub__check.
        { simpl; intuition. }
        { discriminate. }
        { crush_lc. }
        { crush_lc. }
        { apply a_lookeq__arrow with (Ξ1 := nil) (Ξ2 := nil)
            (C1 := a_cstr_eq (pskl_var_f fa) :: nil)
            (C2 := a_cstr_eq (pskl_var_f fb) :: nil);
            apply a_lookeq__var. }
      * eapply a_solve_cstr__eq with (Ξ1 := nil) (Ξ2 := nil).
        { apply a_solve_eq__hole_l. }
        { eapply a_solve_cstr__eq with (Ξ1 := nil) (Ξ2 := nil).
          { apply a_solve_eq__var. }
          { apply a_solve_cstr__empty. } }
      * apply (a_guess__ty (A := ptyp_var_f fa)).
        apply a_guess_mono__var.
    + crush_uniq.
    + crush_wf.
    + simpl_open.
      apply a_sub__check; [ simpl; intuition | simpl; intuition | crush_lc | crush_lc | ].
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
  destruct (atom_fresh (dom Θlib `union` singleton fa `union` singleton fb))
    as [x Hx].
  eapply a_typing__abs_anno with (x := x)
    (Ξ := (fa ~ abind_flex_mono_def (ptyp_var_f fb))
          ++ (fb ~ abind_flex_mono))
    (P := pskl_hole) (Q := pskl_hole)
    (Θ1 := Θlib) (Θ2 := Θlib) (Θ3 := Θlib).
  - discriminate.
  - apply a_split__hole.
  - eexists. apply a_consis__ghost_r. fsetdec.
  - repeat constructor.
  - simpl_env; simpl fvar_in_exp; clear - Hx; fsetdec.
  - simpl_open. cbn [decr_mode].
    eapply a_typing__app
      with (A := ptyp_arrow (ptyp_var_f fa) (ptyp_var_f fb))
           (P := pskl_tophole (pskl_arrow pskl_hole pskl_hole))
           (Θ2 := (fa ~ abind_flex_mono) ++ (fb ~ abind_flex_mono)
                  ++ (x ~ abind_var_typ σ_id) ++ Θlib).
    + (* x ⇨[TC;□] ∀◇(□→□) *)
      apply pat_var_sigid; [ crush_uniq | crush_binds ].
    + (* x ⦂[FN TI; ∀◇(□→□) → □]  (α̂→β̂) → α̂→β̂ *)
      eapply a_typing__var; [ crush_binds | ].
      unfold σ_id; simpl ptyp_to_pskl.
      pick_forall_l α Hα.
      eapply a_sub__forall_l with (α := α)
        (Ξ := (fa ~ abind_flex_mono) ++ (fb ~ abind_flex_mono))
        (P1 := pskl_arrow (pskl_var_f fa) (pskl_var_f fb)).
      * discriminate.
      * left. crush_lc.
      * clear - Hα; fsetdec.
      * eapply a_extract__solve with (Ξ := nil) (Ξs := nil)
          (C := a_cstr_eq (pskl_tophole (pskl_arrow pskl_hole pskl_hole)) :: nil)
          (Q := pskl_tophole (pskl_arrow pskl_hole pskl_hole)).
        { simpl_open.
          apply a_looksub__arrow with (Ξ1 := nil) (Ξ2 := nil)
            (C1 := a_cstr_eq (pskl_tophole (pskl_arrow pskl_hole pskl_hole)) :: nil)
            (C2 := nil).
          - apply a_lookeq__var.
          - apply a_looksub__vacuous. }
        { eapply a_solve_cstr__eq with (Ξ1 := nil) (Ξ2 := nil).
          - apply a_solve_eq__hole_l.
          - apply a_solve_cstr__empty. }
        { apply (a_guess__ty
                   (A := ptyp_arrow (ptyp_var_f fa) (ptyp_var_f fb))).
          apply a_guess_mono__tophole.
          apply a_guess_mono__arrow
            with (Ξ1 := (fa ~ abind_flex_mono) ++ nil)
                 (Ξ2 := (fb ~ abind_flex_mono) ++ nil);
            apply a_guess_mono__hole; crush_guess_fresh. }
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
      pick_forall_l β Hβ.
      eapply a_sub__forall_l with (α := β) (Ξ := nil) (P1 := pskl_var_f fa).
      * discriminate.
      * left. crush_lc.
      * clear - Hβ; fsetdec.
      * eapply a_extract__solve with (Ξ := nil) (Ξs := nil)
          (C := a_cstr_eq (pskl_var_f fa) :: a_cstr_eq (pskl_var_f fb) :: nil)
          (Q := pskl_var_f fa).
        { simpl_open.
          apply a_looksub__check.
          - simpl; intuition.
          - discriminate.
          - crush_lc.
          - crush_lc.
          - apply a_lookeq__arrow with (Ξ1 := nil) (Ξ2 := nil)
              (C1 := a_cstr_eq (pskl_var_f fa) :: nil)
              (C2 := a_cstr_eq (pskl_var_f fb) :: nil);
              apply a_lookeq__var. }
        { eapply a_solve_cstr__eq with (Ξ1 := nil) (Ξ2 := nil).
          - apply a_solve_eq__hole_l.
          - eapply a_solve_cstr__eq with (Ξ1 := nil) (Ξ2 := nil).
            + apply a_solve_eq__var.
            + apply a_solve_cstr__empty. }
        { apply (a_guess__ty (A := ptyp_var_f fa)).
          apply a_guess_mono__var. }
      * crush_uniq.
      * crush_wf.
      * simpl_open.
        apply a_sub__check; [ simpl; intuition | simpl; intuition | crush_lc | crush_lc | ].
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
  - (* id ⇨[TC;□] ∀◇(□→□) *)
    apply pat_var_sigid; [ crush_uniq | crush_binds ].
  - (* poly ⦂[FN TI; ∀◇(□→□) → □]  σ_id → σ_prodIB *)
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
  - (* λx.λy.y ⇨[TC;□] ∀◇(□ → ∀◇(□→□)) *)
    eapply a_pat__abs_check with (L := dom Θlib `union` singleton fa `union` singleton fb) (Ξ := nil) (Θ1 := Θlib).
    + constructor.
    + intros x Hx. simpl_open.
      eapply a_pat__abs_check with (L := dom Θlib `union` singleton fa `union` singleton fb) (Ξ := nil)
        (Θ1 := (x ~ abind_var_skl pskl_hole) ++ Θlib).
      * constructor.
      * intros y _. simpl_open.
        eapply a_pat__var_skl; [ crush_binds | ].
        apply a_sub__ghost.
  - (* r ⦂[FN TI; ∀◇(□→∀◇(□→□)) → □]  (∀a.a→∀b.b→b) → Int *)
    eapply a_typing__var; [ crush_binds | ].
    unfold σ_r; simpl ptyp_to_pskl.
    apply a_sub__arrow with (Θ1 := Θlib).
    + (* skel(∀a.a→∀b.b→b) against ∀◇(□→∀◇(□→□)) *)
      apply a_consis_forall_syn_cofinite with (L := {}).
      intros α _. simpl_open.
      apply a_consis__univ_ghost_r; [ crush_lc | crush_non_flex | ].
      eapply a_consis__arrow with (Θ1 := (α ~ abind_tvar) ++ Θlib).
      * apply a_consis__ghost_r. fsetdec.
      * apply a_consis_forall_syn_cofinite with (L := {}).
        intros β _. simpl_open.
        apply a_consis__univ_ghost_r; [ crush_lc | crush_non_flex | ].
        eapply a_consis__arrow; apply a_consis__ghost_r; fsetdec.
    + apply a_sub__infer.
  - (* λx.λy.y ⦂[TC; skel(∀a.a→∀b.b→b)]  ∀a.a→∀b.b→b *)
    destruct (atom_fresh (dom Θlib `union` singleton fa `union` singleton fb))
      as [α Hα].
    eapply a_typing__abs_check_step with (α := α) (Ξ := nil)
      (A0 := ptyp_arrow b0 (ptyp_all (ptyp_arrow b0 b0)))
      (A := ptyp_arrow b0 (ptyp_all (ptyp_arrow b0 b0)))
      (Θ1 := Θlib).
    + constructor.
    + crush_uniq.
    + intros γ Hγ; simpl in Hγ; clear - Hγ; fsetdec.
    + simpl_env; simpl ftvar_in_ptyp; simpl ftvar_in_exp; clear - Hα; fsetdec.
    + simpl_open.
      destruct (atom_fresh (dom Θlib `union` singleton fa
                  `union` singleton fb `union` singleton α)) as [x Hx].
      eapply a_typing__abs_check_base
        with (x := x) (Ξ := nil)
        (A0 := ptyp_arrow (ptyp_var_f α) (ptyp_all (ptyp_arrow b0 b0)))
        (A := ptyp_var_f α) (B := ptyp_all (ptyp_arrow b0 b0))
        (Θ2 := (α ~ abind_tvar) ++ Θlib).
      * apply a_split__arrow.
      * constructor.
      * crush_uniq.
      * intros γ Hγ; simpl in Hγ; clear - Hγ; fsetdec.
      * simpl_env; simpl fvar_in_exp; clear - Hx; fsetdec.
      * simpl_open.
        destruct (atom_fresh (dom Θlib `union` singleton fa
                    `union` singleton fb `union` singleton α
                    `union` singleton x)) as [β Hβ].
        eapply a_typing__abs_check_step
          with (α := β) (Ξ := nil)
          (A0 := ptyp_arrow b0 b0) (A := ptyp_arrow b0 b0)
          (Θ1 := (x ~ abind_var_typ (ptyp_var_f α))
                 ++ (α ~ abind_tvar) ++ Θlib).
        { constructor. }
        { crush_uniq. }
        { intros γ Hγ; simpl in Hγ; clear - Hγ; fsetdec. }
        { simpl_env; simpl ftvar_in_ptyp; simpl ftvar_in_exp; clear - Hβ; fsetdec. }
        { simpl_open.
          destruct (atom_fresh (dom Θlib `union` singleton fa
                      `union` singleton fb `union` singleton α
                      `union` singleton x `union` singleton β)) as [y Hy].
          eapply a_typing__abs_check_base
            with (x := y) (Ξ := nil)
            (A0 := ptyp_arrow (ptyp_var_f β) (ptyp_var_f β))
            (A := ptyp_var_f β) (B := ptyp_var_f β)
            (Θ2 := (β ~ abind_tvar) ++ (x ~ abind_var_typ (ptyp_var_f α))
                   ++ (α ~ abind_tvar) ++ Θlib).
          - apply a_split__arrow.
          - constructor.
          - crush_uniq.
          - intros γ Hγ; simpl in Hγ; clear - Hγ; fsetdec.
          - simpl_env; simpl fvar_in_exp; clear - Hy; fsetdec.
          - simpl_open.
            eapply a_typing__var; [ crush_binds | ].
            apply a_sub__check; [ simpl; intuition | simpl; intuition | crush_lc | crush_lc | ].
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
    destruct (atom_fresh (dom Θlib `union` singleton fa `union` singleton fb
                `union` singleton x_poly)) as [x Hx].
    eapply a_typing__abs_check_base with (x := x) (Ξ := nil)
      (A0 := ptyp_arrow σ_id σ_prodIB) (A := σ_id) (B := σ_prodIB)
      (Θ2 := Θlib).
    + apply a_split__arrow.
    + constructor.
    + crush_uniq.
    + intros γ Hγ; simpl in Hγ; clear - Hγ; fsetdec.
    + simpl_env; simpl fvar_in_exp; clear - Hx; fsetdec.
    + simpl_open.
      eapply a_typing__app
        with (A := σ_id)
             (P := pskl_tophole (pskl_arrow pskl_hole pskl_hole))
             (Θ2 := (x ~ abind_var_typ σ_id) ++ Θlib).
      * (* x ⇨[TC;□] ∀◇(□→□) *)
        apply pat_var_sigid; [ crush_uniq | crush_binds ].
      * (* poly ⦂[FN TC; ∀◇(□→□) → skel σ_prodIB] *)
        eapply a_typing__var; [ crush_binds | ].
        unfold σ_poly; simpl ptyp_to_pskl.
        apply a_sub__arrow with (Θ1 := (x ~ abind_var_typ σ_id) ++ Θlib).
        { apply consis_sigid_tophole. }
        (* codomain: skel σ_prodIB ⩽[TC; skel σ_prodIB] itself *)
        destruct (atom_fresh (dom Θlib `union` singleton aInt
                    `union` singleton aBool `union` singleton fa
                    `union` singleton fb `union` singleton x)) as [α Hα].
        apply a_sub__forall_r with (α := α) (Ξ := nil)
          (B := ptyp_to_pskl
                  (ptyp_arrow (ptyp_arrow tInt (ptyp_arrow tBool b0)) b0)).
        { simpl; intuition. }
        { constructor. }
        { crush_uniq. }
        { simpl. simpl in Hα. clear - Hα. fsetdec. }
        simpl_open.
        pick_forall_l β Hβ.
        eapply a_sub__forall_l
          with (α := β) (Ξ := nil) (P1 := pskl_var_f α).
        { discriminate. }
        { left. crush_lc. }
        { clear - Hβ; fsetdec. }
        { eapply a_extract__solve with (Ξ := nil) (Ξs := nil)
            (C := a_cstr_eq (pskl_var_f α) :: a_cstr_eq (pskl_var_f α) :: nil)
            (Q := pskl_var_f α).
          - simpl_open.
            apply a_looksub__check;
              [ simpl; intuition | discriminate | crush_lc | crush_lc | ].
            apply a_lookeq__arrow with (Ξ1 := nil) (Ξ2 := nil)
              (C1 := a_cstr_eq (pskl_var_f α) :: nil)
              (C2 := a_cstr_eq (pskl_var_f α) :: nil).
            + apply a_lookeq__arrow with (Ξ1 := nil) (Ξ2 := nil)
                (C1 := nil) (C2 := a_cstr_eq (pskl_var_f α) :: nil).
              * apply a_lookeq__absent. forall_l_absent Hβ.
              * apply a_lookeq__arrow with (Ξ1 := nil) (Ξ2 := nil)
                  (C1 := nil) (C2 := a_cstr_eq (pskl_var_f α) :: nil).
                { apply a_lookeq__absent. forall_l_absent Hβ. }
                { apply a_lookeq__var. }
            + apply a_lookeq__var.
          - eapply a_solve_cstr__eq with (Ξ1 := nil) (Ξ2 := nil).
            { apply a_solve_eq__hole_l. }
            eapply a_solve_cstr__eq with (Ξ1 := nil) (Ξ2 := nil).
            { apply a_solve_eq__var. }
            apply a_solve_cstr__empty.
          - apply (a_guess__ty (A := ptyp_var_f α)).
            apply a_guess_mono__var. }
        { crush_uniq. }
        { clear Hβ; crush_wf. }   (* ⚙ the ForallL opener's 3-way
                                     union makes [fsetdec] crawl *)
        { simpl_open.
          apply a_sub__check; [ simpl; intuition | simpl; intuition | crush_lc | crush_lc | ].
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
        destruct (atom_fresh (dom Θlib `union` singleton aInt
                    `union` singleton aBool `union` singleton fa
                    `union` singleton fb `union` singleton x)) as [α Hα].
        apply a_sub__forall_r with (α := α) (Ξ := nil)
          (B := pskl_arrow (pskl_var_b 0) (pskl_var_b 0)).
        { simpl; intuition. }
        { constructor. }
        { crush_uniq. }
        { simpl. simpl in Hα. clear - Hα. fsetdec. }
        simpl_open.
        pick_forall_l β Hβ.
        eapply a_sub__forall_l with (α := β) (Ξ := nil)
          (P1 := pskl_var_f α).
        { discriminate. }
        { left. crush_lc. }
        { clear - Hβ; fsetdec. }
        { eapply a_extract__solve with (Ξ := nil) (Ξs := nil)
            (C := a_cstr_eq (pskl_var_f α) :: a_cstr_eq (pskl_var_f α) :: nil)
            (Q := pskl_var_f α).
          - simpl_open.
            apply a_looksub__check;
              [ simpl; intuition | discriminate | crush_lc | crush_lc | ].
            apply a_lookeq__arrow with (Ξ1 := nil) (Ξ2 := nil)
              (C1 := a_cstr_eq (pskl_var_f α) :: nil)
              (C2 := a_cstr_eq (pskl_var_f α) :: nil);
              apply a_lookeq__var.
          - eapply a_solve_cstr__eq with (Ξ1 := nil) (Ξ2 := nil).
            { apply a_solve_eq__hole_l. }
            eapply a_solve_cstr__eq with (Ξ1 := nil) (Ξ2 := nil).
            { apply a_solve_eq__var. }
            apply a_solve_cstr__empty.
          - apply (a_guess__ty (A := ptyp_var_f α)).
            apply a_guess_mono__var. }
        { crush_uniq. }
        { clear Hβ; crush_wf. }   (* ⚙ the ForallL opener's 3-way
                                     union makes [fsetdec] crawl *)
        { simpl_open.
          apply a_sub__check; [ simpl; intuition | simpl; intuition | crush_lc | crush_lc | ].
          eexists.
          eapply a_consis__arrow; apply a_consis__rigid; crush_binds. }
  - (* outer TI subtyping: Infer *)
    apply a_sub__infer.
Qed.

End BenchmarkExamples.
