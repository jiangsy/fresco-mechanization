(** PROBE (2026-08-17): SKELETON INFERENCE PRESENTS THE DIVERGENT CELL, so
    the fragment direction — (R2) of docs/HANDOFF-close-consis-unrestricted.md
    §5, "weaken [pskl_no_hole] to a predicate that excludes just the two
    divergent shapes" — CANNOT reach the flagship: the shapes are REACHED.

    The handover's own first question was whether subtyping and typing ever
    actually PRESENT a hole opposite a flexible variable.  They do, and not
    in a corner.  The source program

        (λf. f (λy. f y)) (λz. z)

    reaches the cell through three independently innocent moves:

      (1) [AT-Abs] GUESSES a λ-binder's type from its split skeleton, and
          a guess MIRRORS the skeleton's structure, inventing a fresh
          flexible exactly at each ◇ ([e_guess_mono]).  An abstraction
          applied to an unannotated abstraction splits its pattern at
          [⫯(◇→◇)], so f's guessed type is δ̂1 → δ̂2 — an ARROW of fresh,
          UNDEFINED flexibles — deposited as [f ~ typ (δ̂1→δ̂2), δ̂1, δ̂2].
      (2) [AT-App] re-runs skeleton inference on its ARGUMENT at pattern ◇
          in that typing-phase context, and under the argument's own
          λ-binder [AP-AbsCheck] binds y at SKELETON ◇, whose occurrence
          echoes ◇ back out through [Ghost] ([e_sub__ghost] answers a ◇
          subject with the pattern).  So the body run for [f y] types f at
          the NAKED arrow pattern ◇ → ◇.
      (3) [AP-Var] + [Arrow] pair that pattern componentwise against f's
          type: consis(pattern ◇, subject δ̂1) — a hole opposite an
          undefined flexible, the exact cell at which the consistency
          rules and their runner diverge (cex/probe_consis_ghost_flex.v:
          [U-GhostR] answers with the context UNCHANGED, [U-FlexL] SOLVES
          the flexible to a fresh alias).

    WHAT IS MACHINE-CHECKED HERE: the skeleton-inference call itself — the
    run [AP-AbsCheck] launches for the body [f y], inside the argument-pat
    of [AT-App], at a context of exactly the shape [AT-Abs] builds — admits
    TWO derivations whose output contexts differ in LENGTH:

        route A  ([U-GhostR] at the cell)  ⊣ Θ             (4 entries)
        route B  ([U-FlexL]  at the cell)  ⊣ Θ + 1 entry   (δ̂1 ≔ ε̂, ε̂)

    and no swap chain relates them ([probe_pat_outputs_not_swap_related]),
    so a completeness motive whose conclusion is swap-equality of contexts
    ([consis_call_complete]'s, and any level-6 mirror of it) is FALSE at a
    call skeleton inference PRESENTS.  ⇒ No restriction can both hold at
    the flagship's calls and exclude the divergent cells; the two-context
    problem (handover §4) must be solved, not fenced off.

    ⚙ INSPECTED, NOT CHECKED: that the probe's context is the one the
    pipeline builds for the program above — (1)–(2) name the constructing
    rules; the probe takes the context as given and checks the
    derivations from there. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_shapes.
Require Import src.frost.algo.def_rules.
Require Import src.frost.algo.prop_swap.
Require Import src.frost.ext_algo.notations.
Require Import src.frost.ext_algo.def_supply.
Require Import src.frost.ext_algo.def_guess.
Require Import src.frost.ext_algo.def_consis.
Require Import src.frost.ext_algo.def_look.
Require Import src.frost.ext_algo.def_solve.
Require Import src.frost.ext_algo.def_extract.
Require Import src.frost.ext_algo.def_sub.
Require Import src.frost.ext_algo.def_pat.
Require Import src.frost.ext_algo.prop_solve_det.

Open Scope frost_a_scope.
Open Scope frost_e_scope.

(** The context after (1)–(2): y at skeleton ◇ (the argument's own binder),
    f at the guessed arrow type, then the guess's two deposited flexibles. *)
Definition probe_pf_ctx (y f δ1 δ2 : atom) : aenv :=
  (y ~ abind_var_skl pskl_hole)
  ++ (f ~ abind_var_typ (ptyp_arrow (ptyp_var_f δ1) (ptyp_var_f δ2)))
  ++ (δ1 ~ abind_flex_mono) ++ (δ2 ~ abind_flex_mono) ++ nil.

(** Route B's output: δ̂1 solved to the flexible [guess^TY(◇)] invents. *)
Definition probe_pf_ctx_solved (y f δ1 δ2 ε : atom) : aenv :=
  (y ~ abind_var_skl pskl_hole)
  ++ (f ~ abind_var_typ (ptyp_arrow (ptyp_var_f δ1) (ptyp_var_f δ2)))
  ++ (δ1 ~ abind_flex_mono_def (ptyp_var_f ε))
  ++ (ε ~ abind_flex_mono) ++ (δ2 ~ abind_flex_mono) ++ nil.

Definition probe_pf_body (y f : atom) : exp :=
  exp_app (exp_var_f f) (exp_var_f y).

(* --------------------------------------------------------------------- *)
(*  Route A: the cell is answered by [U-GhostR] — context UNCHANGED.      *)
(* --------------------------------------------------------------------- *)

Lemma probe_pat_ghostr_route : forall S y f δ1 δ2,
  {{ S ↝ S ⊨ (probe_pf_ctx y f δ1 δ2) ⊢ˢ[ mode_tc ; pskl_hole ]
     (probe_pf_body y f) ⦂ (pskl_tophole (pskl_var_f δ2))
     ⊣ (probe_pf_ctx y f δ1 δ2) }}e.
Proof.
  intros. unfold probe_pf_body.
  apply e_pat__app with (S1 := S) (Θ1 := probe_pf_ctx y f δ1 δ2)
    (P0 := pskl_hole) (P := pskl_var_f δ1).
  - (* pat y at (tc, ◇): the skeleton-◇ binder echoes ◇ (Ghost). *)
    apply e_pat__var_skl with (P := pskl_hole).
    + unfold probe_pf_ctx, binds. simpl. auto.
    + apply e_sub__ghost.
  - (* pat f at (fn tc, ◇→◇): Arrow pairs ◇ against δ̂1 — the cell. *)
    apply e_pat__var
      with (A := ptyp_arrow (ptyp_var_f δ1) (ptyp_var_f δ2)).
    + unfold probe_pf_ctx, binds. simpl. auto.
    + simpl.
      apply e_sub__arrow with (S1 := S) (Θ1 := probe_pf_ctx y f δ1 δ2).
      * (* THE CELL, route A: U-GhostR — pattern ◇ answers the subject. *)
        apply e_consis__ghost_r. clear. simpl. fsetdec.
      * apply e_sub__univ_ghost_r. apply guarded_pskl__var.
Qed.

(* --------------------------------------------------------------------- *)
(*  Route B: the SAME call, [U-FlexL] at the cell — δ̂1 gets SOLVED.       *)
(* --------------------------------------------------------------------- *)

Lemma probe_pat_flexl_route : forall S y f δ1 δ2 ε,
  ε `notin` S ->
  {{ S ↝ (add ε S) ⊨ (probe_pf_ctx y f δ1 δ2) ⊢ˢ[ mode_tc ; pskl_hole ]
     (probe_pf_body y f) ⦂ (pskl_tophole (pskl_var_f δ2))
     ⊣ (probe_pf_ctx_solved y f δ1 δ2 ε) }}e.
Proof.
  intros * Hε. unfold probe_pf_body.
  apply e_pat__app with (S1 := S) (Θ1 := probe_pf_ctx y f δ1 δ2)
    (P0 := pskl_hole) (P := pskl_var_f δ1).
  - apply e_pat__var_skl with (P := pskl_hole).
    + unfold probe_pf_ctx, binds. simpl. auto.
    + apply e_sub__ghost.
  - apply e_pat__var
      with (A := ptyp_arrow (ptyp_var_f δ1) (ptyp_var_f δ2)).
    + unfold probe_pf_ctx, binds. simpl. auto.
    + simpl.
      apply e_sub__arrow
        with (S1 := add ε S) (Θ1 := probe_pf_ctx_solved y f δ1 δ2 ε).
      * (* THE CELL, route B: U-FlexL — nonflex{◇} holds, so the rules
           may ASSIGN δ̂1 ≔ ◇, and [guess^TY(◇)] invents ε̂. *)
        apply e_consis__flex_l.
        { split; [ apply lc_pskl_hole | intros Hf; inversion Hf ]. }
        unfold probe_pf_ctx, probe_pf_ctx_solved.
        apply e_assign__skip_tm_skl.
        apply e_assign__skip_tm_var.
        replace ((δ1 ~ abind_flex_mono_def (ptyp_var_f ε))
                   ++ (ε ~ abind_flex_mono) ++ (δ2 ~ abind_flex_mono) ++ nil)
          with ((δ1 ~ abind_flex_mono_def (ptyp_var_f ε))
                  ++ ((ε ~ abind_flex_mono) ++ nil) ++ nil
                  ++ (δ2 ~ abind_flex_mono) ++ nil)
          by (simpl_env; reflexivity).
        apply e_assign__solve_m.
        { simpl. clear. fsetdec. }
        { apply e_guess_mono__hole. assumption. }
        { apply mono_ptyp__var. }
      * apply e_sub__univ_ghost_r. apply guarded_pskl__var.
Qed.

(* --------------------------------------------------------------------- *)
(*  The two outputs are not related by ANY swap chain: a swap preserves   *)
(*  the context's LENGTH, and route B's output has one entry more.        *)
(* --------------------------------------------------------------------- *)

Lemma probe_swap_aenv_length : forall a b Θ,
  length (swap_aenv a b Θ) = length Θ.
Proof. intros. unfold swap_aenv. apply List.length_map. Qed.

Lemma probe_swaps_aenv_length : forall ps Θ,
  length (swaps_aenv ps Θ) = length Θ.
Proof.
  induction ps as [| [a b] ps IH]; intros; simpl.
  - reflexivity.
  - rewrite IH. apply probe_swap_aenv_length.
Qed.

Lemma probe_pat_outputs_not_swap_related : forall y f δ1 δ2 ε ps,
  swaps_aenv ps (probe_pf_ctx_solved y f δ1 δ2 ε) <> probe_pf_ctx y f δ1 δ2.
Proof.
  intros * Heq.
  assert (Hl := probe_swaps_aenv_length ps (probe_pf_ctx_solved y f δ1 δ2 ε)).
  rewrite Heq in Hl.
  unfold probe_pf_ctx, probe_pf_ctx_solved in Hl. simpl in Hl.
  discriminate Hl.
Qed.
