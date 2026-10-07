(** PROBE (2026-08-17): ⛔ THE ALIAS-COLLAPSE TRANSPORT IS FALSE AS AN
    EQUALITY — the FIFTH refuted design for the two-context relation
    (docs/HANDOFF-close-consis-unrestricted.md §4, §5 (R1)).

    (R1)'s step 3 wanted: a derivation at an alias-carrying context [Θ]
    yields one at [collapse1 γ ε Θ] whose output is
    [collapse1 γ ε] of the original's output.  That is FALSE, and the
    residual difference is not a freshness artefact — it is an
    ORIENTATION choice between two PRE-EXISTING variables, which the
    completeness motive's swap chain (fresh names only, [a,b ∉ S0])
    cannot express.

    THE CONFIGURATION.  Context [(γ̂ ≔ ε̂, ε̂, α̂)], walk target [α̂],
    payload the ALIAS VARIABLE [γ̂] itself:

      ORIGINAL   the walk hits the alias entry, so it MUST take
                 [Assign-Assign] (a defined head has no skip row); that
                 substitutes [ε̂] for [γ̂] in the payload, so the premise
                 is a consistency between TWO FLEXIBLES — [U-Flex], i.e.
                 a UNIFY, not a walk — and [Flex-Flex-R] orients it as
                 [ε̂ ≔ α̂].     output  (γ̂ ≔ ε̂, ε̂ ≔ α̂, α̂)
                 collapse1 γ ε of that =  (γ̂ ≔ α̂, α̂)

      COLLAPSED  [(γ̂, α̂)] has no alias entry, so the walk just proceeds:
                 [Assign-Depend] moves [γ̂] into the block (the payload
                 mentions it), then [Assign-SolveM] at the target.
                 output  (α̂ ≔ γ̂, γ̂)                     ← and UNIQUELY so

    [(α̂ ≔ γ̂, γ̂)] and [(γ̂ ≔ α̂, α̂)] are EQUI-GENERAL — same equivalence
    class {α̂, γ̂}, different REPRESENTATIVE — but they are not equal, and
    they are not related by any fresh-name renaming.  ⭐ Note they ARE
    related by the transposition [α̂ ↔ γ̂]; the obstruction is precisely
    that this transposition moves names the coverage hypothesis pins.

    ⇒ A successor relation must be SEMANTIC (equi-generality, i.e.
    [a_inc] in BOTH directions), not the collapse FUNCTION.  ⚙ What
    survives untouched: [e_assign_absorb] (ext_algo/prop_consis_alias.v
    §3), which is about ONE side and was the piece §8c.12c predicted;
    and §1–§2 of that file, which characterise the ◇-walk and compute
    the collapse.

    WHAT IS MACHINE-CHECKED HERE:
      (1) [probe_orient_original] — the original derivation, with its
          output spelled out;
      (2) [probe_orient_collapsed_unique] — the collapsed walk's output
          is UNIQUELY [(α̂ ≔ γ̂, γ̂)] (both steps inverted, so this is not
          merely "one derivation gives that");
      (3) [probe_orient_differ] — the two are different contexts, hence
          no collapsed derivation meets the transport's conclusion. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.prop_swap.
Require Import src.fresco.algo.consis.prop_consis_rename.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.def_supply.
Require Import src.fresco.ext_algo.def_guess.
Require Import src.fresco.ext_algo.def_consis.
Require Import src.fresco.ext_algo.prop_consis_alias.

Open Scope fresco_a_scope.
Open Scope fresco_e_scope.

(** The alias-carrying context, and its collapse. *)
Definition po_ctx (γ ε α : atom) : aenv :=
  (γ ~ abind_flex_mono_def (ptyp_var_f ε))
  ++ (ε ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ nil.

Definition po_ctx_collapsed (γ α : atom) : aenv :=
  (γ ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ nil.

(* --------------------------------------------------------------------- *)
(*  (1)  the ORIGINAL derivation — Assign-Assign, then a UNIFY            *)
(* --------------------------------------------------------------------- *)

Lemma probe_orient_original : forall S (γ ε α : atom),
  γ <> ε -> α <> ε -> α <> γ ->
  {{ S ↝ S ⊨ (po_ctx γ ε α) ⊲[ nil ] α ≔ (pskl_var_f γ)
     ⊣ ((γ ~ abind_flex_mono_def (ptyp_var_f ε))
        ++ (ε ~ abind_flex_mono_def (ptyp_var_f α))
        ++ (α ~ abind_flex_mono) ++ nil) }}e.
Proof.
  intros * Hγε Hαε Hαγ. unfold po_ctx.
  apply e_assign__assign with (τ := ptyp_var_f ε) (Q := pskl_var_f α).
  - (* the target is flexible *)
    left. simpl. auto.
  - (* the payload's γ became ε, so the premise pairs TWO flexibles *)
    simpl_env.
    rewrite subst_pskl_var_eq.
    rewrite subst_pskl_var_neq by exact Hαγ.
    cbn [ptyp_to_pskl].
    apply e_consis__flex.
    (* Flex-Flex-R: the head ε̂ is the RIGHT operand, so ε̂ ≔ α̂ *)
    apply e_unify__flex_r.
    + exact Hαε.
    + left. simpl. auto.
Qed.

(** What the transport's conclusion would demand of the collapsed side. *)
Lemma probe_orient_original_collapsed_output : forall (γ ε α : atom),
  γ <> ε -> α <> ε -> α <> γ ->
  collapse1 γ ε ((γ ~ abind_flex_mono_def (ptyp_var_f ε))
                 ++ (ε ~ abind_flex_mono_def (ptyp_var_f α))
                 ++ (α ~ abind_flex_mono) ++ nil)
  = (γ ~ abind_flex_mono_def (ptyp_var_f α))
    ++ (α ~ abind_flex_mono) ++ nil.
Proof.
  intros * Hγε Hαε Hαγ. unfold collapse1.
  (* ⚙ alternate reduction and case-split: [simpl] stops at each [if], and
     the branch it exposes is what lets the next [simpl] proceed. *)
  repeat (simpl;
          match goal with
          | |- context [ if ?t then _ else _ ] =>
              destruct t; try congruence
          end).
  (* the last [destruct] closed it by [congruence] *)
Qed.

(* --------------------------------------------------------------------- *)
(*  (2)  the COLLAPSED walk's output is UNIQUE                            *)
(* --------------------------------------------------------------------- *)

Lemma probe_orient_collapsed_unique : forall S0 S1 (γ α : atom) Θ',
  α <> γ ->
  {{ S0 ↝ S1 ⊨ (po_ctx_collapsed γ α) ⊲[ nil ] α ≔ (pskl_var_f γ)
     ⊣ Θ' }}e ->
  Θ' = (α ~ abind_flex_mono_def (ptyp_var_f γ))
       ++ (γ ~ abind_flex_mono) ++ nil.
Proof.
  intros * Hαγ Hd. unfold po_ctx_collapsed in Hd.
  (* head γ̂: only [Assign-Depend] — [SolveM]/[UnivGhost-Id] want the head
     to BE the target, [Assign-Skip] wants it out of the payload, and the
     payload IS γ̂. *)
  inversion Hd; subst;
    try congruence;
    try (match goal with
         | Hout : ?b `notin` ftvar_in_pskl ?p |- _ =>
             exfalso; clear - Hout; simpl in Hout; fsetdec
         end).
  match goal with
  | Hd2 : {{ _ ↝ _ ⊨ _ ⊲[ _ ] _ ≔ _ ⊣ _ }}e |- _ =>
      rename Hd2 into Hstep
  end.
  simpl_env in Hstep.
  (* head α̂ IS the target: only [Assign-SolveM] ([UnivGhost-Id] wants a
     ⫯-payload), and [guess^TY] of a variable is the variable. *)
  inversion Hstep; subst; try congruence.
  match goal with
  | Hg : e_guess_mono _ _ _ _ _ |- _ => inversion Hg; subst
  end.
  simpl_env. reflexivity.
Qed.

(* --------------------------------------------------------------------- *)
(*  (3)  the two answers are different contexts                           *)
(* --------------------------------------------------------------------- *)

Lemma probe_orient_differ : forall (γ α : atom),
  α <> γ ->
  (α ~ abind_flex_mono_def (ptyp_var_f γ)) ++ (γ ~ abind_flex_mono) ++ nil
  <> (γ ~ abind_flex_mono_def (ptyp_var_f α)) ++ (α ~ abind_flex_mono)
     ++ nil.
Proof.
  intros * Hαγ Heq. inversion Heq. congruence.
Qed.
