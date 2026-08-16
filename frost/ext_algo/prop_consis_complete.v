(** ext_algo — §8c.10, campaign level 5: COMPLETENESS of the extracted
    [assign] / [unifyvar] / [consistency] block, [e_consis_call_impl].

    ⛔ READ FIRST: docs/HANDOFF-extractable-algo-encoding.md §8c.10b.  The
    level's first scoping — one induction whose motive relates the
    derivation's output context to the runner's UP TO A RENAMING — was
    REFUTED (cex/probe_consis_ghost_flex.v).  At a (ghost pattern,
    flexible subject) node the rules admit both [U-GhostR] and [U-FlexL],
    the runner takes [U-GhostR], and the two output contexts differ by a
    solved-to-fresh-flexible entry: equi-general, but NOT a renaming.
    Repairing that needs a generalization ([⊑]) transport, and it is
    owed at exactly one row, [U-Arrow].

    ⭐ WHAT THIS FILE PROVES INSTEAD, and why it is not a detour: the
    divergence needs a [pskl_hole] on one side, and HOLE-FREENESS IS
    MAINTAINED BY THE WHOLE RECURSION — arrow halves and ∀ openings
    inherit it, and the two rows that rewrite their skeletons
    ([Assign-Assign], [Flex-Flex-Assign]) substitute a [ptyp] payload,
    which has no holes.  So on hole-free inputs the level IS the
    originally-scoped design, and the induction skeleton built here — the
    order's strong induction principle, the dispatch kills, the case
    scripts — is what the [⊑] repair will reuse; only the ghost rows and
    [U-Arrow]'s threading step change.

    ⚙ [unifyvar] is INSIDE the hole-free fragment unconditionally: its
    only consistency premise runs on [ptyp_to_pskl] payloads.  So the
    unify headline needs no restriction. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.Sumbool.
Require Import Metalib.Metatheory.
From Equations Require Import Equations.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_shapes.
Require Import src.frost.prop_coercions.
Require Import src.frost.prop_tag.
Require Import src.frost.algo.prop_swap.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.
Require Import src.frost.prop_basic.
Require Import src.frost.algo.prop_basic.
Require Import src.frost.ext_algo.notations.
Require Import src.frost.ext_algo.def_supply.
Require Import src.frost.ext_algo.def_guess.
Require Import src.frost.ext_algo.def_guess_impl.
Require Import src.frost.ext_algo.prop_guess.
Require Import src.frost.ext_algo.def_consis.
Require Import src.frost.ext_algo.def_order.
Require Import src.frost.ext_algo.prop_consis.
Require Import src.frost.ext_algo.prop_termination.
Require Import src.frost.ext_algo.prop_solve_det.
Require Import src.frost.ext_algo.def_consis_impl.

Set Implicit Arguments.

Open Scope frost_a_scope.
Open Scope frost_e_scope.

(* ===================================================================== *)
(*  §1  Strong induction for [e_consis_call_order]                        *)
(*                                                                        *)
(*  The runner recurses on the ORDER, so completeness must too — and the  *)
(*  order's own [Induction] scheme gives an IH only at the immediate      *)
(*  sub-orders, which is not what the clause list needs (a clause may     *)
(*  consult a premise the SHAPE tests select).  The idiom is              *)
(*  prop_run_complete.v §2a's: hand-write the principle with every        *)
(*  premise DOUBLED — the order premise itself, and its motive            *)
(*  companion — so a case script may use either.                          *)
(*                                                                        *)
(*  ⚙ [Assign-SolveM]'s premise is an [e_guess_mono_order], not a         *)
(*  recursive call, so it is the one premise with no companion.           *)
(* ===================================================================== *)

Section e_consis_call_order_sind.

Variable Qc : supply -> aenv -> consis_call -> Prop.

Hypothesis Hassign : forall S0 Θ Ξ α P,
    (* Assign-SolveM — the head is the target itself, undefined *)
    (forall Θ0,
       Θ = (α ~ abind_flex_mono) ++ Θ0 ->
       e_guess_mono_order S0 P) ->
    (* Assign-Assign — a DEFINED head is substituted away and dropped *)
    (forall β τ Θ0,
       Θ = (β ~ abind_flex_mono_def τ) ++ Θ0 ->
       e_consis_call_order S0 (Ξ ++ Θ0)
         (consis_call_consis empty empty
            (subst_pskl_in_pskl (ptyp_to_pskl τ) β P)
            (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)))) ->
    (forall β τ Θ0,
       Θ = (β ~ abind_flex_mono_def τ) ++ Θ0 ->
       Qc S0 (Ξ ++ Θ0)
         (consis_call_consis empty empty
            (subst_pskl_in_pskl (ptyp_to_pskl τ) β P)
            (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)))) ->
    (* Assign-Depend / Assign-Skip — an undefined non-target head *)
    (forall β Θ0,
       Θ = (β ~ abind_flex_mono) ++ Θ0 ->
       e_consis_call_order S0 Θ0
         (consis_call_assign (Ξ ++ (β ~ abind_flex_mono)) α P)
       /\ e_consis_call_order S0 Θ0 (consis_call_assign Ξ α P)) ->
    (forall β Θ0,
       Θ = (β ~ abind_flex_mono) ++ Θ0 ->
       Qc S0 Θ0 (consis_call_assign (Ξ ++ (β ~ abind_flex_mono)) α P)
       /\ Qc S0 Θ0 (consis_call_assign Ξ α P)) ->
    (* Assign-SkipRigid *)
    (forall β Θ0,
       Θ = (β ~ abind_tvar) ++ Θ0 ->
       e_consis_call_order S0 Θ0 (consis_call_assign Ξ α P)) ->
    (forall β Θ0,
       Θ = (β ~ abind_tvar) ++ Θ0 ->
       Qc S0 Θ0 (consis_call_assign Ξ α P)) ->
    (* Assign-SkipTmVar, both payload sorts *)
    (forall x A Θ0,
       Θ = (x ~ abind_var_typ A) ++ Θ0 ->
       e_consis_call_order S0 Θ0 (consis_call_assign Ξ α P)) ->
    (forall x A Θ0,
       Θ = (x ~ abind_var_typ A) ++ Θ0 ->
       Qc S0 Θ0 (consis_call_assign Ξ α P)) ->
    (forall x Q Θ0,
       Θ = (x ~ abind_var_skl Q) ++ Θ0 ->
       e_consis_call_order S0 Θ0 (consis_call_assign Ξ α P)) ->
    (forall x Q Θ0,
       Θ = (x ~ abind_var_skl Q) ++ Θ0 ->
       Qc S0 Θ0 (consis_call_assign Ξ α P)) ->
    Qc S0 Θ (consis_call_assign Ξ α P).

Hypothesis Hunify : forall S0 Θ α β,
    (* Flex-Flex-Assign *)
    (forall α1 τ Θ0,
       Θ = (α1 ~ abind_flex_mono_def τ) ++ Θ0 ->
       e_consis_call_order S0 Θ0
         (consis_call_consis empty empty
            (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f β)))
            (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f α))))) ->
    (forall α1 τ Θ0,
       Θ = (α1 ~ abind_flex_mono_def τ) ++ Θ0 ->
       Qc S0 Θ0
         (consis_call_consis empty empty
            (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f β)))
            (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f α))))) ->
    (* Flex-Flex-Skip *)
    (forall α1 Θ0,
       Θ = (α1 ~ abind_flex_mono) ++ Θ0 ->
       e_consis_call_order S0 Θ0 (consis_call_unify α β)) ->
    (forall α1 Θ0,
       Θ = (α1 ~ abind_flex_mono) ++ Θ0 ->
       Qc S0 Θ0 (consis_call_unify α β)) ->
    (* Flex-Flex-Skip' — the three other binding sorts *)
    (forall c0 Θ0,
       Θ = (c0 ~ abind_tvar) ++ Θ0 ->
       e_consis_call_order S0 Θ0 (consis_call_unify α β)) ->
    (forall c0 Θ0,
       Θ = (c0 ~ abind_tvar) ++ Θ0 ->
       Qc S0 Θ0 (consis_call_unify α β)) ->
    (forall x A Θ0,
       Θ = (x ~ abind_var_typ A) ++ Θ0 ->
       e_consis_call_order S0 Θ0 (consis_call_unify α β)) ->
    (forall x A Θ0,
       Θ = (x ~ abind_var_typ A) ++ Θ0 ->
       Qc S0 Θ0 (consis_call_unify α β)) ->
    (forall x Q Θ0,
       Θ = (x ~ abind_var_skl Q) ++ Θ0 ->
       e_consis_call_order S0 Θ0 (consis_call_unify α β)) ->
    (forall x Q Θ0,
       Θ = (x ~ abind_var_skl Q) ++ Θ0 ->
       Qc S0 Θ0 (consis_call_unify α β)) ->
    Qc S0 Θ (consis_call_unify α β).

Hypothesis Hconsis : forall S0 Θ Δ1 Δ2 P0 P,
    (* U-Arrow — the sibling runs at the FIRST premise's output context *)
    (forall P0a P0b P1 P2,
       P0 = pskl_arrow P0a P0b -> P = pskl_arrow P1 P2 ->
       e_consis_call_order S0 Θ (consis_call_consis Δ1 Δ2 P0a P1)
       /\ (forall S1 Θ1 Q1,
             {{ S0 ↝ S1 ⊨ Θ ⊢[ Δ1 | Δ2 | P0a ] P1 ∼ Q1 ⊣ Θ1 }}e ->
             e_consis_call_order S1 Θ1 (consis_call_consis Δ1 Δ2 P0b P2))) ->
    (forall P0a P0b P1 P2,
       P0 = pskl_arrow P0a P0b -> P = pskl_arrow P1 P2 ->
       Qc S0 Θ (consis_call_consis Δ1 Δ2 P0a P1)
       /\ (forall S1 Θ1 Q1,
             {{ S0 ↝ S1 ⊨ Θ ⊢[ Δ1 | Δ2 | P0a ] P1 ∼ Q1 ⊣ Θ1 }}e ->
             Qc S1 Θ1 (consis_call_consis Δ1 Δ2 P0b P2))) ->
    (* U-ForallInh *)
    (forall P0' P1,
       P0 = pskl_all_syn P0' -> P = pskl_all_syn P1 ->
       e_consis_call_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ)
         (consis_call_consis
            (add (supply_fresh S0) Δ1) (add (supply_fresh S0) Δ2)
            (open_pskl_wrt_pskl P0' (pskl_var_f (supply_fresh S0)))
            (open_pskl_wrt_pskl P1 (pskl_var_f (supply_fresh S0))))) ->
    (forall P0' P1,
       P0 = pskl_all_syn P0' -> P = pskl_all_syn P1 ->
       Qc (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ)
         (consis_call_consis
            (add (supply_fresh S0) Δ1) (add (supply_fresh S0) Δ2)
            (open_pskl_wrt_pskl P0' (pskl_var_f (supply_fresh S0)))
            (open_pskl_wrt_pskl P1 (pskl_var_f (supply_fresh S0))))) ->
    (* U-ForallSyn *)
    (forall P0' P1,
       P0 = pskl_tophole P0' -> P = pskl_all_syn P1 ->
       e_consis_call_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ)
         (consis_call_consis Δ1 (add (supply_fresh S0) Δ2)
            (pskl_tophole P0')
            (open_pskl_wrt_pskl P1 (pskl_var_f (supply_fresh S0))))) ->
    (forall P0' P1,
       P0 = pskl_tophole P0' -> P = pskl_all_syn P1 ->
       Qc (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ)
         (consis_call_consis Δ1 (add (supply_fresh S0) Δ2)
            (pskl_tophole P0')
            (open_pskl_wrt_pskl P1 (pskl_var_f (supply_fresh S0))))) ->
    (* U-UnivGhost *)
    (forall P0' P1,
       P0 = pskl_tophole P0' -> P = pskl_tophole P1 ->
       e_consis_call_order S0 Θ (consis_call_consis Δ1 Δ2 P0' P1)) ->
    (forall P0' P1,
       P0 = pskl_tophole P0' -> P = pskl_tophole P1 ->
       Qc S0 Θ (consis_call_consis Δ1 Δ2 P0' P1)) ->
    (* U-UnivGhost1 *)
    (forall P0' P1,
       P0 = pskl_all_syn P0' -> P = pskl_tophole P1 ->
       e_consis_call_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ)
         (consis_call_consis (add (supply_fresh S0) Δ1) Δ2
            (open_pskl_wrt_pskl P0' (pskl_var_f (supply_fresh S0)))
            (pskl_tophole P1))) ->
    (forall P0' P1,
       P0 = pskl_all_syn P0' -> P = pskl_tophole P1 ->
       Qc (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ)
         (consis_call_consis (add (supply_fresh S0) Δ1) Δ2
            (open_pskl_wrt_pskl P0' (pskl_var_f (supply_fresh S0)))
            (pskl_tophole P1))) ->
    (* U-UnivGhost2 — strip the subject's ⫯ against a guarded pattern *)
    (forall P1,
       P = pskl_tophole P1 ->
       e_consis_call_order S0 Θ (consis_call_consis Δ1 Δ2 P0 P1)) ->
    (forall P1,
       P = pskl_tophole P1 ->
       Qc S0 Θ (consis_call_consis Δ1 Δ2 P0 P1)) ->
    (* U-UnivGhostR — strip the pattern's ⫯ *)
    (forall P0',
       P0 = pskl_tophole P0' ->
       e_consis_call_order S0 Θ (consis_call_consis Δ1 Δ2 P0' P)) ->
    (forall P0',
       P0 = pskl_tophole P0' ->
       Qc S0 Θ (consis_call_consis Δ1 Δ2 P0' P)) ->
    (* U-Flex *)
    (forall α β,
       P = pskl_var_f α -> P0 = pskl_var_f β ->
       e_consis_call_order S0 Θ (consis_call_unify α β)) ->
    (forall α β,
       P = pskl_var_f α -> P0 = pskl_var_f β ->
       Qc S0 Θ (consis_call_unify α β)) ->
    (* U-FlexL *)
    (forall α,
       P = pskl_var_f α ->
       e_consis_call_order S0 Θ (consis_call_assign nil α P0)) ->
    (forall α,
       P = pskl_var_f α ->
       Qc S0 Θ (consis_call_assign nil α P0)) ->
    (* U-FlexR *)
    (forall α,
       P0 = pskl_var_f α ->
       e_consis_call_order S0 Θ (consis_call_assign nil α P)) ->
    (forall α,
       P0 = pskl_var_f α ->
       Qc S0 Θ (consis_call_assign nil α P)) ->
    Qc S0 Θ (consis_call_consis Δ1 Δ2 P0 P).

Fixpoint e_consis_call_order_sind S0 Θ c
    (H : e_consis_call_order S0 Θ c) {struct H} : Qc S0 Θ c :=
  match H in e_consis_call_order S0' Θ' c' return Qc S0' Θ' c' with
  | e_consis_call_order__assign _ _ _ _ _ p1 p2 p3 p4 p5 p6 =>
      @Hassign _ _ _ _ _
        p1
        p2
        (fun β τ Θ0 E => e_consis_call_order_sind (p2 β τ Θ0 E))
        p3
        (fun β Θ0 E =>
           match p3 β Θ0 E with
           | conj Ha Hb =>
               conj (e_consis_call_order_sind Ha)
                    (e_consis_call_order_sind Hb)
           end)
        p4
        (fun β Θ0 E => e_consis_call_order_sind (p4 β Θ0 E))
        p5
        (fun x A Θ0 E => e_consis_call_order_sind (p5 x A Θ0 E))
        p6
        (fun x Q Θ0 E => e_consis_call_order_sind (p6 x Q Θ0 E))
  | e_consis_call_order__unify _ _ _ _ p1 p2 p3 p4 p5 =>
      @Hunify _ _ _ _
        p1
        (fun α1 τ Θ0 E => e_consis_call_order_sind (p1 α1 τ Θ0 E))
        p2
        (fun α1 Θ0 E => e_consis_call_order_sind (p2 α1 Θ0 E))
        p3
        (fun c0 Θ0 E => e_consis_call_order_sind (p3 c0 Θ0 E))
        p4
        (fun x A Θ0 E => e_consis_call_order_sind (p4 x A Θ0 E))
        p5
        (fun x Q Θ0 E => e_consis_call_order_sind (p5 x Q Θ0 E))
  | e_consis_call_order__consis _ _ _ _ _ _
      q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 =>
      @Hconsis _ _ _ _ _ _
        q1
        (fun P0a P0b P1 P2 E1 E2 =>
           match q1 P0a P0b P1 P2 E1 E2 with
           | conj Ha Hb =>
               conj (e_consis_call_order_sind Ha)
                    (fun S1 Θ1 Q1 Hrun =>
                       e_consis_call_order_sind (Hb S1 Θ1 Q1 Hrun))
           end)
        q2
        (fun P0' P1 E1 E2 => e_consis_call_order_sind (q2 P0' P1 E1 E2))
        q3
        (fun P0' P1 E1 E2 => e_consis_call_order_sind (q3 P0' P1 E1 E2))
        q4
        (fun P0' P1 E1 E2 => e_consis_call_order_sind (q4 P0' P1 E1 E2))
        q5
        (fun P0' P1 E1 E2 => e_consis_call_order_sind (q5 P0' P1 E1 E2))
        q6
        (fun P1 E => e_consis_call_order_sind (q6 P1 E))
        q7
        (fun P0' E => e_consis_call_order_sind (q7 P0' E))
        q8
        (fun α β E1 E2 => e_consis_call_order_sind (q8 α β E1 E2))
        q9
        (fun α E => e_consis_call_order_sind (q9 α E))
        q10
        (fun α E => e_consis_call_order_sind (q10 α E))
  end.

End e_consis_call_order_sind.

(* ===================================================================== *)
(*  §2  HOLE-FREENESS, and why it is an INVARIANT of the whole recursion  *)
(*                                                                        *)
(*  §8c.10b's divergence needs a [◇] on one side — [U-GhostR] against     *)
(*  [U-FlexL] at (pattern ◇, subject α̂), and its mirror.  Hole-freeness    *)
(*  therefore excludes it, and it is MAINTAINED everywhere the block       *)
(*  recurses:                                                             *)
(*                                                                        *)
(*    - the structural rows take sub-skeletons (arrow halves, the ⫯       *)
(*      strips) or open a ∀ body with a VARIABLE — [pskl_no_hole_open];   *)
(*    - [Assign-Assign] and [Flex-Flex-Assign], the only rows that        *)
(*      REWRITE their skeletons, substitute a definition PAYLOAD, and a   *)
(*      payload is a [ptyp], which has no holes at all                     *)
(*      ([ptyp_to_pskl_no_hole] + [pskl_no_hole_subst]);                  *)
(*    - [U-FlexL] / [U-FlexR] hand the assign layer the pattern or the    *)
(*      subject unchanged.                                                *)
(*                                                                        *)
(*  ⭐ So [unifyvar] is inside the fragment UNCONDITIONALLY: a unify call  *)
(*  carries no skeleton, and its one consistency premise runs on          *)
(*  [ptyp_to_pskl] payloads.  That is why the unify headline needs no     *)
(*  restriction while the assign / consistency ones do.                    *)
(* ===================================================================== *)

Definition consis_call_no_hole (c : consis_call) : Prop :=
  match c with
  | consis_call_assign _ _ P    => pskl_no_hole P
  | consis_call_unify _ _       => True
  | consis_call_consis _ _ P0 P => pskl_no_hole P0 /\ pskl_no_hole P
  end.

(** [Assign-Assign]'s recursive call: the payload is substituted into both
    the pattern and the target variable, and neither can gain a hole. *)
Lemma consis_call_no_hole_assign_assign : forall (α : atom) (P : pskl)
    (β : atom) (τ : ptyp),
  pskl_no_hole P ->
  consis_call_no_hole
    (consis_call_consis empty empty
       (subst_pskl_in_pskl (ptyp_to_pskl τ) β P)
       (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α))).
Proof.
  intros. split; apply pskl_no_hole_subst;
    auto using ptyp_to_pskl_no_hole; simpl; exact I.
Qed.

(** [Flex-Flex-Assign]'s: both sides are payload views outright. *)
Lemma consis_call_no_hole_flex_assign : forall (τ : ptyp)
    (α1 α β : atom),
  consis_call_no_hole
    (consis_call_consis empty empty
       (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f β)))
       (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f α)))).
Proof. intros. split; apply ptyp_to_pskl_no_hole. Qed.

(** The ∀ rows open with a VARIABLE. *)
Lemma consis_call_no_hole_open : forall (Δ1 Δ2 : atoms)
    (P0 P : pskl) (α : atom),
  pskl_no_hole P0 -> pskl_no_hole P ->
  consis_call_no_hole
    (consis_call_consis Δ1 Δ2
       (open_pskl_wrt_pskl P0 (pskl_var_f α))
       (open_pskl_wrt_pskl P (pskl_var_f α))).
Proof. intros. split; apply pskl_no_hole_open; assumption. Qed.

#[local] Hint Resolve ptyp_to_pskl_no_hole pskl_no_hole_open
  pskl_no_hole_subst consis_call_no_hole_assign_assign
  consis_call_no_hole_flex_assign consis_call_no_hole_open : nohole.

(* ===================================================================== *)
(*  §3  EQUIVARIANCE ALONG A CHAIN                                        *)
(*                                                                        *)
(*  What [U-Arrow] will consume.  Its second premise runs at the FIRST    *)
(*  premise's output, and the derivation's output differs from the        *)
(*  runner's by the fresh names each side happened to pick — a whole      *)
(*  CHAIN of transpositions, not one.  prop_consis.v §10 iterates: the    *)
(*  Δ-slots stay LITERAL (each step feeds the next its own                *)
(*  [swap_atoms], so no set ever has to be moved across [=]), and only    *)
(*  the supply is carried up to [=], which is where prop_consis.v §9's    *)
(*  supply-respect discharges the empty chain.                            *)
(*                                                                        *)
(*  ⚙ The chain acts as the IDENTITY on anything the caller already held  *)
(*  — that is [swaps_pskl_fresh_id] / [swaps_atom_notin]                  *)
(*  (prop_solve_det.v §1), given that every pair in the chain avoids the  *)
(*  input supply.                                                         *)
(* ===================================================================== *)

Lemma e_assign_swaps : forall ps S0 Θ0 Ξ α P S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
  forall S0', S0' [=] swaps_atoms ps S0 ->
  exists S1', S1' [=] swaps_atoms ps S1 /\
    {{ S0' ↝ S1' ⊨ (swaps_aenv ps Θ0) ⊲[ swaps_aenv ps Ξ ]
       (swaps_atom ps α) ≔ (swaps_pskl ps P) ⊣ (swaps_aenv ps Θ1) }}e.
Proof.
  induction ps as [ | [a b] ps IH ]; intros * Hd S0' Heq; simpl in *.
  - (* the empty chain is the identity — only the supply has to move *)
    exact (e_assign_supply_respect Hd Heq).
  - assert (Hr : swap_atoms a b S0 [=] swap_atoms a b S0) by reflexivity.
    destruct (e_assign_swap Hd Hr) as [S1a [HS1a Hda]].
    destruct (IH _ _ _ _ _ _ _ Hda _ Heq) as [S1' [HS1' Hd']].
    exists S1'. split; [ | exact Hd' ].
    rewrite HS1'. apply swaps_atoms_cong. exact HS1a.
Qed.

Lemma e_unify_swaps : forall ps S0 Θ0 α β S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}e ->
  forall S0', S0' [=] swaps_atoms ps S0 ->
  exists S1', S1' [=] swaps_atoms ps S1 /\
    {{ S0' ↝ S1' ⊨ (swaps_aenv ps Θ0) ⊲
       (swaps_atom ps α) ≈ᵘ (swaps_atom ps β) ⊣ (swaps_aenv ps Θ1) }}e.
Proof.
  induction ps as [ | [a b] ps IH ]; intros * Hd S0' Heq; simpl in *.
  - exact (e_unify_supply_respect Hd Heq).
  - assert (Hr : swap_atoms a b S0 [=] swap_atoms a b S0) by reflexivity.
    destruct (e_unify_swap Hd Hr) as [S1a [HS1a Hda]].
    destruct (IH _ _ _ _ _ _ Hda _ Heq) as [S1' [HS1' Hd']].
    exists S1'. split; [ | exact Hd' ].
    rewrite HS1'. apply swaps_atoms_cong. exact HS1a.
Qed.

(** ⚙ The Δ-slots are taken as [=]-VARIANTS, exactly as [e_consis_swap]
    takes them and for the same reason: a caller that has to hold the
    chain's action on a Δ fixed ([U-Arrow], where every pair dodges the
    input supply and the two Δs live inside it) holds a [swaps_atoms_notin]
    proof, not the term.  prop_consis.v §9's [e_consis_delta_respect] is
    what discharges it at the empty chain. *)
Lemma e_consis_swaps : forall ps Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}e ->
  forall Δ1' Δ2' S0',
  Δ1' [=] swaps_atoms ps Δ1 -> Δ2' [=] swaps_atoms ps Δ2 ->
  S0' [=] swaps_atoms ps S0 ->
  exists S1', S1' [=] swaps_atoms ps S1 /\
    {{ S0' ↝ S1' ⊨ (swaps_aenv ps Θ0)
       ⊢[ Δ1' | Δ2' | (swaps_pskl ps P0) ]
       (swaps_pskl ps P) ∼ (swaps_pskl ps Q) ⊣ (swaps_aenv ps Θ1) }}e.
Proof.
  induction ps as [ | [a b] ps IH ];
    intros * Hd Δ1' Δ2' S0' HD1 HD2 HS; simpl in *.
  - destruct (e_consis_supply_respect Hd HS) as [S1' [HS1 Hd']].
    exists S1'. split; [ exact HS1 | ].
    eapply e_consis_delta_respect; eassumption.
  - assert (H1 : swap_atoms a b Δ1 [=] swap_atoms a b Δ1) by reflexivity.
    assert (H2 : swap_atoms a b Δ2 [=] swap_atoms a b Δ2) by reflexivity.
    assert (Hr : swap_atoms a b S0 [=] swap_atoms a b S0) by reflexivity.
    destruct (e_consis_swap Hd H1 H2 Hr) as [S1a [HS1a Hda]].
    destruct (IH _ _ _ _ _ _ _ _ _ Hda _ _ _ HD1 HD2 HS)
      as [S1' [HS1' Hd']].
    exists S1'. split; [ | exact Hd' ].
    rewrite HS1'. apply swaps_atoms_cong. exact HS1a.
Qed.

(** [guess^TY] along a chain — the same iteration, on the judgement
    [Assign-SolveM] calls. *)
Lemma e_guess_mono_swaps : forall ps S0 P S1 Ξ τ,
  e_guess_mono S0 P S1 Ξ τ ->
  forall S0', S0' [=] swaps_atoms ps S0 ->
  exists S1', S1' [=] swaps_atoms ps S1 /\
    e_guess_mono S0' (swaps_pskl ps P) S1' (swaps_aenv ps Ξ)
      (swaps_ptyp ps τ).
Proof.
  induction ps as [ | [a b] ps IH ]; intros * Hd S0' Heq; simpl in *.
  - exact (e_guess_mono_supply_respect Hd Heq).
  - assert (Hr : swap_atoms a b S0 [=] swap_atoms a b S0) by reflexivity.
    destruct (e_guess_mono_swap Hd Hr) as [S1a [HS1a Hda]].
    destruct (IH _ _ _ _ _ Hda _ Heq) as [S1' [HS1' Hd']].
    exists S1'. split; [ | exact Hd' ].
    rewrite HS1'. apply swaps_atoms_cong. exact HS1a.
Qed.

(* --------------------------------------------------------------------- *)
(*  §3b  ⭐ [guess^TY] IS DETERMINISTIC UP TO A FRESH RENAMING            *)
(*                                                                        *)
(*  [Assign-SolveM] is the level's one GENERATIVE row: the derivation's    *)
(*  invented block and the runner's are both drawn "fresh for [S0]" and    *)
(*  so differ by a renaming, which is where the induction's pair list      *)
(*  grows.  This is that renaming, and it is the ONE place in the level    *)
(*  where two arbitrary derivations are compared — legitimate here because *)
(*  [guess^TY] is syntax-directed (prop_guess.v §9's inversions are        *)
(*  unconditional), so the runner-sided doctrine has nothing to protect.   *)
(*                                                                        *)
(*  ⚙ SIZE induction, not induction on either derivation: the arrow row    *)
(*  threads, so its second halves sit at DIFFERENT input supplies, and a   *)
(*  derivation-indexed IH would be pinned to one of them.  With the size   *)
(*  the second call is made after the first half's renaming has already    *)
(*  moved one side onto the other's rails.                                 *)
(* --------------------------------------------------------------------- *)

(** ⚠️ [repeat split] INTRODUCES PRODUCTS (Coq's [constructor] does), so it
    dives straight through the [forall a b] conjunct and leaves goals with
    the pair already introduced.  Four goals, spelled out. *)
Local Ltac rel4 := split; [ | split; [ | split ] ].

Lemma e_guess_mono_rel_n : forall n S0 P S1 Ξ A,
  size_pskl P <= n ->
  e_guess_mono S0 P S1 Ξ A ->
  ftvar_in_pskl P [<=] S0 ->
  forall S1' Ξ' A', e_guess_mono S0 P S1' Ξ' A' ->
  exists ps,
    (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0) /\
    swaps_atoms ps S1 [=] S1' /\
    swaps_aenv ps Ξ = Ξ' /\
    swaps_ptyp ps A = A'.
Proof.
  induction n as [ | n IH ]; intros S0 P S1 Ξ A Hsz Hd Hcov S1' Ξ' A' Hd'.
  { destruct P; simpl in Hsz; lia. }
  destruct P.
  - (* unit *)
    destruct (e_guess_mono_inv_unit Hd) as [-> [-> ->]].
    destruct (e_guess_mono_inv_unit Hd') as [-> [-> ->]].
    exists nil. rel4; simpl; try reflexivity. intros ? ? [].
  - (* var_b — no rule *) destruct (e_guess_mono_inv_var_b Hd).
  - (* var_f *)
    destruct (e_guess_mono_inv_var Hd) as [-> [-> ->]].
    destruct (e_guess_mono_inv_var Hd') as [-> [-> ->]].
    exists nil. rel4; simpl; try reflexivity. intros ? ? [].
  - (* arrow — the threading row *)
    destruct (e_guess_mono_inv_arrow Hd)
      as [Sa [Xa [Xb [Aa [Ab [-> [-> [D1 D2]]]]]]]].
    destruct (e_guess_mono_inv_arrow Hd')
      as [Sa' [Xa' [Xb' [Aa' [Ab' [-> [-> [D1' D2']]]]]]]].
    simpl in Hsz, Hcov.
    destruct (IH S0 P1 Sa Xa Aa ltac:(lia) D1
                 ltac:(clear - Hcov; fsetdec) Sa' Xa' Aa' D1')
      as [ps1 [Hav1 [HS1 [HX1 HA1]]]].
    assert (HP2 : swaps_pskl ps1 P2 = P2)
      by (apply swaps_pskl_fresh_id; intros a0 b0 Hin;
          destruct (Hav1 a0 b0 Hin) as [Ha0 Hb0]; split;
          clear - Ha0 Hb0 Hcov; fsetdec).
    assert (Heq2 : Sa' [=] swaps_atoms ps1 Sa) by (symmetry; exact HS1).
    destruct (e_guess_mono_swaps ps1 D2 Heq2) as [S2t [HS2t D2t]].
    rewrite HP2 in D2t.
    pose proof (e_guess_mono_supply_grows D1') as Hgr1'.
    destruct (IH Sa' P2 S2t (swaps_aenv ps1 Xb) (swaps_ptyp ps1 Ab)
                 ltac:(lia) D2t ltac:(clear - Hcov Hgr1'; fsetdec)
                 S1' Xb' Ab' D2')
      as [ps2 [Hav2 [HS2 [HX2 HA2]]]].
    (* what the SECOND renaming must leave alone: the first half's yield *)
    pose proof (e_guess_mono_generated_in_supply D1') as Hdom1'.
    pose proof (e_guess_mono_generated_ftvar D1') as Hftv1'.
    pose proof (e_guess_mono_ftv D1') as HftA1'.
    assert (HX1' : swaps_aenv ps2 Xa' = Xa')
      by (apply swaps_aenv_fresh_id; intros a0 b0 Hin;
          destruct (Hav2 a0 b0 Hin) as [Ha0 Hb0]; split;
          clear - Ha0 Hb0 Hdom1' Hftv1'; fsetdec).
    assert (HA1' : swaps_ptyp ps2 Aa' = Aa')
      by (apply swaps_ptyp_fresh_id; intros a0 b0 Hin;
          destruct (Hav2 a0 b0 Hin) as [Ha0 Hb0]; split;
          clear - Ha0 Hb0 Hdom1' HftA1' Hcov Hgr1'; fsetdec).
    exists (ps1 ++ ps2). rel4.
    + intros a0 b0 Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      * exact (Hav1 a0 b0 Hin).
      * destruct (Hav2 a0 b0 Hin) as [Ha0 Hb0].
        split; clear - Ha0 Hb0 Hgr1'; fsetdec.
    + rewrite swaps_atoms_app. rewrite <- HS2.
      apply swaps_atoms_cong. symmetry. exact HS2t.
    + rewrite swaps_aenv_app, !swaps_aenv_app_dist, HX1, HX2, HX1'.
      reflexivity.
    + rewrite swaps_ptyp_app, !swaps_ptyp_arrow, HA1, HA2, HA1'.
      reflexivity.
  - (* all_syn — the two openers are paired first, by ONE transposition *)
    destruct (e_guess_mono_inv_all_syn Hd) as [β [Aa [Hβ [-> Dp]]]].
    destruct (e_guess_mono_inv_all_syn Hd') as [β' [Aa' [Hβ' [-> Dp']]]].
    simpl in Hsz, Hcov.
    assert (Heqs : add β' S0 [=] swap_atoms β β' (add β S0)).
    { rewrite swap_atoms_add. rewrite (swap_atoms_notin β β' S0 Hβ Hβ').
      unfold swap_atom. destruct (β == β); [ | congruence ]. reflexivity. }
    destruct (e_guess_mono_swap Dp Heqs) as [S1t [HS1t Dpt]].
    rewrite swap_pskl_open_var in Dpt.
    rewrite (swap_pskl_fresh_id β β' P) in Dpt;
      [ | clear - Hcov Hβ; fsetdec | clear - Hcov Hβ'; fsetdec ].
    replace (swap_atom β β' β) with β' in Dpt
      by (unfold swap_atom; destruct (β == β); congruence).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β'))
      as Hup.
    destruct (IH (add β' S0) (open_pskl_wrt_pskl P (pskl_var_f β'))
                 S1t (swap_aenv β β' Ξ) (swap_ptyp β β' Aa)
                 ltac:(rewrite size_pskl_open_pskl_wrt_pskl_var; lia)
                 Dpt ltac:(clear - Hup Hcov; simpl in *; fsetdec)
                 S1' Ξ' Aa' Dp')
      as [ps' [Hav' [HS' [HX' HA']]]].
    exists ((β, β') :: ps'). rel4.
    + intros a0 b0 [Heqp | Hin];
        [ inversion Heqp; subst; split; assumption | ].
      destruct (Hav' a0 b0 Hin) as [Ha0 Hb0].
      split; clear - Ha0 Hb0; fsetdec.
    + cbn [swaps_atoms]. rewrite <- HS'.
      apply swaps_atoms_cong. symmetry. exact HS1t.
    + cbn [swaps_aenv]. exact HX'.
    + cbn [swaps_ptyp swap_ptyp]. rewrite swap_ptyp_close.
      replace (swap_atom β β' β) with β'
        by (unfold swap_atom; destruct (β == β); congruence).
      rewrite swaps_ptyp_all, swaps_ptyp_close, HA'.
      f_equal. f_equal. apply swaps_atom_notin.
      intros a0 b0 Hin. destruct (Hav' a0 b0 Hin) as [Ha0 Hb0].
      split; [ clear - Ha0 | clear - Hb0 ]; fsetdec.
  - (* hole — the row that INVENTS *)
    destruct (e_guess_mono_inv_hole Hd) as [α [Hα [-> [-> ->]]]].
    destruct (e_guess_mono_inv_hole Hd') as [α' [Hα' [-> [-> ->]]]].
    exists ((α, α') :: nil). rel4.
    + intros ? ? [Heqp | []]. inversion Heqp; subst. split; assumption.
    + cbn [swaps_atoms]. rewrite swap_atoms_add.
      rewrite (swap_atoms_notin α α' S0 Hα Hα').
      replace (swap_atom α α' α) with α'
        by (unfold swap_atom; destruct (α == α); congruence).
      reflexivity.
    + rewrite swaps_aenv_app_dist, swaps_aenv_one_flex, swaps_aenv_nil.
      cbn [swaps_atom].
      replace (swap_atom α α' α) with α'
        by (unfold swap_atom; destruct (α == α); congruence).
      reflexivity.
    + rewrite swaps_ptyp_var_f. cbn [swaps_atom].
      replace (swap_atom α α' α) with α'
        by (unfold swap_atom; destruct (α == α); congruence).
      reflexivity.
  - (* tophole *)
    pose proof (e_guess_mono_inv_tophole Hd) as Dp.
    pose proof (e_guess_mono_inv_tophole Hd') as Dp'.
    simpl in Hsz, Hcov.
    exact (IH S0 P S1 Ξ A ltac:(lia) Dp Hcov S1' Ξ' A' Dp').
Qed.

Corollary e_guess_mono_rel : forall S0 P S1 Ξ A S1' Ξ' A',
  e_guess_mono S0 P S1 Ξ A ->
  e_guess_mono S0 P S1' Ξ' A' ->
  ftvar_in_pskl P [<=] S0 ->
  exists ps,
    (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0) /\
    swaps_atoms ps S1 [=] S1' /\
    swaps_aenv ps Ξ = Ξ' /\
    swaps_ptyp ps A = A'.
Proof.
  intros * Hd Hd' Hcov.
  exact (e_guess_mono_rel_n (le_n _) Hd Hcov Hd').
Qed.

(* ===================================================================== *)
(*  §4  ROOT INVERSIONS — the case backbone, machine-checked              *)
(*                                                                        *)
(*  §8c.10b settled by INSPECTION that every (pattern, subject) shape     *)
(*  pair but three admits exactly ONE consistency rule, so the runner's   *)
(*  first-match commits to the derivation's root.  These are that audit   *)
(*  as lemmas: one per clause of the runner's dispatch, each turning a    *)
(*  derivation at the clause's shape into that rule's premises.           *)
(*                                                                        *)
(*  ⭐ NONE of them needs hole-freeness.  [U-Ghost] demands the SUBJECT   *)
(*  be literally [◇] and [U-GhostR] the PATTERN, so at any concrete       *)
(*  shape they cannot fire at all; hole-freeness is what keeps the        *)
(*  recursion away from the two clauses where they can (§8c.10b's         *)
(*  divergence), not what makes these inversions unique.                  *)
(*                                                                        *)
(*  The three genuinely ambiguous pairs are the ones the runner decides   *)
(*  with a flexibility TEST, and they come out as disjunctions whose      *)
(*  branches are EXCLUSIVE — [e_assign_target_flex] (prop_consis.v §8)    *)
(*  is what makes the assign branch imply the very [a_flex_tvar] the      *)
(*  other branch's [a_non_flex] denies.                                    *)
(* ===================================================================== *)

(** After [inversion], the rows that COULD have matched the shape but
    demand [guarded_pskl] of a ∀ / ⫯ / ◇ leave that demand behind; it is
    never derivable, so one [inversion] each closes them. *)
Local Ltac kill_unguarded :=
  repeat match goal with
         | Hg : guarded_pskl (pskl_all_syn _) |- _ => inversion Hg
         | Hg : guarded_pskl (pskl_tophole _) |- _ => inversion Hg
         | Hg : guarded_pskl pskl_hole |- _ => inversion Hg
         end.

(* --- the UNAMBIGUOUS shape pairs: exactly one rule fires --- *)

Lemma e_consis_inv_arrow : forall Δ1 Δ2 S0 Θ0 P0a P0b P1 P2 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_arrow P0a P0b) ]
     (pskl_arrow P1 P2) ∼ Q ⊣ Θ1 }}e ->
  exists Sm Θm Q1 Q2,
    Q = pskl_arrow Q1 Q2 /\
    {{ S0 ↝ Sm ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0a ] P1 ∼ Q1 ⊣ Θm }}e /\
    {{ Sm ↝ S1 ⊨ Θm ⊢[ Δ1 | Δ2 | P0b ] P2 ∼ Q2 ⊣ Θ1 }}e.
Proof. intros * Hd. inversion Hd; subst; kill_unguarded; eauto 10. Qed.

Lemma e_consis_inv_unit : forall Δ1 Δ2 S0 Θ0 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | pskl_unit ] pskl_unit ∼ Q ⊣ Θ1 }}e ->
  Q = pskl_unit /\ S1 = S0 /\ Θ1 = Θ0.
Proof. intros * Hd. inversion Hd; subst; kill_unguarded; auto. Qed.

Lemma e_consis_inv_forall_inh : forall Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_all_syn P0) ]
     (pskl_all_syn P) ∼ Q ⊣ Θ1 }}e ->
  exists α Qb,
    α `notin` S0 /\ Q = pskl_all_syn (close_pskl_wrt_pskl α Qb) /\
    {{ (add α S0) ↝ S1 ⊨ ((α ~ abind_tvar) ++ Θ0)
       ⊢[ (add α Δ1) | (add α Δ2)
         | (open_pskl_wrt_pskl P0 (pskl_var_f α)) ]
       (open_pskl_wrt_pskl P (pskl_var_f α)) ∼ Qb
       ⊣ ((α ~ abind_tvar) ++ Θ1) }}e.
Proof. intros * Hd. inversion Hd; subst; kill_unguarded; eauto 10. Qed.

Lemma e_consis_inv_forall_syn : forall Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_tophole P0) ]
     (pskl_all_syn P) ∼ Q ⊣ Θ1 }}e ->
  exists α Qb,
    α `notin` S0 /\ Q = pskl_all_syn (close_pskl_wrt_pskl α Qb) /\
    {{ (add α S0) ↝ S1 ⊨ ((α ~ abind_tvar) ++ Θ0)
       ⊢[ Δ1 | (add α Δ2) | (pskl_tophole P0) ]
       (open_pskl_wrt_pskl P (pskl_var_f α)) ∼ Qb
       ⊣ ((α ~ abind_tvar) ++ Θ1) }}e.
Proof. intros * Hd. inversion Hd; subst; kill_unguarded; eauto 10. Qed.

Lemma e_consis_inv_univ_ghost : forall Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_tophole P0) ]
     (pskl_tophole P) ∼ Q ⊣ Θ1 }}e ->
  exists Qb,
    Q = pskl_tophole Qb /\
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Qb ⊣ Θ1 }}e.
Proof. intros * Hd. inversion Hd; subst; kill_unguarded; eauto. Qed.

Lemma e_consis_inv_univ_ghost1 : forall Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_all_syn P0) ]
     (pskl_tophole P) ∼ Q ⊣ Θ1 }}e ->
  exists α Qb,
    α `notin` S0 /\ Q = pskl_all_syn (close_pskl_wrt_pskl α Qb) /\
    {{ (add α S0) ↝ S1 ⊨ ((α ~ abind_tvar) ++ Θ0)
       ⊢[ (add α Δ1) | Δ2
         | (open_pskl_wrt_pskl P0 (pskl_var_f α)) ]
       (pskl_tophole P) ∼ Qb ⊣ ((α ~ abind_tvar) ++ Θ1) }}e.
Proof. intros * Hd. inversion Hd; subst; kill_unguarded; eauto 10. Qed.

Lemma e_consis_inv_univ_ghost2_unit : forall Δ1 Δ2 S0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | pskl_unit ]
     (pskl_tophole P) ∼ Q ⊣ Θ1 }}e ->
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | pskl_unit ] P ∼ Q ⊣ Θ1 }}e.
Proof. intros * Hd. inversion Hd; subst; kill_unguarded; auto. Qed.

Lemma e_consis_inv_univ_ghost2_arrow : forall Δ1 Δ2 S0 Θ0 P0a P0b P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_arrow P0a P0b) ]
     (pskl_tophole P) ∼ Q ⊣ Θ1 }}e ->
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_arrow P0a P0b) ] P ∼ Q ⊣ Θ1 }}e.
Proof. intros * Hd. inversion Hd; subst; kill_unguarded; auto. Qed.

Lemma e_consis_inv_univ_ghost_r_unit : forall Δ1 Δ2 S0 Θ0 P0 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_tophole P0) ]
     pskl_unit ∼ Q ⊣ Θ1 }}e ->
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] pskl_unit ∼ Q ⊣ Θ1 }}e.
Proof. intros * Hd. inversion Hd; subst; kill_unguarded; auto. Qed.

Lemma e_consis_inv_univ_ghost_r_arrow : forall Δ1 Δ2 S0 Θ0 P0 P1 P2 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_tophole P0) ]
     (pskl_arrow P1 P2) ∼ Q ⊣ Θ1 }}e ->
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] (pskl_arrow P1 P2) ∼ Q ⊣ Θ1 }}e.
Proof. intros * Hd. inversion Hd; subst; kill_unguarded; auto. Qed.

(* --- a flexible PATTERN against a non-variable subject: only U-FlexR --- *)

Lemma e_consis_inv_flex_r : forall Δ1 Δ2 S0 Θ0 α P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_var_f α) ] P ∼ Q ⊣ Θ1 }}e ->
  (forall β, P <> pskl_var_f β) -> P <> pskl_hole ->
  (forall Pb, P <> pskl_tophole Pb) ->
  Q = pskl_var_f α /\ a_non_flex Θ0 P /\
  {{ S0 ↝ S1 ⊨ Θ0 ⊲[ nil ] α ≔ P ⊣ Θ1 }}e.
Proof.
  intros * Hd Hnv Hnh Hnt. inversion Hd; subst; kill_unguarded;
    try solve [ congruence
              | exfalso; eapply Hnv; reflexivity
              | exfalso; eapply Hnt; reflexivity ].
  all: (split; [ reflexivity | split; assumption ]).
Qed.

(* --- a flexible SUBJECT against a non-variable pattern: only U-FlexL --- *)

Lemma e_consis_inv_flex_l : forall Δ1 Δ2 S0 Θ0 α P0 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] (pskl_var_f α) ∼ Q ⊣ Θ1 }}e ->
  (forall β, P0 <> pskl_var_f β) -> P0 <> pskl_hole ->
  (forall Pb, P0 <> pskl_tophole Pb) ->
  Q = pskl_var_f α /\ a_non_flex Θ0 P0 /\
  {{ S0 ↝ S1 ⊨ Θ0 ⊲[ nil ] α ≔ P0 ⊣ Θ1 }}e.
Proof.
  intros * Hd Hnv Hnh Hnt. inversion Hd; subst; kill_unguarded;
    try solve [ congruence
              | exfalso; eapply Hnv; reflexivity
              | exfalso; eapply Hnt; reflexivity ].
  all: (split; [ reflexivity | split; assumption ]).
Qed.

(* --- the three pairs the runner resolves by a flexibility TEST --- *)

Lemma e_consis_inv_var_tophole : forall Δ1 Δ2 S0 Θ0 β P1 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_var_f β) ]
     (pskl_tophole P1) ∼ Q ⊣ Θ1 }}e ->
  (a_flex_tvar Θ0 β /\ Q = pskl_var_f β /\
     {{ S0 ↝ S1 ⊨ Θ0 ⊲[ nil ] β ≔ (pskl_tophole P1) ⊣ Θ1 }}e)
  \/ (a_non_flex Θ0 (pskl_var_f β) /\
      {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_var_f β) ] P1 ∼ Q ⊣ Θ1 }}e).
Proof.
  intros * Hd. inversion Hd; subst; kill_unguarded.
  - right; auto.
  - left; repeat split; auto. eapply e_assign_target_flex; eassumption.
Qed.

Lemma e_consis_inv_tophole_var : forall Δ1 Δ2 S0 Θ0 α P0 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_tophole P0) ]
     (pskl_var_f α) ∼ Q ⊣ Θ1 }}e ->
  (a_flex_tvar Θ0 α /\ Q = pskl_var_f α /\
     {{ S0 ↝ S1 ⊨ Θ0 ⊲[ nil ] α ≔ (pskl_tophole P0) ⊣ Θ1 }}e)
  \/ (a_non_flex Θ0 (pskl_var_f α) /\
      {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] (pskl_var_f α) ∼ Q ⊣ Θ1 }}e).
Proof.
  intros * Hd. inversion Hd; subst; kill_unguarded.
  - left; repeat split; auto. eapply e_assign_target_flex; eassumption.
  - right; auto.
Qed.

Lemma e_consis_inv_var_var : forall Δ1 Δ2 S0 Θ0 α β Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_var_f β) ]
     (pskl_var_f α) ∼ Q ⊣ Θ1 }}e ->
  (* U-Rigid *)
  (α = β /\ binds α abind_tvar Θ0 /\ Q = pskl_var_f α /\
     S1 = S0 /\ Θ1 = Θ0)
  (* U-Flex *)
  \/ (Q = pskl_var_f α /\ {{ S0 ↝ S1 ⊨ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}e)
  (* U-FlexL — the SUBJECT variable is assigned *)
  \/ (a_non_flex Θ0 (pskl_var_f β) /\ Q = pskl_var_f α /\
      {{ S0 ↝ S1 ⊨ Θ0 ⊲[ nil ] α ≔ (pskl_var_f β) ⊣ Θ1 }}e)
  (* U-FlexR — the PATTERN variable is assigned *)
  \/ (a_non_flex Θ0 (pskl_var_f α) /\ Q = pskl_var_f β /\
      {{ S0 ↝ S1 ⊨ Θ0 ⊲[ nil ] β ≔ (pskl_var_f α) ⊣ Θ1 }}e).
Proof.
  intros * Hd. inversion Hd; subst; kill_unguarded.
  - left; repeat split; auto.
  - right; left; auto.
  - right; right; left; auto.
  - right; right; right; auto.
Qed.

(* --- the two WALKS: one inversion per head shape --------------------- *)
(*                                                                        *)
(*  The context-walking clauses of the dispatch.  Each is unambiguous     *)
(*  once the head's BINDING SHAPE is fixed, except at a bare flexible     *)
(*  head, where [Assign-Depend] and [Assign-Skip] split on the same       *)
(*  occurrence test the runner performs.                                  *)

(** [Flex-Flex-Skip'] fires at a rigid / term-variable head only; wherever
    the head is a FLEXIBLE its binding-shape premise refutes. *)
Local Ltac kill_skip_other :=
  match goal with
  | H : _ = abind_tvar \/ (exists _, _ = abind_var_typ _) \/
        (exists _, _ = abind_var_skl _) |- _ =>
      solve [ destruct H as [Hb | [[? Hb] | [? Hb]]]; discriminate ]
  end.

Lemma e_assign_inv_nil : forall S0 Ξ α P S1 Θ1,
  {{ S0 ↝ S1 ⊨ nil ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e -> False.
Proof. intros * Hd. inversion Hd. Qed.

(** The head IS the target: [Assign-UnivGhost-Id] against
    [Assign-SolveM], and the occurs check separates them. *)
Lemma e_assign_inv_flex_self : forall S0 Θ0 Ξ α P S1 Θ1,
  {{ S0 ↝ S1 ⊨ ((α ~ abind_flex_mono) ++ Θ0) ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
  (Ξ = nil /\ P = pskl_tophole (pskl_var_f α) /\ S1 = S0 /\
     Θ1 = (α ~ abind_flex_mono) ++ Θ0)
  \/ (α `notin` ftvar_in_pskl P /\
      exists βs τ, e_guess_mono S0 P S1 βs τ /\ mono_ptyp τ /\
        Θ1 = (α ~ abind_flex_mono_def τ) ++ βs ++ Ξ ++ Θ0).
Proof.
  intros * Hd. inversion Hd; subst; try congruence.
  - left; split; [ reflexivity
                 | split; [ reflexivity | split; reflexivity ] ].
  - right; split; [ assumption | eauto 10 ].
Qed.

Lemma e_assign_inv_flex_other : forall S0 Θ0 Ξ α β P S1 Θ1,
  α <> β ->
  {{ S0 ↝ S1 ⊨ ((β ~ abind_flex_mono) ++ Θ0) ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
  (β `in` ftvar_in_pskl P /\
     {{ S0 ↝ S1 ⊨ Θ0 ⊲[ (Ξ ++ (β ~ abind_flex_mono)) ] α ≔ P ⊣ Θ1 }}e)
  \/ (β `notin` ftvar_in_pskl P /\ exists Θ1',
        Θ1 = (β ~ abind_flex_mono) ++ Θ1' /\
        {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1' }}e).
Proof.
  intros * Hne Hd. inversion Hd; subst; try congruence.
  - left; split; assumption.
  - right; split; [ assumption | eauto ].
Qed.

Lemma e_assign_inv_def : forall S0 Θ0 Ξ α β τ P S1 Θ1,
  {{ S0 ↝ S1 ⊨ ((β ~ abind_flex_mono_def τ) ++ Θ0) ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
  a_flex_tvar ((β ~ abind_flex_mono_def τ) ++ Θ0) α /\
  exists Θ1' Q, Θ1 = (β ~ abind_flex_mono_def τ) ++ Θ1' /\
    {{ S0 ↝ S1 ⊨ (Ξ ++ Θ0) ⊢[ empty | empty
         | (subst_pskl_in_pskl (ptyp_to_pskl τ) β P) ]
       (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)) ∼ Q
       ⊣ Θ1' }}e.
Proof. intros * Hd. inversion Hd; subst. split; [ assumption | eauto ]. Qed.

Lemma e_assign_inv_tvar : forall S0 Θ0 Ξ α β P S1 Θ1,
  {{ S0 ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ0) ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
  β `notin` ftvar_in_pskl P /\ exists Θ1',
    Θ1 = (β ~ abind_tvar) ++ Θ1' /\
    {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1' }}e.
Proof. intros * Hd. inversion Hd; subst. split; [ assumption | eauto ]. Qed.

Lemma e_assign_inv_var_typ : forall S0 Θ0 Ξ α x A P S1 Θ1,
  {{ S0 ↝ S1 ⊨ ((x ~ abind_var_typ A) ++ Θ0) ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
  exists Θ1', Θ1 = (x ~ abind_var_typ A) ++ Θ1' /\
    {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1' }}e.
Proof. intros * Hd. inversion Hd; subst. eauto. Qed.

Lemma e_assign_inv_var_skl : forall S0 Θ0 Ξ α x Q P S1 Θ1,
  {{ S0 ↝ S1 ⊨ ((x ~ abind_var_skl Q) ++ Θ0) ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
  exists Θ1', Θ1 = (x ~ abind_var_skl Q) ++ Θ1' /\
    {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1' }}e.
Proof. intros * Hd. inversion Hd; subst. eauto. Qed.

(** The unify walk.  All five are stated at [α <> β]: at [α = β] the
    runner commits to [Flex-Flex-Id] whatever the head is, and what
    answers that arm is §5's reflexivity, not an inversion. *)
Lemma e_unify_inv_nil : forall S0 α β S1 Θ1,
  {{ S0 ↝ S1 ⊨ nil ⊲ α ≈ᵘ β ⊣ Θ1 }}e -> False.
Proof.
  intros * Hd. inversion Hd; subst.
  destruct H as [Hb | [τ Hb]]; inversion Hb.
Qed.

Lemma e_unify_inv_flex_l : forall S0 Θ0 α β S1 Θ1,
  α <> β ->
  {{ S0 ↝ S1 ⊨ ((α ~ abind_flex_mono) ++ Θ0) ⊲ α ≈ᵘ β ⊣ Θ1 }}e ->
  a_flex_tvar Θ0 β /\ S1 = S0 /\
  Θ1 = (α ~ abind_flex_mono_def (ptyp_var_f β)) ++ Θ0.
Proof.
  intros * Hne Hd. inversion Hd; subst; try congruence; try kill_skip_other.
  split; [ assumption | split; reflexivity ].
Qed.

Lemma e_unify_inv_flex_r : forall S0 Θ0 α β S1 Θ1,
  α <> β ->
  {{ S0 ↝ S1 ⊨ ((β ~ abind_flex_mono) ++ Θ0) ⊲ α ≈ᵘ β ⊣ Θ1 }}e ->
  a_flex_tvar Θ0 α /\ S1 = S0 /\
  Θ1 = (β ~ abind_flex_mono_def (ptyp_var_f α)) ++ Θ0.
Proof.
  intros * Hne Hd. inversion Hd; subst; try congruence; try kill_skip_other.
  split; [ assumption | split; reflexivity ].
Qed.

Lemma e_unify_inv_flex_skip : forall S0 Θ0 γ α β S1 Θ1,
  α <> β -> γ <> α -> γ <> β ->
  {{ S0 ↝ S1 ⊨ ((γ ~ abind_flex_mono) ++ Θ0) ⊲ α ≈ᵘ β ⊣ Θ1 }}e ->
  exists Θ1', Θ1 = (γ ~ abind_flex_mono) ++ Θ1' /\
    {{ S0 ↝ S1 ⊨ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1' }}e.
Proof.
  intros * Hne H1 H2 Hd.
  inversion Hd; subst; try congruence; try kill_skip_other. eauto.
Qed.

Lemma e_unify_inv_def : forall S0 Θ0 γ τ α β S1 Θ1,
  α <> β ->
  {{ S0 ↝ S1 ⊨ ((γ ~ abind_flex_mono_def τ) ++ Θ0) ⊲ α ≈ᵘ β ⊣ Θ1 }}e ->
  a_flex_tvar ((γ ~ abind_flex_mono_def τ) ++ Θ0) α /\
  a_flex_tvar ((γ ~ abind_flex_mono_def τ) ++ Θ0) β /\
  exists Θ1' Q, Θ1 = (γ ~ abind_flex_mono_def τ) ++ Θ1' /\
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ empty | empty
         | (ptyp_to_pskl (subst_ptyp_in_ptyp τ γ (ptyp_var_f β))) ]
       (ptyp_to_pskl (subst_ptyp_in_ptyp τ γ (ptyp_var_f α))) ∼ Q
       ⊣ Θ1' }}e.
Proof.
  intros * Hne Hd.
  inversion Hd; subst; try congruence; try kill_skip_other.
  split; [ assumption | split; [ assumption | eauto ] ].
Qed.

Lemma e_unify_inv_other : forall S0 Θ0 c b α β S1 Θ1,
  α <> β ->
  (b = abind_tvar \/ (exists A, b = abind_var_typ A) \/
   (exists Q, b = abind_var_skl Q)) ->
  {{ S0 ↝ S1 ⊨ ((c ~ b) ++ Θ0) ⊲ α ≈ᵘ β ⊣ Θ1 }}e ->
  exists Θ1', Θ1 = (c ~ b) ++ Θ1' /\
    {{ S0 ↝ S1 ⊨ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1' }}e.
Proof.
  intros * Hne Hb Hd.
  destruct Hb as [-> | [[A ->] | [Q ->]]];
    inversion Hd; subst; try congruence; eauto.
Qed.

(* ===================================================================== *)
(*  §5  ⭐ [α̂ ≈ᵘ α̂] MOVES NOTHING — under the runner's own discipline     *)
(*                                                                        *)
(*  [Flex-Flex-Id] carries no [α <> β], so at [α̂ ≈ᵘ α̂] it OVERLAPS both   *)
(*  [Flex-Flex-Skip] (at an undefined non-matching head) and              *)
(*  [Flex-Flex-Assign] (at a DEFINED one) — and the runner commits to     *)
(*  [Flex-Flex-Id], returning the supply AND the context untouched        *)
(*  (def_consis_impl.v:619).  So the level needs that overlap to be       *)
(*  BENIGN in both components, which is what this says.                    *)
(*                                                                        *)
(*  ⭐ WHY IT IS TRUE, AND WHY [aenv_defs_mono] IS LOAD-BEARING.           *)
(*  [Flex-Flex-Assign]'s premise is a consistency of a DEFINITION PAYLOAD *)
(*  with itself.  A payload is a [ptyp], so no ◇ and no ⫯ can appear —    *)
(*  which already gives the context.  For the SUPPLY one needs more: a ∀  *)
(*  payload's [ForallInh] draws an opener and the supply grows.  The      *)
(*  context discipline the runner already demands rules that out — a      *)
(*  defined flexible's payload is a MONOTYPE, and a monotype's skeleton   *)
(*  view has no ∀ either, so only Unit / Rigid / Arrow / Flex can fire.   *)
(*                                                                        *)
(*  The motives travel together: the consis motive's [FlexL]/[FlexR] rows *)
(*  are refuted by §8's [e_assign_target_flex], which says the assign     *)
(*  walk can only have reached [α] through a flex-bound head — so the     *)
(*  ASSIGN motive here is [True].                                          *)
(* ===================================================================== *)

Lemma e_unify_consis_refl_mono :
  (forall S0 Θ0 Ξ α P S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e -> True) /\
  (forall S0 Θ0 α β S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}e ->
     α = β -> aenv_defs_mono Θ0 -> S1 = S0 /\ Θ1 = Θ0) /\
  (forall Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}e ->
     P0 = P -> (exists A, P = ptyp_to_pskl A /\ mono_ptyp A) ->
     aenv_defs_mono Θ0 -> S1 = S0 /\ Θ1 = Θ0).
Proof.
  apply (e_assign_unify_consis_mutind
           (fun S0 Θ0 Ξ α P S1 Θ1 _ => True)
           (fun S0 Θ0 α β S1 Θ1 _ =>
              α = β -> aenv_defs_mono Θ0 -> S1 = S0 /\ Θ1 = Θ0)
           (fun Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1 _ =>
              P0 = P -> (exists A, P = ptyp_to_pskl A /\ mono_ptyp A) ->
              aenv_defs_mono Θ0 -> S1 = S0 /\ Θ1 = Θ0)).
  (* ---- assign: superseded by §8's [e_assign_target_flex] ---- *)
  1-8: intros; exact I.
  (* ---- unify ---- *)
  - (* Flex-Flex-Id *) intros S Θ0 α Hf Heq HD. split; reflexivity.
  - (* Flex-Flex-L: needs α <> β *)
    intros S Θ0 α β Hne Hf Heq HD. contradiction.
  - (* Flex-Flex-R *)
    intros S Θ0 α β Hne Hf Heq HD. contradiction.
  - (* Flex-Flex-Assign — a SELF-consistency of a MONOTYPE payload *)
    intros S0 S1 Θ0 Θ1 α1 τ α β Q Hfa Hfb Hd IH Heq HD. subst.
    destruct (aenv_defs_mono_cons_inv HD) as [Hmτ HD0].
    destruct IH as [-> ->];
      [ reflexivity
      | eexists; split;
        [ reflexivity
        | apply mono_ptyp_subst; [ apply mono_ptyp__var | exact Hmτ ] ]
      | exact HD0
      | ].
    split; reflexivity.
  - (* Flex-Flex-Skip *)
    intros S0 S1 Θ0 Θ1 α1 α β Hne1 Hne2 Hd IH Heq HD. subst.
    destruct (aenv_defs_mono_cons_inv HD) as [_ HD0].
    destruct IH as [-> ->]; [ reflexivity | exact HD0 | ].
    split; reflexivity.
  - (* Flex-Flex-Skip' *)
    intros S0 S1 Θ0 Θ1 c b α β Hb Hd IH Heq HD. subst.
    destruct (aenv_defs_mono_cons_inv HD) as [_ HD0].
    destruct IH as [-> ->]; [ reflexivity | exact HD0 | ].
    split; reflexivity.
  (* ---- consis ---- *)
  - (* Ghost *)
    intros Δ1 Δ2 S Θ0 P0 Hdis Heq Hsh HD. split; reflexivity.
  - (* Unit *) intros Δ1 Δ2 S Θ0 Heq Hsh HD. split; reflexivity.
  - (* Rigid *) intros Δ1 Δ2 S Θ0 α Hb Heq Hsh HD. split; reflexivity.
  - (* Arrow — both halves are self-consistencies of a monotype half *)
    intros Δ1 Δ2 S0 S1 S2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2
           Hd1 IH1 Hd2 IH2 Heq Hsh HD.
    destruct Hsh as [Ash [He Hmo]]; destruct Ash; simpl in He;
      try discriminate.
    inversion He; subst. inversion Heq; subst. inversion Hmo; subst.
    destruct IH1 as [-> ->];
      [ reflexivity
      | eexists; split; [ reflexivity | assumption ] | exact HD | ].
    destruct IH2 as [-> ->];
      [ reflexivity
      | eexists; split; [ reflexivity | assumption ] | exact HD | ].
    split; reflexivity.
  - (* ForallInh — a monotype has no ∀ *)
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q α Hα Hd IH Heq Hsh HD.
    destruct Hsh as [Ash [He Hmo]]; destruct Ash; simpl in He;
      try discriminate; inversion Hmo.
  - (* ForallSyn — [⫯P0] against [∀P] *)
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q α Hα Hd IH Heq Hsh HD. discriminate.
  - (* UnivGhost — a ⫯ is no monotype view *)
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q Hd IH Heq Hsh HD.
    exfalso. destruct Hsh as [Ash [He Hmo]]; destruct Ash; discriminate.
  - (* UnivGhost1 *)
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q α Hα Hd IH Heq Hsh HD. discriminate.
  - (* UnivGhost2 — the subject is a ⫯ *)
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q Hg Hnf Hd IH Heq Hsh HD.
    exfalso. destruct Hsh as [Ash [He Hmo]]; destruct Ash; discriminate.
  - (* Flex — pattern and subject are the SAME variable *)
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 α β Hd IH Heq Hsh HD.
    inversion Heq; subst.
    destruct IH as [-> ->]; [ reflexivity | exact HD | ].
    split; reflexivity.
  - (* FlexL — [nonflex] against the assign walk's own finding *)
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 α P0 Hnf Hd IH Heq Hsh HD.
    exfalso. subst. destruct Hnf as [_ Hf]. apply Hf.
    apply a_flex_tvar_flex. eapply e_assign_target_flex; eassumption.
  - (* FlexR — the mirror *)
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 α P Hnf Hd IH Heq Hsh HD.
    exfalso. subst. destruct Hnf as [_ Hf]. apply Hf.
    apply a_flex_tvar_flex. eapply e_assign_target_flex; eassumption.
  - (* GhostR *)
    intros Δ1 Δ2 S Θ0 P Hdis Heq Hsh HD. split; reflexivity.
  - (* UnivGhostR *)
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q Hg Hnf Hd IH Heq Hsh HD.
    exfalso. subst.
    destruct Hsh as [Ash [He Hmo]]; destruct Ash; discriminate.
Qed.

(** What the runner's [Flex-Flex-Id] arm consumes. *)
Corollary e_unify_refl : forall S0 Θ0 α S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊲ α ≈ᵘ α ⊣ Θ1 }}e ->
  aenv_defs_mono Θ0 -> S1 = S0 /\ Θ1 = Θ0.
Proof.
  intros. eapply (proj1 (proj2 e_unify_consis_refl_mono));
    [ eassumption | reflexivity | assumption ].
Qed.
