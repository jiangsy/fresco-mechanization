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

Lemma e_consis_swaps : forall ps Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}e ->
  forall S0', S0' [=] swaps_atoms ps S0 ->
  exists S1', S1' [=] swaps_atoms ps S1 /\
    {{ S0' ↝ S1' ⊨ (swaps_aenv ps Θ0)
       ⊢[ (swaps_atoms ps Δ1) | (swaps_atoms ps Δ2) | (swaps_pskl ps P0) ]
       (swaps_pskl ps P) ∼ (swaps_pskl ps Q) ⊣ (swaps_aenv ps Θ1) }}e.
Proof.
  induction ps as [ | [a b] ps IH ]; intros * Hd S0' Heq; simpl in *.
  - exact (e_consis_supply_respect Hd Heq).
  - assert (H1 : swap_atoms a b Δ1 [=] swap_atoms a b Δ1) by reflexivity.
    assert (H2 : swap_atoms a b Δ2 [=] swap_atoms a b Δ2) by reflexivity.
    assert (Hr : swap_atoms a b S0 [=] swap_atoms a b S0) by reflexivity.
    destruct (e_consis_swap Hd H1 H2 Hr) as [S1a [HS1a Hda]].
    destruct (IH _ _ _ _ _ _ _ _ _ Hda _ Heq) as [S1' [HS1' Hd']].
    exists S1'. split; [ | exact Hd' ].
    rewrite HS1'. apply swaps_atoms_cong. exact HS1a.
Qed.
