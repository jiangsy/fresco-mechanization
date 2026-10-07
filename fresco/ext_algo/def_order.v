(** ext_algo — the Bove–Capretta DOMAIN PREDICATES ("orders") for the
    subtyping side of the algorithm: every judgement [e_sub] reaches, from
    [guess^N] up to [e_sub]/[e_sub_flex] themselves.

    Phase 2 of the termination campaign
    (docs/HANDOFF-extractable-algo-encoding.md §8b).  Each predicate is the
    CALL GRAPH of the eventual runner, in Prop: it says which recursive calls
    the function makes and nothing about what they return, so a runner can
    recurse structurally on it ([Equations … by struct H], §7.1) and
    TERMINATION becomes the separate theorem that the predicate is inhabited
    (prop_termination.v).

    ⭐ ONE CONSTRUCTOR PER JUDGEMENT, WITH SHAPE-CONDITIONAL PREMISES — a
    deliberate departure from [e_guess_mono_order]'s one-constructor-per-rule
    shape (def_guess_impl.v §2), for three reasons that only appear at this
    scale:

    - TOTALITY NEEDS NO FAILURE ENUMERATION.  These judgements are PARTIAL —
      most input shapes fire no rule, and the runner must be callable there
      to REJECT.  Per-rule constructors would owe a constructor per failing
      shape (a combinatorial family per judgement); here a failing input
      satisfies the one constructor with every premise VACUOUS, because each
      premise is guarded by equations on the input shapes.

    - INVERSION IS UNAMBIGUOUS.  A runner branch inverts [H] once and gets
      EVERY premise, then selects with the branch's own equations.  With
      per-rule constructors, overlapping shapes (absent/vacuous against every
      structural row here) would multiply inversion cases inside every
      obligation.

    - THE GUARD CONDITION STILL HOLDS.  A conditional premise applied to
      [eq_refl]s and to the sibling call's relation evidence is still a
      structural subterm of [H] — the [Acc_inv] pattern, already exercised by
      [ego_arrow]'s higher-order premise.

    ⚙ RULE GUARDS ARE DROPPED, SHAPES ARE KEPT.  A premise is conditioned on
    what determines the RECURSION (the input shapes, the mode's shape), not
    on the rule's side conditions ([β ∉ ftv P], [guarded_pskl Q], …): the
    runner tests those before recursing, and an order that also holds where a
    guard fails is merely stronger.  The ONE exception is [e_sub_order]'s
    ForallL premise, which keeps the rule's wf check on the extracted
    instantiation — the recursion is at [open P P1], so the premise must know
    the check passed, exactly as the reference implementation recurses only
    behind [is_wf p1] (type.ml:966).

    ⭐ THE FRESH CHOICES ARE COMMITTED.  Where a rule draws a name from the
    supply, the order names [supply_fresh S0] — the deterministic choice THE
    IMPLEMENTATION makes ([ego_forall]'s rationale, def_guess_impl.v: the
    relation keeps the freedom, the implementation does not).

    ⚠️ NO [Set Implicit Arguments], as in def_guess_impl.v: these predicates
    exist to be arguments of [Equations] runners, where implicit maximality
    misfires on recursive calls with an error naming neither side. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.def_supply.
Require Import src.fresco.ext_algo.def_guess.
Require Import src.fresco.ext_algo.def_guess_impl.
Require Import src.fresco.ext_algo.def_consis.
Require Import src.fresco.ext_algo.def_look.
Require Import src.fresco.ext_algo.def_solve.
Require Import src.fresco.ext_algo.def_extract.
Require Import src.fresco.ext_algo.def_sub.

Open Scope fresco_e_scope.

(* ===================================================================== *)
(*  §1  [guess^N] — the sort wrapper over [e_guess_mono_order]            *)
(* ===================================================================== *)

Inductive e_guess_order : supply -> a_sub_mode -> pskl -> Prop :=
| e_guess_order__intro : forall S0 NM Q,
    (NM = a_sub_mode_ty -> e_guess_mono_order S0 Q) ->
    e_guess_order S0 NM Q.

(* ===================================================================== *)
(*  §2  The collection cluster                                            *)
(*                                                                        *)
(*  [e_lookeq] never calls [e_looksub], so the two orders LAYER instead   *)
(*  of going mutual — which is also how their totality wants to be        *)
(*  proved (lookeq first, looksub on top of it).                          *)
(* ===================================================================== *)

Inductive e_lookeq_order : supply -> aenv -> atom -> pskl -> pskl -> Prop :=
| e_lookeq_order__intro : forall S0 Θ α P P',
    (* LE-Arrow — the sibling threads the supply *)
    (forall P1 P2 P1' P2',
       P = pskl_arrow P1 P2 -> P' = pskl_arrow P1' P2' ->
       e_lookeq_order S0 Θ α P1 P1'
       /\ (forall S1 Ξ1 C1,
             {{ S0 ↝ S1 ⊨ Θ ⊢ P1 ∼[ α ] P1' ⤳ Ξ1 ⨾ C1 }}e ->
             e_lookeq_order S1 Θ α P2 P2')) ->
    (* LE-ForallInh *)
    (forall Q Q',
       P = pskl_all_syn Q -> P' = pskl_all_syn Q' ->
       e_lookeq_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ) α
         (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0)))
         (open_pskl_wrt_pskl Q' (pskl_var_f (supply_fresh S0)))) ->
    (* LE-ForallSyn *)
    (forall Q Q',
       P = pskl_all_syn Q -> P' = pskl_tophole Q' ->
       e_lookeq_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ) α
         (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0)))
         (pskl_tophole Q')) ->
    (* LE-UnivGhost *)
    (forall Q Q',
       P = pskl_tophole Q -> P' = pskl_tophole Q' ->
       e_lookeq_order S0 Θ α Q Q') ->
    (* LE-UnivGhost1 *)
    (forall Q Q',
       P = pskl_tophole Q -> P' = pskl_all_syn Q' ->
       e_lookeq_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ) α
         (pskl_tophole Q)
         (open_pskl_wrt_pskl Q' (pskl_var_f (supply_fresh S0)))) ->
    (* LE-UnivGhost2 — strip the subject's ⫯ *)
    (forall Q,
       P = pskl_tophole Q ->
       e_lookeq_order S0 Θ α Q P') ->
    (* LE-UnivGhostR — strip the counterpart's ⫯ *)
    (forall Q',
       P' = pskl_tophole Q' ->
       e_lookeq_order S0 Θ α P Q') ->
    e_lookeq_order S0 Θ α P P'.

Inductive e_looksub_order : supply -> aenv -> atom -> mode -> pskl -> pskl
                            -> Prop :=
| e_looksub_order__intro : forall S0 Θ α m P P',
    (* LS-Check — the drop into the eq layer, at check mode *)
    (m = mode_tc -> e_lookeq_order S0 Θ α P P') ->
    (* LS-ForallR *)
    (forall B,
       m = mode_tc -> P' = pskl_all_syn B ->
       e_looksub_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ) α mode_tc P
         (open_pskl_wrt_pskl B (pskl_var_f (supply_fresh S0)))) ->
    (* LS-Arrow *)
    (forall m' P1 P2 P1' P2',
       m = mode_fn m' -> P = pskl_arrow P1 P2 -> P' = pskl_arrow P1' P2' ->
       e_lookeq_order S0 Θ α P1 P1'
       /\ (forall S1 Ξ1 C1,
             {{ S0 ↝ S1 ⊨ Θ ⊢ P1 ∼[ α ] P1' ⤳ Ξ1 ⨾ C1 }}e ->
             e_looksub_order S1 Θ α m' P2 P2')) ->
    (* LS-ForallL *)
    (forall Q,
       P = pskl_all_syn Q ->
       e_looksub_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ) α m
         (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0))) P') ->
    (* LS-UnivGhostL *)
    (forall Q,
       P = pskl_tophole Q ->
       e_looksub_order S0 Θ α m Q P') ->
    e_looksub_order S0 Θ α m P P'.

(* ===================================================================== *)
(*  §3  The solving layer — same layering ([e_solve_eq] never calls       *)
(*  [e_solve_sub])                                                        *)
(* ===================================================================== *)

Inductive e_solve_eq_order : supply -> aenv -> pskl -> pskl -> Prop :=
| e_solve_eq_order__intro : forall S0 Θ P Q,
    (* SE-FlexR — the yield is a guess on the accumulated pattern *)
    (forall β,
       Q = pskl_var_f β ->
       e_guess_mono_order S0 P) ->
    (* SE-Arrow — the sibling ALSO threads the context (def_solve.v header) *)
    (forall P1 P2 Q1 Q2,
       P = pskl_arrow P1 P2 -> Q = pskl_arrow Q1 Q2 ->
       e_solve_eq_order S0 Θ P1 Q1
       /\ (forall S1 Ξ1 P1',
             {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P1 ∼ Q1 ⤳ Ξ1 ⨾ P1' }}e ->
             e_solve_eq_order S1 (Ξ1 ++ Θ) P2 Q2)) ->
    (* SE-Forall *)
    (forall P1 Q1,
       P = pskl_all_syn P1 -> Q = pskl_all_syn Q1 ->
       e_solve_eq_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ)
         (open_pskl_wrt_pskl P1 (pskl_var_f (supply_fresh S0)))
         (open_pskl_wrt_pskl Q1 (pskl_var_f (supply_fresh S0)))) ->
    (* SE-UnivGhost *)
    (forall P1 Q1,
       P = pskl_tophole P1 -> Q = pskl_tophole Q1 ->
       e_solve_eq_order S0 Θ P1 Q1) ->
    (* SE-GhostForall *)
    (forall P1 Q1,
       P = pskl_tophole P1 -> Q = pskl_all_syn Q1 ->
       e_solve_eq_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ)
         (pskl_tophole P1)
         (open_pskl_wrt_pskl Q1 (pskl_var_f (supply_fresh S0)))) ->
    (* SE-GhostGuarded — strip the subject's ⫯ *)
    (forall P1,
       P = pskl_tophole P1 ->
       e_solve_eq_order S0 Θ P1 Q) ->
    (* SE-ForallGhost *)
    (forall P1 Q1,
       P = pskl_all_syn P1 -> Q = pskl_tophole Q1 ->
       e_solve_eq_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ)
         (open_pskl_wrt_pskl P1 (pskl_var_f (supply_fresh S0)))
         (pskl_tophole Q1)) ->
    (* SE-GuardedGhost — strip the constraint's ⫯ *)
    (forall Q1,
       Q = pskl_tophole Q1 ->
       e_solve_eq_order S0 Θ P Q1) ->
    e_solve_eq_order S0 Θ P Q.

Inductive e_solve_sub_order : supply -> aenv -> mode -> pskl -> pskl -> Prop :=
| e_solve_sub_order__intro : forall S0 Θ m P Q,
    (* SS-ForallL *)
    (forall P1,
       P = pskl_all_syn P1 ->
       e_solve_sub_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ) m
         (open_pskl_wrt_pskl P1 (pskl_var_f (supply_fresh S0))) Q) ->
    (* SS-UnivGhostL *)
    (forall P1,
       P = pskl_tophole P1 ->
       e_solve_sub_order S0 Θ m P1 Q) ->
    (* SS-Check — the drop into the eq layer *)
    (m = mode_tc -> e_solve_eq_order S0 Θ P Q) ->
    (* SS-ForallR *)
    (forall B,
       m = mode_tc -> Q = pskl_all_syn B ->
       e_solve_sub_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ) mode_tc P
         (open_pskl_wrt_pskl B (pskl_var_f (supply_fresh S0)))) ->
    (* SS-Arrow *)
    (forall m' P1 P2 Q1 Q2,
       m = mode_fn m' -> P = pskl_arrow P1 P2 -> Q = pskl_arrow Q1 Q2 ->
       e_solve_eq_order S0 Θ P1 Q1
       /\ (forall S1 Ξ1 P1',
             {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P1 ∼ Q1 ⤳ Ξ1 ⨾ P1' }}e ->
             e_solve_sub_order S1 (Ξ1 ++ Θ) m' P2 Q2)) ->
    (* SS-GhostLF — the ◇ expands along the counterpart's arrow *)
    (forall m' Q1 Q2,
       m = mode_fn m' -> P = pskl_hole -> Q = pskl_arrow Q1 Q2 ->
       e_solve_eq_order S0 Θ pskl_hole Q1
       /\ (forall S1 Ξ1 P1',
             {{ S0 ↝ S1 ⊨ Θ ⊢ₑ pskl_hole ∼ Q1 ⤳ Ξ1 ⨾ P1' }}e ->
             e_solve_sub_order S1 (Ξ1 ++ Θ) m' pskl_hole Q2)) ->
    e_solve_sub_order S0 Θ m P Q.

(** The constraint fold — structural on the list, with the context and the
    accumulated pattern threaded through the relation. *)
Inductive e_solve_cstr_order : supply -> aenv -> a_cstrs -> pskl -> Prop :=
| e_solve_cstr_order__intro : forall S0 Θ C P,
    (forall m Q,
       C = a_cstr_sub m Q :: nil ->
       e_solve_sub_order S0 Θ m P Q) ->
    (forall Q C',
       C = a_cstr_eq Q :: C' ->
       e_solve_eq_order S0 Θ P Q
       /\ (forall S1 Ξ1 P'',
             {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ1 ⨾ P'' }}e ->
             e_solve_cstr_order S1 (Ξ1 ++ Θ) C' P'')) ->
    e_solve_cstr_order S0 Θ C P.

(* ===================================================================== *)
(*  §4  The extraction — collection, then the ◇-seeded fold, then guess   *)
(* ===================================================================== *)

Inductive e_extract_order : supply -> aenv -> a_sub_mode -> atom -> mode
                            -> pskl -> pskl -> Prop :=
| e_extract_order__intro : forall S0 Θ0 NM α m P P',
    e_looksub_order S0 Θ0 α m P P' ->
    (forall S1 Ξ C,
       {{ S0 ↝ S1 ⊨ Θ0 ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
       e_solve_cstr_order S1 (Ξ ++ Θ0) C pskl_hole) ->
    (forall S1 Ξ C S2 Ξs Q,
       {{ S0 ↝ S1 ⊨ Θ0 ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
       {{ S1 ↝ S2 ⊨ (Ξ ++ Θ0) ⊩ C ⨾ pskl_hole ⤳ Ξs ⨾ Q }}e ->
       e_guess_order S2 NM Q) ->
    e_extract_order S0 Θ0 NM α m P P'.

(* ===================================================================== *)
(*  §5  The consistency block — MUTUAL, as the judgements are             *)
(*                                                                        *)
(*  ⚠️ These three orders are DEFINED here but their totality is NOT      *)
(*  phase 2's: [e_assign__solve_m] trades an undefined flexible for a     *)
(*  fresh guess block and [e_assign__assign]/[e_unify__flex_assign]       *)
(*  substitute a defined entry away and re-enter [e_consis] at a GROWN    *)
(*  pattern — unification-style termination, its own campaign (handoff    *)
(*  §8b.4).  [e_sub]'s totality takes their totality as an explicit       *)
(*  hypothesis until it lands.                                            *)
(* ===================================================================== *)

Inductive e_assign_order : supply -> aenv -> aenv -> atom -> pskl -> Prop :=
| e_assign_order__intro : forall S0 Θ Ξ α P,
    (* Assign-SolveM — the head is the target itself, undefined *)
    (forall Θ0,
       Θ = (α ~ abind_flex_mono) ++ Θ0 ->
       e_guess_mono_order S0 P) ->
    (* Assign-Assign — a DEFINED head is substituted away and dropped *)
    (forall β τ Θ0,
       Θ = (β ~ abind_flex_mono_def τ) ++ Θ0 ->
       e_consis_order empty empty S0 (Ξ ++ Θ0)
         (subst_pskl_in_pskl (ptyp_to_pskl τ) β P)
         (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α))) ->
    (* Assign-Depend / Assign-Skip — an undefined non-target head *)
    (forall β Θ0,
       Θ = (β ~ abind_flex_mono) ++ Θ0 ->
       e_assign_order S0 Θ0 (Ξ ++ (β ~ abind_flex_mono)) α P
       /\ e_assign_order S0 Θ0 Ξ α P) ->
    (* Assign-SkipRigid *)
    (forall β Θ0,
       Θ = (β ~ abind_tvar) ++ Θ0 ->
       e_assign_order S0 Θ0 Ξ α P) ->
    (* Assign-SkipTmVar, both payload sorts *)
    (forall x A Θ0,
       Θ = (x ~ abind_var_typ A) ++ Θ0 ->
       e_assign_order S0 Θ0 Ξ α P) ->
    (forall x Q Θ0,
       Θ = (x ~ abind_var_skl Q) ++ Θ0 ->
       e_assign_order S0 Θ0 Ξ α P) ->
    e_assign_order S0 Θ Ξ α P

with e_unify_order : supply -> aenv -> atom -> atom -> Prop :=
| e_unify_order__intro : forall S0 Θ α β,
    (* Flex-Flex-Assign — a defined head is substituted into both sides *)
    (forall α1 τ Θ0,
       Θ = (α1 ~ abind_flex_mono_def τ) ++ Θ0 ->
       e_consis_order empty empty S0 Θ0
         (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f β)))
         (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f α)))) ->
    (* Flex-Flex-Skip *)
    (forall α1 Θ0,
       Θ = (α1 ~ abind_flex_mono) ++ Θ0 ->
       e_unify_order S0 Θ0 α β) ->
    (* Flex-Flex-Skip' — the three other binding sorts *)
    (forall c Θ0,
       Θ = (c ~ abind_tvar) ++ Θ0 ->
       e_unify_order S0 Θ0 α β) ->
    (forall x A Θ0,
       Θ = (x ~ abind_var_typ A) ++ Θ0 ->
       e_unify_order S0 Θ0 α β) ->
    (forall x Q Θ0,
       Θ = (x ~ abind_var_skl Q) ++ Θ0 ->
       e_unify_order S0 Θ0 α β) ->
    e_unify_order S0 Θ α β

with e_consis_order : atoms -> atoms -> supply -> aenv -> pskl -> pskl
                      -> Prop :=
| e_consis_order__intro : forall Δ1 Δ2 S0 Θ P0 P,
    (* Arrow — the sibling runs at the FIRST premise's output context *)
    (forall P0a P0b P1 P2,
       P0 = pskl_arrow P0a P0b -> P = pskl_arrow P1 P2 ->
       e_consis_order Δ1 Δ2 S0 Θ P0a P1
       /\ (forall S1 Θ1 Q1,
             {{ S0 ↝ S1 ⊨ Θ ⊢[ Δ1 | Δ2 | P0a ] P1 ∼ Q1 ⊣ Θ1 }}e ->
             e_consis_order Δ1 Δ2 S1 Θ1 P0b P2)) ->
    (* ForallInh *)
    (forall P0' P1,
       P0 = pskl_all_syn P0' -> P = pskl_all_syn P1 ->
       e_consis_order (add (supply_fresh S0) Δ1) (add (supply_fresh S0) Δ2)
         (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ)
         (open_pskl_wrt_pskl P0' (pskl_var_f (supply_fresh S0)))
         (open_pskl_wrt_pskl P1 (pskl_var_f (supply_fresh S0)))) ->
    (* ForallSyn *)
    (forall P0' P1,
       P0 = pskl_tophole P0' -> P = pskl_all_syn P1 ->
       e_consis_order Δ1 (add (supply_fresh S0) Δ2)
         (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ)
         (pskl_tophole P0')
         (open_pskl_wrt_pskl P1 (pskl_var_f (supply_fresh S0)))) ->
    (* UnivGhost *)
    (forall P0' P1,
       P0 = pskl_tophole P0' -> P = pskl_tophole P1 ->
       e_consis_order Δ1 Δ2 S0 Θ P0' P1) ->
    (* UnivGhost1 *)
    (forall P0' P1,
       P0 = pskl_all_syn P0' -> P = pskl_tophole P1 ->
       e_consis_order (add (supply_fresh S0) Δ1) Δ2
         (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ)
         (open_pskl_wrt_pskl P0' (pskl_var_f (supply_fresh S0)))
         (pskl_tophole P1)) ->
    (* UnivGhost2 — strip the subject's ⫯ against a guarded pattern *)
    (forall P1,
       P = pskl_tophole P1 ->
       e_consis_order Δ1 Δ2 S0 Θ P0 P1) ->
    (* UnivGhostR — strip the pattern's ⫯ *)
    (forall P0',
       P0 = pskl_tophole P0' ->
       e_consis_order Δ1 Δ2 S0 Θ P0' P) ->
    (* Flex — both sides the same flexible, pattern a variable *)
    (forall α β,
       P = pskl_var_f α -> P0 = pskl_var_f β ->
       e_unify_order S0 Θ α β) ->
    (* FlexL — the subject variable is assigned the pattern *)
    (forall α,
       P = pskl_var_f α ->
       e_assign_order S0 Θ nil α P0) ->
    (* FlexR — the pattern variable is assigned the subject *)
    (forall α,
       P0 = pskl_var_f α ->
       e_assign_order S0 Θ nil α P) ->
    e_consis_order Δ1 Δ2 S0 Θ P0 P.

Scheme e_assign_order_mind := Induction for e_assign_order Sort Prop
  with e_unify_order_mind  := Induction for e_unify_order  Sort Prop
  with e_consis_order_mind := Induction for e_consis_order Sort Prop.
Combined Scheme e_assign_unify_consis_order_mutind
  from e_assign_order_mind, e_unify_order_mind, e_consis_order_mind.

(* ===================================================================== *)
(*  §6  Subtyping and its flexible walk — MUTUAL                          *)
(* ===================================================================== *)

Inductive e_sub_order : supply -> a_sub_mode -> mode -> pskl -> aenv -> pskl
                        -> Prop :=
| e_sub_order__intro : forall S0 NM M P0 Θ0 P,
    (* Check — one consistency run, pattern against subject *)
    (M = mode_tc -> e_consis_order empty empty S0 Θ0 P0 P) ->
    (* ForallR — peel the pattern's quantifier *)
    (forall B,
       M = mode_tc -> P0 = pskl_all_syn B ->
       e_sub_order (add (supply_fresh S0) S0) a_sub_mode_ty mode_tc
         (open_pskl_wrt_pskl B (pskl_var_f (supply_fresh S0)))
         ((supply_fresh S0 ~ abind_tvar) ++ Θ0) P) ->
    (* FlexMono — enter the walk *)
    (forall α M',
       P = pskl_var_f α -> M = mode_fn M' ->
       e_sub_flex_order S0 NM M' P0 Θ0 nil α) ->
    (* Arrow — the domain goes to consistency, the codomain stays *)
    (forall M' P0a P0b P1 P2,
       M = mode_fn M' -> P0 = pskl_arrow P0a P0b -> P = pskl_arrow P1 P2 ->
       e_consis_order empty empty S0 Θ0 P0a P1
       /\ (forall S1 Θ1 Q1,
             {{ S0 ↝ S1 ⊨ Θ0 ⊢[ empty | empty | P0a ] P1 ∼ Q1 ⊣ Θ1 }}e ->
             e_sub_order S1 NM M' P0b Θ1 P2)) ->
    (* ForallL — extract an instantiation, then recurse on the opened body.
       ⚙ The ONE row that keeps its rule GUARDS: the guarded-or-◇ premise on
       [P0] is what §9's decrease theorem consumes (the graft carries no head
       ∀ only against such a [P0]), and the recursion happens only behind the
       rule's wf check on [P1] (type.ml:966's [is_wf p1]).
       ⚙ Δ (phase 4): the extraction runs at [add (supply_fresh S0) S0] — the
       supply AFTER the binder is drawn — exactly as [e_sub__forall_l]'s
       premise states it.  As first written both slots said [S0]; totality
       never noticed (every extraction lemma is supply-parametric), the
       RUNNER did (its extract call must satisfy this premise AND the rule). *)
    (forall Q,
       P = pskl_all_syn Q -> M <> mode_ti ->
       (guarded_pskl P0 \/ P0 = pskl_hole) ->
       e_extract_order (add (supply_fresh S0) S0) Θ0 NM (supply_fresh S0) M
         (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0))) P0
       /\ (forall S1 Ξ P1,
             {{ (add (supply_fresh S0) S0) ↝ S1 ⊨ Θ0
                ⊢ (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0)))
                ⊳[ NM , (supply_fresh S0) , M ] P0 ⤳ Ξ ↪ P1 }}e ->
             {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P1 }}a ->
             e_sub_order S1 NM M P0 (Ξ ++ Θ0) (open_pskl_wrt_pskl Q P1))) ->
    (* UnivGhostL — strip the subject's ⫯ *)
    (forall Q,
       P = pskl_tophole Q -> M <> mode_ti ->
       e_sub_order S0 NM M P0 Θ0 Q) ->
    e_sub_order S0 NM M P0 Θ0 P

with e_sub_flex_order : supply -> a_sub_mode -> mode -> pskl -> aenv -> aenv
                        -> atom -> Prop :=
| e_sub_flex_order__intro : forall S0 NM M P0 Θ0 Ξ α,
    (* Flex-Solve — the head IS the target, undefined: it is defined at a
       fresh arrow and the walk re-enters the subtyping judgement.  Two names
       are drawn in sequence. *)
    (forall Θ0',
       Θ0 = (α ~ abind_flex_mono) ++ Θ0' ->
       e_sub_order
         (add (supply_fresh (add (supply_fresh S0) S0))
            (add (supply_fresh S0) S0))
         NM (mode_fn M) P0
         (Ξ ++ (α ~ abind_flex_mono_def
                      (ptyp_arrow (ptyp_var_f (supply_fresh S0))
                         (ptyp_var_f (supply_fresh (add (supply_fresh S0) S0)))))
             ++ (supply_fresh (add (supply_fresh S0) S0) ~ abind_flex_mono)
             ++ (supply_fresh S0 ~ abind_flex_mono) ++ Θ0')
         (pskl_arrow (pskl_var_f (supply_fresh S0))
            (pskl_var_f (supply_fresh (add (supply_fresh S0) S0))))) ->
    (* Flex-Assign — a defined head is substituted away and dropped *)
    (forall β τ Θ0',
       Θ0 = (β ~ abind_flex_mono_def τ) ++ Θ0' ->
       e_sub_order S0 NM (mode_fn M)
         (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0)
         (Ξ ++ Θ0')
         (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α))) ->
    (* Flex-Depend / Flex-Skip — an undefined non-target head *)
    (forall β Θ0',
       Θ0 = (β ~ abind_flex_mono) ++ Θ0' ->
       e_sub_flex_order S0 NM M P0 Θ0' (Ξ ++ (β ~ abind_flex_mono)) α
       /\ e_sub_flex_order S0 NM M P0 Θ0' Ξ α) ->
    (* Flex-SkipRigid *)
    (forall β Θ0',
       Θ0 = (β ~ abind_tvar) ++ Θ0' ->
       e_sub_flex_order S0 NM M P0 Θ0' Ξ α) ->
    (* Flex-SkipTmVar, both payload sorts *)
    (forall x A Θ0',
       Θ0 = (x ~ abind_var_typ A) ++ Θ0' ->
       e_sub_flex_order S0 NM M P0 Θ0' Ξ α) ->
    (forall x Q Θ0',
       Θ0 = (x ~ abind_var_skl Q) ++ Θ0' ->
       e_sub_flex_order S0 NM M P0 Θ0' Ξ α) ->
    e_sub_flex_order S0 NM M P0 Θ0 Ξ α.

Scheme e_sub_order_mind      := Induction for e_sub_order      Sort Prop
  with e_sub_flex_order_mind := Induction for e_sub_flex_order Sort Prop.
Combined Scheme e_sub_sub_flex_order_mutind
  from e_sub_order_mind, e_sub_flex_order_mind.
