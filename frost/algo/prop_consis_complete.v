(** Problems, solutions, and OPTIMALITY for consistency
    — the notions [thm:complete-consistency] is stated against.
    (full-algo-spec.tex:1476-1519, "Problems and solutions of consistency").

    These are the notions [thm:complete-consistency] is stated against.  Note
    they are where the paper's EXTERNAL well-formedness conditions land: a
    problem REQUIRES its skeletons to be well-formed in Θ₀
    (docs/WF-SIDE-CONDITIONS.md).

    Optimality is the interesting one.  It says the algorithm's solution is the
    MOST GENERAL one: every other solution factors through it, via a further
    metasubstitution ζ — which is exactly why completeness needs COMPOSITION
    (`θ ≡ ζ ∘ θ₁`, see algo/prop_compose.v) and PRECISION (`ζP₁ ⊑ Q`, see
    algo/prop_precise.v).  Those two were the prerequisites; this file states
    what they are for. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_decorate.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_compose.
Require Import src.frost.algo.prop_precise.

Set Implicit Arguments.

(* ===================================================================== *)
(*  1.  Consistency                                                       *)
(* ===================================================================== *)

(** A problem of consistency is a tuple (Θ₀; P₀; P) where P₀ and P are
    well-formed in Θ₀.  (The paper's external wf condition, made a premise.) *)
Definition a_consis_problem (Θ0 : aenv) (P0 P : pskl) : Prop :=
  a_wf_aenv Θ0 /\ a_wf_pskl Θ0 P0 /\ a_wf_pskl Θ0 P.

(** A solution is a tuple (Θ₀ ⊑[θ₁] Θ₁; P₁) such that the substituted input is
    consistent with P₁, and P₁ is a refinement of the substituted input
    skeleton. *)
Definition a_consis_solution
    (Θ0 : aenv) (P0 P : pskl) (θ1 : metasubst) (Θ1 : aenv) (P1 : bskl) : Prop :=
  Θ0 ≤[ θ1 ] Θ1 /\
  empty ⨟ Θ1 ⊨ₛᵃ (pskl_to_uskl (msubst_pskl θ1 P)) ≈ P1 /\
  Θ1 ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl θ1 P0)) ⊳ P1.

(** The solution is OPTIMAL if every other solution factors through it: there is
    a ζ carrying Θ₁ to the other target, with θ ≡ ζ∘θ₁, and the algorithm's
    output is at least as PRECISE as the other one's. *)
Definition a_consis_optimal
    (Θ0 : aenv) (P0 P : pskl) (θ1 : metasubst) (Θ1 : aenv) (P1 : bskl) : Prop :=
  forall θ Θ Q,
    a_consis_solution Θ0 P0 P θ Θ Q ->
    exists ζ,
      Θ1 ≤[ ζ ] Θ /\
      a_inc_equiv Θ0 θ (msubst_compose ζ θ1) Θ /\
      Θ ⨟ empty ⊢ᵣᵃ (msubst_bskl ζ P1) ⊳ Q.

(* ===================================================================== *)
(*  2.  Unification of flexible variables                                 *)
(* ===================================================================== *)

(** The paper's [α̂]/[β̂] are HATTED — flexible, defined or not.  [α `in` dom Θ0]
    would also admit RIGID and TERM variables, which [unifyvar] does not take.
    All four [a_unify] rules now carry [a_flex_tvar] explicitly (the hatted
    prose-completion, docs/PAPER-GAPS.md), so the problem must say so too. *)
Definition a_unify_problem (Θ0 : aenv) (α β : atom) : Prop :=
  a_wf_aenv Θ0 /\ a_flex_tvar Θ0 α /\ a_flex_tvar Θ0 β.

Definition a_unify_solution
    (Θ0 : aenv) (α β : atom) (θ1 : metasubst) (Θ1 : aenv) : Prop :=
  Θ0 ≤[ θ1 ] Θ1 /\
  Θ1 ⊢ (msubst_lookup θ1 α) ≡ᵗ (msubst_lookup θ1 β).

Definition a_unify_optimal
    (Θ0 : aenv) (α β : atom) (θ1 : metasubst) (Θ1 : aenv) : Prop :=
  forall θ Θ,
    a_unify_solution Θ0 α β θ Θ ->
    exists ζ,
      Θ1 ≤[ ζ ] Θ /\
      a_inc_equiv Θ0 θ (msubst_compose ζ θ1) Θ.

(* ===================================================================== *)
(*  3.  Assignment of a flexible variable                                 *)
(* ===================================================================== *)

(** NB [P] is well-formed in [Ξ ++ Θ0], NOT in [Θ0].  [Assign-Depend] MOVES
    flexible variables out of [Θ0] into [Ξ] while [P] keeps mentioning them —
    its premise is literally [β ∈ ftv(P)] — so at a recursive assignment node
    [P]'s free variables are spread across both.  The soundness side already
    has this right ([assign_sound_concl] asks for [(Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P]).
    The two readings coincide only at the top-level call, where [Ξ = nil], which
    is why the bug was invisible.  Same for [a_non_flex].

    [dom Ξ ⊆ ftv(P)] is the paper's own invariant on [Ξ] — "Ξ only contains
    declarations of flexible variables APPEARING IN P" (full-algo-spec.tex:1508-1509)
    — which [a_decls Ξ] alone does not express ([a_decls] says only "every entry
    is an undefined flexible variable").  [Assign-Depend] maintains it.

    The subject is HATTED, as in [a_unify_problem] above. *)
Definition a_assign_problem (Θ0 : aenv) (Ξ : aenv) (α : atom) (P : pskl) : Prop :=
  a_wf_aenv (Ξ ++ Θ0) /\ a_flex_tvar Θ0 α /\
  a_wf_pskl (Ξ ++ Θ0) P /\ a_non_flex (Ξ ++ Θ0) P /\
  a_decls Ξ /\ dom Ξ [<=] ftvar_in_pskl P.

Definition a_assign_solution
    (Θ0 Ξ : aenv) (α : atom) (P : pskl) (θ1 : metasubst) (Θ1 : aenv) : Prop :=
  (Ξ ++ Θ0) ≤[ θ1 ] Θ1 /\
  empty ⨟ Θ1 ⊨ₛᵃ (pskl_to_uskl (msubst_pskl θ1 P))
                ≈ (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup θ1 α))).

Definition a_assign_optimal
    (Θ0 Ξ : aenv) (α : atom) (P : pskl) (θ1 : metasubst) (Θ1 : aenv) : Prop :=
  forall θ Θ,
    a_assign_solution Θ0 Ξ α P θ Θ ->
    exists ζ,
      Θ1 ≤[ ζ ] Θ /\
      a_inc_equiv (Ξ ++ Θ0) θ (msubst_compose ζ θ1) Θ.
