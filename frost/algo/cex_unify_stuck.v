(** COUNTEREXAMPLE: the mechanized [a_unify] gets STUCK when a subject is
    defined to a NON-VARIABLE monotype.  This is a MECH BUG, not a paper gap.

    ROOT CAUSE.  [Flex-Flex-Assign] (full-algo-spec.tex:1707) reads

        Θ₀ ⊢ α̂[τ/γ̂] ∼ β̂[τ/γ̂] ⊣ Θ₁
        --------------------------------------------
        Θ₀, γ̂ ≔ τ ⊢ unifyvar{α̂}{β̂} ⊣ Θ₁, γ̂ ≔ τ

    and that premise's `∼` is the CONSISTENCY relation, not unification:
    `\unify{A}{B}` renders `A ∼ B` (macro.tex:1234), and `\aconsis`'s relation is
    `\consis` = `\mathrel{\sim}` (macro.tex:1271) — the SAME symbol.  So the
    premise is *consistency of SUBJECT α̂[τ/γ̂] against INPUT β̂[τ/γ̂]*, exactly as
    `unifyvar{α̂}{β̂}` corresponds to the Flex rule's conclusion
    `aconsis[β̂]{Θ₀}{α̂}{α̂}{Θ₁}` (subject α̂, input β̂).

    The rule drops from `unifyvar` into CONSISTENCY precisely because
    substituting the definition can turn a variable subject into an arbitrary
    monotype — and consistency handles that, via FlexR.

    THE BUG: [a_unify__flex_assign] (algo/def_extra.v) recurses into [a_unify]
    instead.  [a_unify] has only var-var rules, so the algorithm has nowhere to
    go.  ([a_unify_var_inv] — "every derivable [a_unify] has VARIABLE subjects" —
    reads like a theorem but is a SYMPTOM of this.)

    Below: with  Θ₀ = (α̂ ≔ unit → unit), β̂  the mechanized algorithm cannot unify
    α̂ with β̂, although a solution plainly exists (send both to unit → unit), and
    the PAPER's rule would succeed: substituting gives the subject unit → unit,
    and consistency's FlexR assigns  β̂ ≔ unit → unit.

    A definition CAN be an arrow: that is exactly what [Assign-SolveM] produces
    via [guess^TY].

    FIX (open): [a_consis] / [a_unify] / [a_assign] must become MUTUALLY
    inductive.  See docs/PAPER-GAPS.md. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.
Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_decorate.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_consis_sound.

(** A flexible variable defined to an ARROW — a perfectly ordinary state: it is
    exactly what [Assign-SolveM] produces via [guess^TY]. *)
Definition Tarr : ptyp := ptyp_arrow ptyp_unit ptyp_unit.

Theorem a_unify_stuck_on_arrow_definition : forall (a b : atom),
  a <> b ->
  forall Θ1,
  ~ (((a ~ abind_flex_mono_def Tarr) ++ (b ~ abind_flex_mono) ++ nil)
       ⊲ (ptyp_var_f a) ≈ᵘ (ptyp_var_f b) ⊣ Θ1).
Proof.
  intros a b Hne Θ1 Hu.
  inversion Hu; subst; try congruence.
  (* Flex-Flex-Skip' : needs a RIGID or term entry at the head, not a
     definition *)
  all: try (match goal with
            | H : _ = abind_tvar \/ _ |- _ =>
                destruct H as [Hb | [[? Hb] | [? Hb]]]; inversion Hb
            end).
  (* Flex-Flex-Assign : THE case.  Substituting the definition turns the
     subject into  unit → unit  — no longer a variable.  The general [unify]
     judgment was supposed to take over here; it does not exist. *)
  all: match goal with
       | H : _ ⊲ _ ≈ᵘ _ ⊣ _ |- _ =>
           destruct (a_unify_var_inv H) as [[x Hx] _]
       end.
  all: simpl in Hx.
  (* NB destruct the hypothesis's OWN [if], not a re-elaborated [a == a] *)
  all: match goal with
       | H : context [ if ?t then _ else _ ] |- _ => destruct t
       end.
  (* [a = a] : the subject is now  unit → unit,  not a variable — contradiction
     with [a_unify_var_inv].   [a <> a] : absurd. *)
  all: solve [ inversion Hx | congruence ].
Qed.
