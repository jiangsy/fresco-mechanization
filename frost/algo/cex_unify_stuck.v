(** COUNTEREXAMPLE: [a_unify] gets STUCK when a subject is defined to a
    NON-VARIABLE monotype — so completeness of consistency fails as it stands.

    ROOT CAUSE (paper).  The paper has TWO unification judgments:

      unifyvar{α̂}{β̂}   rendered  α̂ ≃ β̂   -- BOXED, with rules
                                             (full-algo-spec.tex:1679)
      unify{A}{B}      rendered  A ∼ B    -- used in THREE rule premises,
                                             but NEVER boxed and NEVER given
                                             any rules

    `\unify` is used at full-algo-spec.tex:393 (skeleton splitting, where it
    unifies a flexible variable with an ARROW: `unify{α̂}{β̂ → γ̂}`), :1707
    (Flex-Flex-Assign), and :1754 (Assign-Assign).  Its premise in
    Flex-Flex-Assign is

        Θ₀ ⊢ unify{α̂[τ/γ̂]}{β̂[τ/γ̂]} ⊣ Θ₁
        --------------------------------------------
        Θ₀, γ̂ ≔ τ ⊢ unifyvar{α̂}{β̂} ⊣ Θ₁, γ̂ ≔ τ

    — note the premise DROPS from `unifyvar` into the general `unify`, precisely
    because substituting a definition may turn a variable subject into an
    arbitrary monotype.  General `unify` is what is supposed to handle that.
    It is never defined.

    The mechanization collapsed the two into a single var-only [a_unify].  Hence
    [a_unify_var_inv] (every derivable [a_unify] has VARIABLE subjects) — which
    reads like a theorem but is really a symptom of the missing rules.  The
    algorithm therefore gets stuck exactly where the general judgment was needed.

    Below: with  Θ₀ = (α̂ ≔ unit → unit), β̂  the algorithm cannot unify α̂ with β̂,
    although a solution plainly exists (send both to unit → unit). *)

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
