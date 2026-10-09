(** THE ALIAS COLLAPSE — [collapse1 γ ε Θ] drops the alias entry
    [γ ≔ ε̂] and renames [ε̂] back to [γ] everywhere (keys and payloads).
    It was built for lifting the consistency runner's completeness off its
    hole-free restriction along the PRE-NORMALISATION route
    (docs/HANDOFF-close-consis-unrestricted.md §5 (R1)); that route closed
    another way, and the definitions stay as the statement
    cex/probe_collapse_orientation.v refutes.  ⚙ [rename_aenv] is the
    DIRECTED rename, kept by prop_swap.v's own header "where a proof
    genuinely needs the one-way form": a collapse MERGES [ε̂] into [γ] — it
    is not injective on {γ, ε̂} — so no transposition can express it.

    ⛔⛔ WHAT THIS FILE DOES **NOT** SUPPORT, and must not be used for:
    an EXACT transport of a derivation across [collapse1] — i.e. "the
    collapsed derivation's output is [collapse1] of the original's".
    That is REFUTED, machine-checked, by cex/probe_collapse_orientation.v:
    at the alias entry a walk must take [Assign-Assign], which converts it
    to a CONSIS, and when the payload is the alias variable itself that
    consis is a UNIFY whose [Flex-Flex-R] orients the new definition the
    OPPOSITE way from the collapsed walk's [SolveM] — [(α̂ ≔ γ̂, γ̂)]
    against [(γ̂ ≔ α̂, α̂)], the same equivalence class with a different
    REPRESENTATIVE.  ⚙ The handover records this as dead end 5 and derives
    constraint C6 (orientation-tolerance) from it, which is what rules out
    ANY relation that is a function of the context. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.prop_swap.
Require Import src.fresco.algo.prop_basic.
Require Import src.fresco.algo.consis.prop_consis_rename.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.def_supply.
Require Import src.fresco.ext_algo.def_guess.
Require Import src.fresco.ext_algo.def_consis.

Set Implicit Arguments.

Open Scope fresco_a_scope.
Open Scope fresco_e_scope.

(** Remove every [α]-keyed entry (under [uniq] there is at most one). *)
Fixpoint aenv_remove (α : atom) (Θ : aenv) : aenv :=
  match Θ with
  | nil => nil
  | (x, b) :: Θ' =>
      if x == α then aenv_remove α Θ' else (x, b) :: aenv_remove α Θ'
  end.

(** Collapse the alias [γ ≔ ε̂]: drop [γ]'s entry, rename [ε̂] back to [γ]
    (keys and payloads — [ε̂]'s own entry becomes [γ]'s). *)
Definition collapse1 (γ ε : atom) (Θ : aenv) : aenv :=
  rename_aenv γ ε (aenv_remove γ Θ).
