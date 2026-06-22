(** Completeness and optimality of the algorithmic system (paper
    [algorithmic.tex] / [proofs.tex]).

    Dual to [prop_soundness.v]: whenever a question has *some* solution,
    the algorithm succeeds and returns the *optimal* one (every other
    solution factors through it via a cofactor metasubstitution — see the
    [_optimal] predicates in [def_question.v]).  Proofs are [Admitted]
    scaffolding. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.coercions.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_question.
Require Import src.frost.algo.prop_lemmas.

Set Implicit Arguments.

(* Completeness and optimality of consistency (paper Lemma). *)
Theorem a_consis_complete : forall Θ0 P0 P,
    a_consis_solution_ex Θ0 P0 P ->
    exists θ1 Θ1 Q, Θ0 ⊢ₐ[ P0 ] P ~ᴬ Q ⊣ Θ1 /\ a_consis_optimal Θ0 P0 P θ1 Θ1 Q.
Proof. Admitted.

(* Completeness and optimality of subtyping (paper Theorem). *)
Theorem a_sub_complete : forall NM M P0 Θ0 P,
    a_sub_solution_ex M Θ0 P0 P ->
    exists θ1 Θ1 Q, Θ0 ⊢ₐ[ NM | M | P0 ] P ⊑ᴬ Q ⊣ Θ1 /\ a_sub_optimal M Θ0 P0 P θ1 Θ1 Q.
Proof. Admitted.

(* Completeness and optimality of skeleton inference (paper Theorem). *)
Theorem a_pat_complete : forall M Θ0 P0 e,
    a_pat_solution_ex M Θ0 P0 e ->
    exists θ1 Θ1 P, Θ0 ⊢ₐ[ M ; P0 ] e ⇨ P ⊣ Θ1 /\ a_pat_optimal M Θ0 P0 e θ1 Θ1 P.
Proof. Admitted.

(* Completeness and optimality of type inference (paper Theorem). *)
Theorem a_typing_complete : forall M Θ0 P e,
    a_typing_solution_ex M Θ0 P e ->
    exists θ1 Θ1 A, Θ0 ⊢ₐ[ M ; P ] e ⦂ A ⊣ Θ1 /\ a_typing_optimal M Θ0 P e θ1 Θ1 A.
Proof. Admitted.
