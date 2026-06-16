(** Soundness of the algorithmic system (paper [algorithmic.tex] /
    [proofs.tex] / [subtyping-proofs.tex]).

    Each algorithmic judgment, when it succeeds, yields a *solution* to
    the corresponding question (in the sense of [def_question.v]): the
    output context is an information increase of the input, and the
    declarative judgment holds under the projected context [⌊Θ⌋] together
    with the inherited-refinement side condition.  The algorithm is
    uncoloured ([ptyp]/[pskl]); painting to the declarative sorts happens
    inside the solution predicates.  Proofs are [Admitted] scaffolding. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.coercions.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.notations.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_question.
Require Import src.frost.algo.prop_lemmas.

Set Implicit Arguments.

(* Soundness of consistency (paper Lemma: Soundness of consistency). *)
Theorem a_consis_sound : forall Θ0 P0 P Q Θ1,
    a_consis Θ0 P0 P Q Θ1 ->
    exists θ1, a_consis_solution Θ0 P0 P θ1 Θ1 Q.
Proof. Admitted.

(* Soundness of subtyping (paper Theorem: Soundness of subtyping). *)
Theorem a_sub_sound : forall NM M P0 Θ0 P Q Θ1,
    a_sub NM M P0 Θ0 P Q Θ1 ->
    exists θ1, a_sub_solution M Θ0 P0 P θ1 Θ1 Q.
Proof. Admitted.

(* Soundness of skeleton inference (paper Theorem). *)
Theorem a_pat_sound : forall M Θ0 P0 e P Θ1,
    a_pat M Θ0 P0 e P Θ1 ->
    exists θ1, a_pat_solution M Θ0 P0 e θ1 Θ1 P.
Proof. Admitted.

(* Soundness of type inference (paper Theorem: Soundness of type inference). *)
Theorem a_typing_sound : forall M Θ0 P e A Θ1,
    a_typing M Θ0 P e A Θ1 ->
    exists θ1, a_typing_solution M Θ0 P e θ1 Θ1 A.
Proof. Admitted.
