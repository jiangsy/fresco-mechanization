(** Soundness of the algorithmic system (paper [algorithmic.tex] /
    [proofs.tex] / [subtyping-proofs.tex]).

    Each algorithmic judgment, when it succeeds, yields a *solution* to
    the corresponding question (in the sense of [def_question.v]): the
    output context is an information increase of the input, and the
    declarative judgment holds under the projected context together with
    the inherited-refinement side condition.  Proofs are [Admitted]
    scaffolding; the supporting lemmas live in [prop_lemmas.v]. *)

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

(* ===================================================================== *)
(*  Soundness of consistency (paper Lemma: Soundness of consistency,      *)
(*  part 1).  The mechanised [a_consis] is the type-level consistency     *)
(*  used by the typing rules; it yields declarative consistency under the *)
(*  projected context.  (Parts 2/3 — unification and assignment — and the *)
(*  skeleton-level [a_consis_solution] are consumed by subtyping.)        *)
(* ===================================================================== *)

Theorem a_consis_sound : forall Θ0 C B Θ1,
    a_consis Θ0 C B Θ1 ->
    exists θ1, Θ0 ≤[ θ1 ] Θ1 /\ d_consis empty ⌊ Θ1 ⌋ C B.
Proof. Admitted.

(* ===================================================================== *)
(*  Soundness of subtyping (paper Theorem: Soundness of subtyping).       *)
(*  If [⊢_{N;M;P₀} Θ₀ B ⊑ B₁ ⊣ Θ₁] then [(Θ₀ ≤ Θ₁; B₁)] is a solution.   *)
(* ===================================================================== *)

Theorem a_sub_sound : forall NM M P0 Θ0 B B1 Θ1,
    a_sub NM M P0 Θ0 B B1 Θ1 ->
    exists θ1, a_sub_solution M Θ0 P0 B θ1 Θ1 B1.
Proof. Admitted.

(* ===================================================================== *)
(*  Soundness of skeleton inference (paper Theorem: Soundness of          *)
(*  skeleton inference).  If [⊢_{M;P₀} Θ₀ e ⇨ P ⊣ Θ₁] then               *)
(*  [(Θ₀ ≤ Θ₁; P)] is a solution.                                        *)
(* ===================================================================== *)

Theorem a_pat_sound : forall M Θ0 P0 e P Θ1,
    a_pat M Θ0 P0 e P Θ1 ->
    exists θ1, a_pat_solution M Θ0 P0 e θ1 Θ1 P.
Proof. Admitted.

(* ===================================================================== *)
(*  Soundness of type inference (paper Theorem: Soundness of type         *)
(*  inference).  If [⊢_{M;P} Θ₀ e ⦂ A ⊣ Θ₁] then [(Θ₀ ≤ Θ₁; A)] is a     *)
(*  solution.                                                             *)
(* ===================================================================== *)

Theorem a_typing_sound : forall M Θ0 P e A Θ1,
    a_typing M Θ0 P e A Θ1 ->
    exists θ1, a_typing_solution M Θ0 P e θ1 Θ1 A.
Proof. Admitted.
