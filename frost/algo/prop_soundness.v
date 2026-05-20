(** Algorithmic soundness placeholders for the split syntax. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.coercions.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_typing.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.notations.
Require Import src.frost.algo.prop_completeness.

Set Implicit Arguments.

Lemma stability_d_typing : forall Γ0 Γ1 m e B,
    d_typing m Γ0 e B ->
    d_typing m Γ1 e B.
Proof.
Admitted.

Theorem a_sub_sound : forall NM m P0 Θ0 B1 B2 Θ1 Γ,
    a_sub NM m P0 Θ0 B1 B2 Θ1 ->
    a_transfers Θ1 Γ ->
    exists C, B1 = utyp_to_btyp C /\ d_sub m nil Γ C B2.
Proof.
Admitted.

Theorem a_pat_sound : forall m Θ0 P0 e Q Θ1 Γ,
    a_pat m Θ0 P0 e Q Θ1 ->
    a_transfers Θ1 Γ ->
    d_pat m Γ e Q.
Proof.
Admitted.

Theorem a_typing_sound : forall m Θ0 P0 e B Θ1 Γ,
    a_typing m Θ0 P0 e B Θ1 ->
    a_transfers Θ1 Γ ->
    d_typing m Γ e B.
Proof.
Admitted.

