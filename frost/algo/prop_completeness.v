(** Algorithmic completeness placeholders for the split syntax. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.coercions.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_typing.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.notations.

Set Implicit Arguments.

Inductive a_transfers : aenv -> list (atom * dbind) -> Prop :=
| a_transfers__nil : a_transfers nil nil
| a_transfers__decl : forall Θ Γ,
    a_transfers Θ Γ.

Theorem a_sub_decidable_existential :
  forall NM m P0 Θ B1 B2,
    (exists Θ', a_sub NM m P0 Θ B1 B2 Θ') \/
    (forall Θ', ~ a_sub NM m P0 Θ B1 B2 Θ').
Proof.
Admitted.

Theorem a_sub_complete : forall Γ Θ0 m C B,
    d_sub m empty Γ C B ->
    a_transfers Θ0 Γ ->
    exists Θ1 NM P0,
      a_sub NM m P0 Θ0 (utyp_to_btyp C) B Θ1 /\ a_transfers Θ1 Γ.
Proof.
Admitted.

Theorem a_pat_complete : forall Γ Θ0 m e Q,
    d_pat m Γ e Q ->
    a_transfers Θ0 Γ ->
    exists Θ1 P0,
      a_pat m Θ0 P0 e Q Θ1 /\ a_transfers Θ1 Γ.
Proof.
Admitted.

Theorem a_typing_complete : forall Γ Θ0 m e B,
    d_typing m Γ e B ->
    a_transfers Θ0 Γ ->
    exists Θ1 P0,
      a_typing m Θ0 P0 e B Θ1 /\ a_transfers Θ1 Γ.
Proof.
Admitted.

