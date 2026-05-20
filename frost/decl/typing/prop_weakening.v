(** Frost declarative typing weakening, native split-syntax form. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.prop_subtyping.

Set Implicit Arguments.

Lemma d_typing_weakening : forall Γ1 Γ2 Γ3 m e B,
    d_typing m (Γ1 ++ Γ3) e B ->
    d_typing m (Γ1 ++ Γ2 ++ Γ3) e B.
Proof.
Admitted.

Lemma d_pat_weakening : forall Γ1 Γ2 Γ3 m e Q,
    d_pat m (Γ1 ++ Γ3) e Q ->
    d_pat m (Γ1 ++ Γ2 ++ Γ3) e Q.
Proof.
Admitted.

Lemma d_typing_weakening_head : forall Γ Γ' m e B,
    d_typing m Γ e B ->
    d_typing m (Γ' ++ Γ) e B.
Proof.
  intros Γ Γ' m e B H.
  rewrite_env (nil ++ Γ' ++ Γ).
  apply d_typing_weakening. exact H.
Qed.

Lemma d_pat_weakening_head : forall Γ Γ' m e Q,
    d_pat m Γ e Q ->
    d_pat m (Γ' ++ Γ) e Q.
Proof.
  intros Γ Γ' m e Q H.
  rewrite_env (nil ++ Γ' ++ Γ).
  apply d_pat_weakening. exact H.
Qed.

