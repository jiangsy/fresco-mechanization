(** Frost — consistency transitivity for the split syntax. *)

Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.subtyping.prop_basics.

Set Implicit Arguments.

Lemma list_swap_middle : forall {A : Type} (l1 l2 l3 l4 : list A),
    Permutation ((l1 ++ l2) ++ (l3 ++ l4)) ((l1 ++ l3) ++ (l2 ++ l4)).
Proof.
  intros A l1 l2 l3 l4.
  replace ((l1 ++ l2) ++ (l3 ++ l4)) with (l1 ++ l2 ++ l3 ++ l4).
  - replace ((l1 ++ l3) ++ (l2 ++ l4)) with (l1 ++ l3 ++ l2 ++ l4).
    + apply Permutation_app_head. apply Permutation_app_swap_app.
    + rewrite app_assoc. reflexivity.
  - rewrite app_assoc. reflexivity.
Qed.

(** Paper B.2, native split form for a synthesized middle type. *)
Lemma d_consis_compose : forall Δa Δb Γ C A B,
    Δa ⨟ Γ ⊨ C ≈ ptyp_to_btyp_syn A ->
    Δb ⨟ Γ ⊨ ptyp_to_utyp_syn A ≈ B ->
    list_disjoint Δa Δb ->
    exists Δc, Permutation Δc (Δa ++ Δb) /\ Δc ⨟ Γ ⊨ C ≈ B.
Proof.
Admitted.

Lemma d_consis_compose_nil_RHS : forall Γ C A B,
    nil ⨟ Γ ⊨ C ≈ ptyp_to_btyp_syn A ->
    nil ⨟ Γ ⊨ ptyp_to_utyp_syn A ≈ B ->
    nil ⨟ Γ ⊨ C ≈ B.
Proof.
  intros Γ C A B H1 H2.
  edestruct d_consis_compose as [Δc [Hperm Hc]];
    [ exact H1 | exact H2 | apply list_disjoint_nil_l | ].
  simpl in Hperm. apply Permutation_sym in Hperm.
  apply Permutation_nil in Hperm. subst. exact Hc.
Qed.
