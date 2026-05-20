(** Frost — consistency-subtyping transitivity for the split syntax. *)

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
Require Import src.frost.decl.subtyping.prop_consis_trans.

Set Implicit Arguments.

(** Paper B.3, native split form. *)
Lemma d_consis_sub_trans : forall M Δ Δ' Γ C A B,
    Δ ⨟ Γ ⊨ C ≈ ptyp_to_btyp_syn A ->
    Δ' ⨟ Γ ⊢[ M ] (ptyp_to_utyp_syn A) ⊑ B ->
    list_disjoint Δ Δ' ->
    exists Δc, Permutation Δc (Δ ++ Δ') /\ Δc ⨟ Γ ⊢[ M ] C ⊑ B.
Proof.
Admitted.

Lemma d_consis_sub_trans_nil : forall M Γ C A B,
    nil ⨟ Γ ⊨ C ≈ ptyp_to_btyp_syn A ->
    nil ⨟ Γ ⊢[ M ] (ptyp_to_utyp_syn A) ⊑ B ->
    nil ⨟ Γ ⊢[ M ] C ⊑ B.
Proof.
  intros M Γ C A B Hc Hs.
  edestruct d_consis_sub_trans as [Δc [Hperm Hsub]];
    [ exact Hc | exact Hs | apply list_disjoint_nil_l | ].
  simpl in Hperm. apply Permutation_sym in Hperm.
  apply Permutation_nil in Hperm. subst. exact Hsub.
Qed.
