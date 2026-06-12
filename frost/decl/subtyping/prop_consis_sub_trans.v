(** Frost — consistency-subtyping transitivity for the split syntax. *)

Require Import Coq.Lists.List.
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

(** Paper B.3, native split form.  Set tag context ⟹ the conclusion is the
    union [Δ ∪ Δ'] with no [Permutation]/[list_disjoint] bookkeeping. *)
Lemma d_consis_sub_trans : forall M Δ Δ' Γ C A B,
    Δ ⨟ Γ ⊨ C ≈ ptyp_to_btyp_syn A ->
    Δ' ⨟ Γ ⊢[ M ] (ptyp_to_utyp_syn A) ⊑ B ->
    (Δ `union` Δ') ⨟ Γ ⊢[ M ] C ⊑ B.
Proof.
Admitted.

Lemma d_consis_sub_trans_nil : forall M Γ C A B,
    empty ⨟ Γ ⊨ C ≈ ptyp_to_btyp_syn A ->
    empty ⨟ Γ ⊢[ M ] (ptyp_to_utyp_syn A) ⊑ B ->
    empty ⨟ Γ ⊢[ M ] C ⊑ B.
Proof.
  intros M Γ C A B Hc Hs.
  eapply d_sub_equiv; [ | eapply d_consis_sub_trans; eassumption ].
  fsetdec.
Qed.
