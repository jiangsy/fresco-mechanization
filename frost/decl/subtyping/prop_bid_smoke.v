(** Smoke tests for the split type hierarchy.

    The old file tested the temporary [_bid] compatibility layer. That
    layer is gone; this file now checks the native [utyp]/[btyp]
    infer rule shape. *)

Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.subtyping.prop_basics.

Lemma d_sub_infer_smoke :
  forall Γ C B,
    empty ⨟ Γ ⊨ C ≈ B ->
    is_styp B ->
    empty ⨟ Γ ⊢[ mode_ti ] C ⊑ B.
Proof.
  intros. apply d_sub__infer; auto. reflexivity.
Qed.

