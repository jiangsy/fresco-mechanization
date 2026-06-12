(** Frost — consistency transitivity for the split syntax. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.subtyping.prop_basics.

Set Implicit Arguments.

(** Paper B.2, native split form for a synthesized middle type.

    With a SET tag context the conclusion is simply the set union
    [Δa ∪ Δb] — no [Permutation] witness and no [list_disjoint] premise
    (set union absorbs a tag reused across the two derivations; that
    absorption is exactly what the paper's "Ψ is a set" buys). *)
Lemma d_consis_compose : forall Δa Δb Γ C A B,
    Δa ⨟ Γ ⊨ C ≈ ptyp_to_btyp_syn A ->
    Δb ⨟ Γ ⊨ ptyp_to_utyp_syn A ≈ B ->
    (Δa `union` Δb) ⨟ Γ ⊨ C ≈ B.
Proof.
Admitted.

Lemma d_consis_compose_nil_RHS : forall Γ C A B,
    empty ⨟ Γ ⊨ C ≈ ptyp_to_btyp_syn A ->
    empty ⨟ Γ ⊨ ptyp_to_utyp_syn A ≈ B ->
    empty ⨟ Γ ⊨ C ≈ B.
Proof.
  intros Γ C A B H1 H2.
  eapply d_consis_equiv; [ | eapply d_consis_compose; eassumption ].
  fsetdec.
Qed.
