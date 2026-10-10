(** Fresco — basic syntactic lemmas for the current split syntax. *)

Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_basic.
Require Import src.fresco.decl.def_rules.

Set Implicit Arguments.

(** * Refinement does not read its context.

    No rule of [d_refine_syn] / [d_refine_pskl] consults [Γ] (the paper's
    rules carry no scoping premise; well-formedness is an external
    presupposition), so a derivation transports to ANY context.  This one
    lemma replaces weakening, strengthening and every other context change. *)
Lemma d_refine_syn_any_ctx : forall Γ Δ Q Q',
    {{ Γ ⨟ Δ ⊢ᵣ Q ⊳ Q' }}d -> forall Γ', {{ Γ' ⨟ Δ ⊢ᵣ Q ⊳ Q' }}d.
Proof.
  intros Γ Δ Q Q' H; induction H; intros Γ'.
  - apply d_refine_syn__unit.
  - apply d_refine_syn__var.
  - apply d_refine_syn__arrow; auto.
  - apply d_refine_syn__all with (L := L); [ assumption | ]. intros α Hα. auto.
  - apply d_refine_syn__ghost. assumption.
  - apply d_refine_syn__univ_ghost_remove; auto.
  - apply d_refine_syn__univ_ghost_fill with (L := L); [ assumption | ].
    intros α Hα. auto.
  - apply d_refine_syn__univ_ghost_keep; auto.
Qed.

Lemma d_refine_pskl_any_ctx : forall Γ Δ P P',
    {{ Γ ⨟ Δ ⊢ᵣₚ P ⊳ P' }}d -> forall Γ', {{ Γ' ⨟ Δ ⊢ᵣₚ P ⊳ P' }}d.
Proof.
  intros Γ Δ P P' H; induction H; intros Γ'.
  - apply d_refine_pskl__unit.
  - apply d_refine_pskl__var.
  - apply d_refine_pskl__arrow; auto.
  - apply d_refine_pskl__all with (L := L). intros α Hα. auto.
  - apply d_refine_pskl__ghost. assumption.
  - apply d_refine_pskl__univ_ghost_remove; auto.
  - apply d_refine_pskl__univ_ghost_fill with (L := L). intros α Hα. auto.
  - apply d_refine_pskl__univ_ghost_keep; auto.
Qed.

(** * Local closure for shape predicates. *)

Lemma is_ityp_lc : forall B, is_ityp B -> lc_btyp B.
Proof.
  intros B H. induction H; eauto.
Qed.

Lemma is_styp_lc : forall B, is_styp B -> lc_btyp B.
Proof.
  intros B H. induction H; eauto.
Qed.

Lemma is_dtyp_lc : forall C, is_dtyp C -> lc_utyp C.
Proof.
  intros C H. induction H; eauto.
Qed.

(** * Coercion local-closure preservation. *)

(** [d_tags_skl] respects set-equality of the tag context. *)
Lemma d_tags_skl_psi_cong : forall Ψ Ψ' ψ,
  d_tags_skl Ψ ψ -> Ψ [=] Ψ' -> d_tags_skl Ψ' ψ.
Proof.
  intros Ψ Ψ' ψ H; revert Ψ'; induction H; intros Ψ' Heq.
  - apply d_tags_skl__unit; fsetdec.
  - apply d_tags_skl__var; fsetdec.
  - eapply d_tags_skl__arrow;
      [ exact H | exact H0 | exact H1 | clear - H2 Heq; fsetdec ].
  - eapply d_tags_skl__all_tag;
      [ exact H | exact H1 | clear - H2 Heq; fsetdec ].
  - apply d_tags_skl__dot_ghost; fsetdec.
  - apply d_tags_skl__dot_univ_ghost; apply IHd_tags_skl; exact Heq.
Qed.
