(** Fresco — basic syntactic lemmas for the current split syntax. *)

Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.prop_tag.
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
#[local] Hint Constructors d_refine_syn d_refine_pskl : refinement.

Lemma d_refine_syn_any_ctx : forall Γ Δ Q Q',
    {{ Γ ⨟ Δ ⊢ᵣ Q ⊳ Q' }}d -> forall Γ', {{ Γ' ⨟ Δ ⊢ᵣ Q ⊳ Q' }}d.
Proof.
  intros Γ Δ Q Q' H; induction H; intros Γ'; eauto 4 with refinement.
Qed.

Lemma d_refine_pskl_any_ctx : forall Γ Δ P P',
    {{ Γ ⨟ Δ ⊢ᵣₚ P ⊳ P' }}d -> forall Γ', {{ Γ' ⨟ Δ ⊢ᵣₚ P ⊳ P' }}d.
Proof.
  intros Γ Δ P P' H; induction H; intros Γ'; eauto 4 with refinement.
Qed.

(** * Local closure for shape predicates. *)

(** At [mode_tc] the RHS of [⩽] is always inherited.  This is why
    [d_sub__forall_r] needs no [is_ityp] premise (the paper's ForallR has
    none): its body is itself a TC-mode subtyping. *)
Lemma d_sub_tc_is_ityp : forall Ψ Γ C B,
    {{ Ψ ⨟ Γ ⊢[ mode_tc ] C ⩽ B }}d -> is_ityp B.
Proof.
  intros Ψ Γ C B H. remember mode_tc as m eqn:Hm.
  induction H; subst; try discriminate; auto.
  apply is_ityp__all with (L := L). intros α Hα. auto.
Qed.

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

(* ⚙ Moved here 2026-10-10 from algo/consis/prop_consis_precise.v: it is a
   fact about the declarative [d_tags_skl] alone. *)
(** A decorated skeleton's tag reading is exactly its syntactic tags. *)
Lemma d_tags_skl_ftag : forall Ψ ψ,
  d_tags_skl Ψ ψ -> Ψ [=] ftag_in_uskl ψ.
Proof.
  intros Ψ ψ H; induction H; simpl; try fsetdec.
  - match goal with |- _ [=] add _ (ftag_in_uskl ?R) =>
      pick fresh α for L;
      pose proof (H0 α ltac:(solve_notin_auto)) as Hα;
      pose proof (ftag_in_uskl_open_var R α) as Hov
    end; fsetdec.
Qed.
