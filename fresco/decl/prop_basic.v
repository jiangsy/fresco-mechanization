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

(** [bskl_to_pskl] preserves guardedness ([guarded] only ranges over
    unit / var / arrow, all of which [bskl_to_pskl] maps homomorphically;
    the arrow case needs local-closure preservation [lc_bskl_to_pskl]). *)
Lemma guarded_bskl_to_pskl : forall Q,
    guarded_bskl Q -> guarded_pskl (bskl_to_pskl Q).
Proof.
  intros Q H. induction H; simpl.
  - apply guarded_pskl__unit.
  - apply guarded_pskl__var.
  - apply guarded_pskl__arrow; apply lc_bskl_to_pskl; assumption.
Qed.

(** * list_disjoint algebra. *)

(** * Local closure for shape predicates. *)

Lemma is_ityp_lc : forall B, is_ityp B -> lc_btyp B.
Proof.
  intros B H. induction H; eauto.
Qed.

Lemma is_styp_lc : forall B, is_styp B -> lc_btyp B.
Proof.
  intros B H. induction H; eauto.
Qed.

Lemma is_ttyp_lc : forall C, is_ttyp C -> lc_utyp C.
Proof.
  intros C H. induction H; eauto.
Qed.

(** * Coercion local-closure preservation. *)

(** The synthesised painting of any locally-closed [ptyp] is synthesised
    ([is_styp]): every ∀ becomes [btyp_all_syn].  (Induct on [lc_ptyp] so the
    ∀ body's [is_styp] follows from the per-instance IH.) *)
Lemma is_styp_ptyp_to_btyp_syn : forall A,
    lc_ptyp A -> is_styp (ptyp_to_btyp_syn A).
Proof.
  intros A H. induction H; simpl.
  - constructor.
  - constructor.
  - constructor; assumption.
  - apply is_styp__all with (L := empty). intros α _.
    change (btyp_var_f α) with (ptyp_to_btyp_syn (ptyp_var_f α)).
    rewrite <- ptyp_to_btyp_syn_open.
    match goal with H : forall _, is_styp _ |- _ => apply H end.
Qed.

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
  - apply d_tags_skl__holeg; fsetdec.
  - apply d_tags_skl__topholeg; apply IHd_tags_skl; exact Heq.
Qed.
