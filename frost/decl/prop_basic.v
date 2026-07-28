(** Frost — basic syntactic lemmas for the current split syntax. *)

Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.

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


Lemma list_disjoint_nil_l : forall (ys : list atom),
    list_disjoint nil ys.
Proof.
  intros ys a Hy. inversion Hy.
Qed.


Lemma list_disjoint_cons_l : forall (a : atom) (xs ys : list atom),
    ~ List.In a ys ->
    list_disjoint xs ys ->
    list_disjoint (a :: xs) ys.
Proof.
  intros a xs ys Hni Hd b Hb Hin.
  destruct Hb as [Heq | Hb].
  - subst. contradiction.
  - apply (Hd b); auto.
Qed.


(** * Local closure for shape predicates. *)

Lemma mono_ptyp_lc : forall A, mono_ptyp A -> lc_ptyp A.
Proof.
  intros A H. induction H; constructor; auto.
Qed.


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


(** * Inclusion facts. *)

Lemma is_styp_is_syn : forall B, is_styp B -> is_syn B.
Proof.
  intros B H. induction H.
  - constructor.
  - constructor.
  - constructor; auto.
  - apply is_syn__all with (L := L); auto.
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
