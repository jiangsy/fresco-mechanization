(** Frost — basic syntactic lemmas. Populated as Phase 2 needs them. *)

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.

(** * Coercion / opening commutation lemmas. *)

(** [bskl_to_pskl] commutes with (recursive) opening. *)
Lemma bskl_to_pskl_open_rec : forall Q V k,
    bskl_to_pskl (open_bskl_wrt_bskl_rec k V Q) =
    open_pskl_wrt_pskl_rec k (bskl_to_pskl V) (bskl_to_pskl Q).
Proof.
  induction Q; intros V k; simpl; try reflexivity;
    try (rewrite IHQ; reflexivity);
    try (rewrite IHQ1, IHQ2; reflexivity).
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
Qed.

(** [bskl_to_pskl] commutes with opening by a free variable. *)
Lemma bskl_to_pskl_open : forall Q X,
    bskl_to_pskl (open_bskl_wrt_bskl Q (bskl_var_f X)) =
    open_pskl_wrt_pskl (bskl_to_pskl Q) (pskl_var_f X).
Proof.
  intros. unfold open_bskl_wrt_bskl, open_pskl_wrt_pskl.
  apply (bskl_to_pskl_open_rec Q (bskl_var_f X) 0).
Qed.

(** [bskl_to_pskl] is a left inverse of the synthesised painting. *)
Lemma bskl_to_pskl_pskl_to_bskl_syn : forall P,
    bskl_to_pskl (pskl_to_bskl_syn P) = P.
Proof.
  induction P; simpl; try reflexivity;
    try (rewrite IHP; reflexivity);
    try (rewrite IHP1, IHP2; reflexivity).
Qed.
