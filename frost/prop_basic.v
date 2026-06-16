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

(** [ptyp_to_pskl] commutes with (recursive) opening. *)
Lemma ptyp_to_pskl_open_rec : forall A V k,
    ptyp_to_pskl (open_ptyp_wrt_ptyp_rec k V A) =
    open_pskl_wrt_pskl_rec k (ptyp_to_pskl V) (ptyp_to_pskl A).
Proof.
  induction A; intros V k; simpl; try reflexivity;
    try (rewrite IHA; reflexivity);
    try (rewrite IHA1, IHA2; reflexivity).
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
Qed.

Lemma ptyp_to_pskl_open : forall A X,
    ptyp_to_pskl (open_ptyp_wrt_ptyp A (ptyp_var_f X)) =
    open_pskl_wrt_pskl (ptyp_to_pskl A) (pskl_var_f X).
Proof.
  intros. unfold open_ptyp_wrt_ptyp, open_pskl_wrt_pskl.
  apply (ptyp_to_pskl_open_rec A (ptyp_var_f X) 0).
Qed.

(** [pskl_to_bskl_inh] commutes with (recursive) opening. *)
Lemma pskl_to_bskl_inh_open_rec : forall P V k,
    pskl_to_bskl_inh (open_pskl_wrt_pskl_rec k V P) =
    open_bskl_wrt_bskl_rec k (pskl_to_bskl_inh V) (pskl_to_bskl_inh P).
Proof.
  induction P; intros V k; simpl; try reflexivity;
    try (rewrite IHP; reflexivity);
    try (rewrite IHP1, IHP2; reflexivity).
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
Qed.

Lemma pskl_to_bskl_inh_open : forall P X,
    pskl_to_bskl_inh (open_pskl_wrt_pskl P (pskl_var_f X)) =
    open_bskl_wrt_bskl (pskl_to_bskl_inh P) (bskl_var_f X).
Proof.
  intros. unfold open_pskl_wrt_pskl, open_bskl_wrt_bskl.
  apply (pskl_to_bskl_inh_open_rec P (pskl_var_f X) 0).
Qed.

(** [bskl_to_pskl] preserves local closure (both ∀-colours collapse to
    [pskl_all_syn]). *)
Lemma lc_bskl_to_pskl : forall Q,
    lc_bskl Q -> lc_pskl (bskl_to_pskl Q).
Proof.
  intros Q H. induction H; simpl.
  - apply lc_pskl_unit.
  - apply lc_pskl_var_f.
  - apply lc_pskl_arrow; auto.
  - apply lc_pskl_all_syn. intro X. rewrite <- bskl_to_pskl_open. auto.
  - apply lc_pskl_all_syn. intro X. rewrite <- bskl_to_pskl_open. auto.
  - apply lc_pskl_hole.
  - apply lc_pskl_tophole; auto.
Qed.
