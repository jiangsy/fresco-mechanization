(** Frost — basic syntactic lemmas. Populated as Phase 2 needs them. *)

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.

(** * Coercion / opening commutation lemmas. *)

(** [bskl_to_pskl] commutes with (recursive) opening. *)
Lemma bskl_to_pskl_open_rec : forall Q Q' k,
    bskl_to_pskl (open_bskl_wrt_bskl_rec k Q' Q) =
    open_pskl_wrt_pskl_rec k (bskl_to_pskl Q') (bskl_to_pskl Q).
Proof.
  induction Q; intros Q' k; simpl; try reflexivity;
    try (rewrite IHQ; reflexivity);
    try (rewrite IHQ1, IHQ2; reflexivity).
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
Qed.

(** [bskl_to_pskl] commutes with opening by a free variable. *)
Lemma bskl_to_pskl_open : forall Q α,
    bskl_to_pskl (open_bskl_wrt_bskl Q (bskl_var_f α)) =
    open_pskl_wrt_pskl (bskl_to_pskl Q) (pskl_var_f α).
Proof.
  intros. unfold open_bskl_wrt_bskl, open_pskl_wrt_pskl.
  apply (bskl_to_pskl_open_rec Q (bskl_var_f α) 0).
Qed.

(** [bskl_to_pskl] is a left inverse of the synthesised painting. *)
Lemma bskl_to_pskl_pskl_to_bskl_syn : forall P,
    bskl_to_pskl (pskl_to_bskl_syn P) = P.
Proof.
  induction P; simpl; try reflexivity;
    try (rewrite IHP; reflexivity);
    try (rewrite IHP1, IHP2; reflexivity).
Qed.

Lemma bskl_to_pskl_pskl_to_bskl_inh : forall P,
    bskl_to_pskl (pskl_to_bskl_inh P) = P.
Proof.
  induction P; simpl; try reflexivity;
    try (rewrite IHP; reflexivity);
    try (rewrite IHP1, IHP2; reflexivity).
Qed.

(** [btyp_to_ptyp] is a left inverse of the two paintings. *)
Lemma btyp_to_ptyp_ptyp_to_btyp_syn : forall A,
    btyp_to_ptyp (ptyp_to_btyp_syn A) = A.
Proof.
  induction A; simpl; try reflexivity;
    try (rewrite IHA; reflexivity);
    try (rewrite IHA1, IHA2; reflexivity).
Qed.

Lemma btyp_to_ptyp_ptyp_to_btyp_inh : forall A,
    btyp_to_ptyp (ptyp_to_btyp_inh A) = A.
Proof.
  induction A; simpl; try reflexivity;
    try (rewrite IHA; reflexivity);
    try (rewrite IHA1, IHA2; reflexivity).
Qed.

(** [ptyp_to_pskl] commutes with (recursive) opening. *)
Lemma ptyp_to_pskl_open_rec : forall A A' k,
    ptyp_to_pskl (open_ptyp_wrt_ptyp_rec k A' A) =
    open_pskl_wrt_pskl_rec k (ptyp_to_pskl A') (ptyp_to_pskl A).
Proof.
  induction A; intros A' k; simpl; try reflexivity;
    try (rewrite IHA; reflexivity);
    try (rewrite IHA1, IHA2; reflexivity).
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
Qed.

Lemma ptyp_to_pskl_open : forall A α,
    ptyp_to_pskl (open_ptyp_wrt_ptyp A (ptyp_var_f α)) =
    open_pskl_wrt_pskl (ptyp_to_pskl A) (pskl_var_f α).
Proof.
  intros. unfold open_ptyp_wrt_ptyp, open_pskl_wrt_pskl.
  apply (ptyp_to_pskl_open_rec A (ptyp_var_f α) 0).
Qed.

(** [pskl_to_bskl_inh] commutes with (recursive) opening. *)
Lemma pskl_to_bskl_inh_open_rec : forall P P' k,
    pskl_to_bskl_inh (open_pskl_wrt_pskl_rec k P' P) =
    open_bskl_wrt_bskl_rec k (pskl_to_bskl_inh P') (pskl_to_bskl_inh P).
Proof.
  induction P; intros P' k; simpl; try reflexivity;
    try (rewrite IHP; reflexivity);
    try (rewrite IHP1, IHP2; reflexivity).
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
Qed.

Lemma pskl_to_bskl_inh_open : forall P α,
    pskl_to_bskl_inh (open_pskl_wrt_pskl P (pskl_var_f α)) =
    open_bskl_wrt_bskl (pskl_to_bskl_inh P) (bskl_var_f α).
Proof.
  intros. unfold open_pskl_wrt_pskl, open_bskl_wrt_bskl.
  apply (pskl_to_bskl_inh_open_rec P (pskl_var_f α) 0).
Qed.

(** [pskl_to_bskl_syn] commutes with (recursive) opening. *)
Lemma pskl_to_bskl_syn_open_rec : forall P P' k,
    pskl_to_bskl_syn (open_pskl_wrt_pskl_rec k P' P) =
    open_bskl_wrt_bskl_rec k (pskl_to_bskl_syn P') (pskl_to_bskl_syn P).
Proof.
  induction P; intros P' k; simpl; try reflexivity;
    try (rewrite IHP; reflexivity);
    try (rewrite IHP1, IHP2; reflexivity).
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
Qed.

Lemma pskl_to_bskl_syn_open : forall P α,
    pskl_to_bskl_syn (open_pskl_wrt_pskl P (pskl_var_f α)) =
    open_bskl_wrt_bskl (pskl_to_bskl_syn P) (bskl_var_f α).
Proof.
  intros. unfold open_pskl_wrt_pskl, open_bskl_wrt_bskl.
  apply (pskl_to_bskl_syn_open_rec P (pskl_var_f α) 0).
Qed.

(** [bskl_to_uskl] commutes with (recursive) opening (both ∀-colours
    collapse to [uskl_all_syn]). *)
Lemma bskl_to_uskl_open_rec : forall Q Q' k,
    bskl_to_uskl (open_bskl_wrt_bskl_rec k Q' Q) =
    open_uskl_wrt_uskl_rec k (bskl_to_uskl Q') (bskl_to_uskl Q).
Proof.
  induction Q; intros Q' k; simpl; try reflexivity;
    try (rewrite IHQ; reflexivity);
    try (rewrite IHQ1, IHQ2; reflexivity).
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
Qed.

Lemma bskl_to_uskl_open : forall Q α,
    bskl_to_uskl (open_bskl_wrt_bskl Q (bskl_var_f α)) =
    open_uskl_wrt_uskl (bskl_to_uskl Q) (uskl_var_f α).
Proof.
  intros. unfold open_bskl_wrt_bskl, open_uskl_wrt_uskl.
  apply (bskl_to_uskl_open_rec Q (bskl_var_f α) 0).
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

(** The syn-painting preserves local closure. *)
Lemma lc_pskl_to_bskl_syn : forall P,
    lc_pskl P -> lc_bskl (pskl_to_bskl_syn P).
Proof.
  intros P H. induction H; simpl.
  - apply lc_bskl_unit.
  - apply lc_bskl_var_f.
  - apply lc_bskl_arrow; auto.
  - apply lc_bskl_all_syn. intro X. rewrite <- pskl_to_bskl_syn_open. auto.
  - apply lc_bskl_hole.
  - apply lc_bskl_tophole; auto.
Qed.

(** [bskl_to_uskl] preserves local closure (both ∀-colours collapse to
    [uskl_all_syn]). *)
Lemma lc_bskl_to_uskl : forall Q,
    lc_bskl Q -> lc_uskl (bskl_to_uskl Q).
Proof.
  intros Q H. induction H; simpl.
  - apply lc_uskl_unit.
  - apply lc_uskl_var_f.
  - apply lc_uskl_arrow; auto.
  - apply lc_uskl_all_syn. intro X. rewrite <- bskl_to_uskl_open. auto.
  - apply lc_uskl_all_syn. intro X. rewrite <- bskl_to_uskl_open. auto.
  - apply lc_uskl_hole.
  - apply lc_uskl_tophole; auto.
Qed.
