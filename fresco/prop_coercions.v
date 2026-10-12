Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.

Lemma bskl_to_pskl_pskl_to_bskl_syn : forall P,
    bskl_to_pskl (pskl_to_bskl_syn P) = P.
Proof.
  induction P; simpl; congruence.
Qed.

Lemma bskl_to_pskl_pskl_to_bskl_inh : forall P,
    bskl_to_pskl (pskl_to_bskl_inh P) = P.
Proof.
  induction P; simpl; congruence.
Qed.

Lemma btyp_to_ptyp_ptyp_to_btyp_syn : forall A,
    btyp_to_ptyp (ptyp_to_btyp_syn A) = A.
Proof.
  induction A; simpl; congruence.
Qed.

Lemma btyp_to_ptyp_ptyp_to_btyp_inh : forall A,
    btyp_to_ptyp (ptyp_to_btyp_inh A) = A.
Proof.
  induction A; simpl; congruence.
Qed.

Lemma uskl_to_pskl_pskl_to_uskl : forall P,
  uskl_to_pskl (pskl_to_uskl P) = P.
Proof. induction P; simpl; f_equal; auto. Qed.

Lemma uskl_to_pskl_utyp_to_uskl : forall C,
  uskl_to_pskl (utyp_to_uskl C) = ptyp_to_pskl (btyp_to_ptyp (utyp_to_btyp C)).
Proof. induction C; simpl; f_equal; auto. Qed.

Lemma bskl_to_pskl_btyp_to_bskl : forall B,
  bskl_to_pskl (btyp_to_bskl B) = ptyp_to_pskl (btyp_to_ptyp B).
Proof. induction B; simpl; f_equal; auto. Qed.

Lemma ptyp_to_utyp_syn_btyp_to_ptyp : forall B,
    ptyp_to_utyp_syn (btyp_to_ptyp B) = btyp_to_utyp_syn B.
Proof.
  induction B; simpl; congruence.
Qed.

Lemma btyp_to_utyp_syn_ptyp_to_btyp_syn : forall A,
    btyp_to_utyp_syn (ptyp_to_btyp_syn A) = ptyp_to_utyp_syn A.
Proof.
  induction A; simpl; try reflexivity.
  - rewrite IHA1, IHA2. reflexivity.
  - rewrite IHA. reflexivity.
Qed.

Lemma utyp_to_btyp_ptyp_to_utyp_syn : forall A,
    utyp_to_btyp (ptyp_to_utyp_syn A) = ptyp_to_btyp_syn A.
Proof. induction A; simpl; congruence. Qed.

Lemma btyp_to_utyp_syn_open_rec : forall B1 B2 k,
    btyp_to_utyp_syn (open_btyp_wrt_btyp_rec k B2 B1) =
    open_utyp_wrt_utyp_rec k (btyp_to_utyp_syn B2) (btyp_to_utyp_syn B1).
Proof.
  induction B1; intros B2 k; simpl; try solve [f_equal; auto 2].
  destruct (lt_eq_lt_dec n k) as [[|]|]; reflexivity.
Qed.

Lemma btyp_to_utyp_syn_open : forall B1 B2,
    btyp_to_utyp_syn (open_btyp_wrt_btyp B1 B2) =
    open_utyp_wrt_utyp (btyp_to_utyp_syn B1) (btyp_to_utyp_syn B2).
Proof.
  intros B1 B2.
  unfold open_btyp_wrt_btyp, open_utyp_wrt_utyp.
  apply btyp_to_utyp_syn_open_rec.
Qed.

Lemma ptyp_to_btyp_syn_open_rec : forall A1 A2 k,
    ptyp_to_btyp_syn (open_ptyp_wrt_ptyp_rec k A2 A1) =
    open_btyp_wrt_btyp_rec k (ptyp_to_btyp_syn A2) (ptyp_to_btyp_syn A1).
Proof.
  induction A1; intros A2 k; simpl; try solve [f_equal; auto 2].
  destruct (lt_eq_lt_dec n k) as [[|]|]; reflexivity.
Qed.

Lemma ptyp_to_btyp_syn_open : forall A1 A2,
    ptyp_to_btyp_syn (open_ptyp_wrt_ptyp A1 A2) =
    open_btyp_wrt_btyp (ptyp_to_btyp_syn A1) (ptyp_to_btyp_syn A2).
Proof.
  intros A1 A2.
  unfold open_ptyp_wrt_ptyp, open_btyp_wrt_btyp.
  apply ptyp_to_btyp_syn_open_rec.
Qed.

Lemma ptyp_to_btyp_inh_open_rec : forall A1 A2 k,
    ptyp_to_btyp_inh (open_ptyp_wrt_ptyp_rec k A2 A1) =
    open_btyp_wrt_btyp_rec k (ptyp_to_btyp_inh A2) (ptyp_to_btyp_inh A1).
Proof.
  induction A1; intros A2 k; simpl; try solve [f_equal; auto 2].
  destruct (lt_eq_lt_dec n k) as [[|]|]; reflexivity.
Qed.

Lemma ptyp_to_btyp_inh_open : forall A1 A2,
    ptyp_to_btyp_inh (open_ptyp_wrt_ptyp A1 A2) =
    open_btyp_wrt_btyp (ptyp_to_btyp_inh A1) (ptyp_to_btyp_inh A2).
Proof.
  intros A1 A2.
  unfold open_ptyp_wrt_ptyp, open_btyp_wrt_btyp.
  apply ptyp_to_btyp_inh_open_rec.
Qed.

Lemma ptyp_to_btyp_inh_open_var : forall A α,
    ptyp_to_btyp_inh (open_ptyp_wrt_ptyp A (ptyp_var_f α)) =
    open_btyp_wrt_btyp (ptyp_to_btyp_inh A) (btyp_var_f α).
Proof. intros A α. exact (ptyp_to_btyp_inh_open A (ptyp_var_f α)). Qed.

Lemma ptyp_to_btyp_syn_open_var : forall A α,
    ptyp_to_btyp_syn (open_ptyp_wrt_ptyp A (ptyp_var_f α)) =
    open_btyp_wrt_btyp (ptyp_to_btyp_syn A) (btyp_var_f α).
Proof. intros A α. exact (ptyp_to_btyp_syn_open A (ptyp_var_f α)). Qed.

Lemma btyp_to_ptyp_open_rec : forall B1 B2 k,
    btyp_to_ptyp (open_btyp_wrt_btyp_rec k B2 B1) =
    open_ptyp_wrt_ptyp_rec k (btyp_to_ptyp B2) (btyp_to_ptyp B1).
Proof.
  induction B1; intros B2 k; simpl; try solve [f_equal; auto 2].
  destruct (lt_eq_lt_dec n k) as [[|]|]; reflexivity.
Qed.

Lemma btyp_to_ptyp_open : forall B1 B2,
    btyp_to_ptyp (open_btyp_wrt_btyp B1 B2) =
    open_ptyp_wrt_ptyp (btyp_to_ptyp B1) (btyp_to_ptyp B2).
Proof.
  intros. unfold open_btyp_wrt_btyp, open_ptyp_wrt_ptyp.
  apply btyp_to_ptyp_open_rec.
Qed.

Lemma btyp_to_ptyp_open_var : forall B α,
    btyp_to_ptyp (open_btyp_wrt_btyp B (btyp_var_f α)) =
    open_ptyp_wrt_ptyp (btyp_to_ptyp B) (ptyp_var_f α).
Proof. intros B α. exact (btyp_to_ptyp_open B (btyp_var_f α)). Qed.

Lemma ptyp_to_utyp_syn_open_rec : forall A1 A2 k,
    ptyp_to_utyp_syn (open_ptyp_wrt_ptyp_rec k A2 A1) =
    open_utyp_wrt_utyp_rec k (ptyp_to_utyp_syn A2) (ptyp_to_utyp_syn A1).
Proof.
  induction A1; intros A2 k; simpl; try solve [f_equal; auto 2].
  destruct (lt_eq_lt_dec n k) as [[|]|]; reflexivity.
Qed.

Lemma ptyp_to_utyp_syn_open : forall A1 A2,
    ptyp_to_utyp_syn (open_ptyp_wrt_ptyp A1 A2) =
    open_utyp_wrt_utyp (ptyp_to_utyp_syn A1) (ptyp_to_utyp_syn A2).
Proof.
  intros A1 A2.
  unfold open_ptyp_wrt_ptyp, open_utyp_wrt_utyp.
  apply ptyp_to_utyp_syn_open_rec.
Qed.

Lemma bskl_to_pskl_open_rec : forall Q Q' k,
    bskl_to_pskl (open_bskl_wrt_bskl_rec k Q' Q) =
    open_pskl_wrt_pskl_rec k (bskl_to_pskl Q') (bskl_to_pskl Q).
Proof.
  induction Q; intros Q' k; simpl; try solve [f_equal; auto 2].
  destruct (lt_eq_lt_dec n k) as [[|]|]; reflexivity.
Qed.

Lemma uskl_to_pskl_subst : forall R Rg β,
  uskl_to_pskl (subst_uskl_in_uskl Rg β R)
  = subst_pskl_in_pskl (uskl_to_pskl Rg) β (uskl_to_pskl R).
Proof.
  induction R; intros Rg β; simpl; try (f_equal; auto; fail).
  destruct_if; reflexivity.
Qed.

Lemma bskl_to_pskl_subst : forall Q Qg β,
  bskl_to_pskl (subst_bskl_in_bskl Qg β Q)
  = subst_pskl_in_pskl (bskl_to_pskl Qg) β (bskl_to_pskl Q).
Proof.
  induction Q; intros Qg β; simpl; try (f_equal; auto; fail).
  destruct_if; reflexivity.
Qed.

Lemma bskl_to_pskl_open : forall Q α,
    bskl_to_pskl (open_bskl_wrt_bskl Q (bskl_var_f α)) =
    open_pskl_wrt_pskl (bskl_to_pskl Q) (pskl_var_f α).
Proof.
  intros. unfold open_bskl_wrt_bskl, open_pskl_wrt_pskl.
  apply (bskl_to_pskl_open_rec Q (bskl_var_f α) 0).
Qed.

Lemma ptyp_to_pskl_open_rec : forall A A' k,
    ptyp_to_pskl (open_ptyp_wrt_ptyp_rec k A' A) =
    open_pskl_wrt_pskl_rec k (ptyp_to_pskl A') (ptyp_to_pskl A).
Proof.
  induction A; intros A' k; simpl; try solve [f_equal; auto 2].
  destruct (lt_eq_lt_dec n k) as [[|]|]; reflexivity.
Qed.

Lemma ptyp_to_pskl_open : forall A α,
    ptyp_to_pskl (open_ptyp_wrt_ptyp A (ptyp_var_f α)) =
    open_pskl_wrt_pskl (ptyp_to_pskl A) (pskl_var_f α).
Proof.
  intros. unfold open_ptyp_wrt_ptyp, open_pskl_wrt_pskl.
  apply (ptyp_to_pskl_open_rec A (ptyp_var_f α) 0).
Qed.

Lemma ptyp_to_pskl_close_rec : forall A α k,
    ptyp_to_pskl (close_ptyp_wrt_ptyp_rec k α A) =
    close_pskl_wrt_pskl_rec k α (ptyp_to_pskl A).
Proof.
  induction A; intros; simpl; f_equal; auto;
    repeat match goal with
    | |- context [ if ?t then _ else _ ] => destruct t
    | |- context [ lt_ge_dec ?a ?b ] => destruct (lt_ge_dec a b)
    end; reflexivity.
Qed.

Lemma ptyp_to_pskl_close : forall A α,
    ptyp_to_pskl (close_ptyp_wrt_ptyp α A) =
    close_pskl_wrt_pskl α (ptyp_to_pskl A).
Proof.
  intros. unfold close_ptyp_wrt_ptyp, close_pskl_wrt_pskl.
  apply (ptyp_to_pskl_close_rec A α 0).
Qed.

Lemma pskl_to_bskl_inh_open_rec : forall P P' k,
    pskl_to_bskl_inh (open_pskl_wrt_pskl_rec k P' P) =
    open_bskl_wrt_bskl_rec k (pskl_to_bskl_inh P') (pskl_to_bskl_inh P).
Proof.
  induction P; intros P' k; simpl; try solve [f_equal; auto 2].
  destruct (lt_eq_lt_dec n k) as [[|]|]; reflexivity.
Qed.

Lemma pskl_to_bskl_inh_open : forall P α,
    pskl_to_bskl_inh (open_pskl_wrt_pskl P (pskl_var_f α)) =
    open_bskl_wrt_bskl (pskl_to_bskl_inh P) (bskl_var_f α).
Proof.
  intros. unfold open_pskl_wrt_pskl, open_bskl_wrt_bskl.
  apply (pskl_to_bskl_inh_open_rec P (pskl_var_f α) 0).
Qed.

Lemma pskl_to_bskl_syn_open_rec : forall P P' k,
    pskl_to_bskl_syn (open_pskl_wrt_pskl_rec k P' P) =
    open_bskl_wrt_bskl_rec k (pskl_to_bskl_syn P') (pskl_to_bskl_syn P).
Proof.
  induction P; intros P' k; simpl; try solve [f_equal; auto 2].
  destruct (lt_eq_lt_dec n k) as [[|]|]; reflexivity.
Qed.

Lemma pskl_to_bskl_syn_open : forall P α,
    pskl_to_bskl_syn (open_pskl_wrt_pskl P (pskl_var_f α)) =
    open_bskl_wrt_bskl (pskl_to_bskl_syn P) (bskl_var_f α).
Proof.
  intros. unfold open_pskl_wrt_pskl, open_bskl_wrt_bskl.
  apply (pskl_to_bskl_syn_open_rec P (pskl_var_f α) 0).
Qed.

Lemma bskl_to_uskl_open_rec : forall Q Q' k,
    bskl_to_uskl (open_bskl_wrt_bskl_rec k Q' Q) =
    open_uskl_wrt_uskl_rec k (bskl_to_uskl Q') (bskl_to_uskl Q).
Proof.
  induction Q; intros Q' k; simpl; try solve [f_equal; auto 2].
  destruct (lt_eq_lt_dec n k) as [[|]|]; reflexivity.
Qed.

Lemma bskl_to_uskl_open : forall Q α,
    bskl_to_uskl (open_bskl_wrt_bskl Q (bskl_var_f α)) =
    open_uskl_wrt_uskl (bskl_to_uskl Q) (uskl_var_f α).
Proof.
  intros. unfold open_bskl_wrt_bskl, open_uskl_wrt_uskl.
  apply (bskl_to_uskl_open_rec Q (bskl_var_f α) 0).
Qed.

Lemma utyp_to_uskl_open_rec : forall C1 C2 k,
    utyp_to_uskl (open_utyp_wrt_utyp_rec k C2 C1) =
    open_uskl_wrt_uskl_rec k (utyp_to_uskl C2) (utyp_to_uskl C1).
Proof.
  induction C1; intros C2 k; simpl; try solve [f_equal; auto 2].
  destruct (lt_eq_lt_dec n k) as [[|]|]; reflexivity.
Qed.

Lemma utyp_to_uskl_open : forall C1 C2,
    utyp_to_uskl (open_utyp_wrt_utyp C1 C2) =
    open_uskl_wrt_uskl (utyp_to_uskl C1) (utyp_to_uskl C2).
Proof.
  intros. unfold open_utyp_wrt_utyp, open_uskl_wrt_uskl.
  apply utyp_to_uskl_open_rec.
Qed.

Lemma utyp_to_uskl_open_var : forall C α,
    utyp_to_uskl (open_utyp_wrt_utyp C (utyp_var_f α)) =
    open_uskl_wrt_uskl (utyp_to_uskl C) (uskl_var_f α).
Proof. intros C α. exact (utyp_to_uskl_open C (utyp_var_f α)). Qed.

Lemma uskl_to_utyp_open_rec : forall R1 R2 k,
    uskl_to_utyp (open_uskl_wrt_uskl_rec k R2 R1) =
    open_utyp_wrt_utyp_rec k (uskl_to_utyp R2) (uskl_to_utyp R1).
Proof.
  induction R1; intros R2 k; simpl; try solve [f_equal; auto 2].
  destruct (lt_eq_lt_dec n k) as [[|]|]; reflexivity.
Qed.

Lemma uskl_to_utyp_open : forall R1 R2,
    uskl_to_utyp (open_uskl_wrt_uskl R1 R2) =
    open_utyp_wrt_utyp (uskl_to_utyp R1) (uskl_to_utyp R2).
Proof.
  intros. unfold open_utyp_wrt_utyp, open_uskl_wrt_uskl.
  apply uskl_to_utyp_open_rec.
Qed.

Lemma uskl_to_utyp_open_var : forall R α,
    uskl_to_utyp (open_uskl_wrt_uskl R (uskl_var_f α)) =
    open_utyp_wrt_utyp (uskl_to_utyp R) (utyp_var_f α).
Proof. intros R α. exact (uskl_to_utyp_open R (uskl_var_f α)). Qed.

Lemma utyp_to_uskl_ptyp_to_utyp_syn : forall A,
    utyp_to_uskl (ptyp_to_utyp_syn A)
    = bskl_to_uskl (pskl_to_bskl_syn (ptyp_to_pskl A)).
Proof. induction A; simpl; try reflexivity; congruence. Qed.

Lemma pskl_to_uskl_open_rec : forall P P' k,
  pskl_to_uskl (open_pskl_wrt_pskl_rec k P' P)
  = open_uskl_wrt_uskl_rec k (pskl_to_uskl P') (pskl_to_uskl P).
Proof.
  induction P; intros; simpl; f_equal; auto.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity.
Qed.

Lemma pskl_to_uskl_open : forall P Q,
  pskl_to_uskl (open_pskl_wrt_pskl P Q)
  = open_uskl_wrt_uskl (pskl_to_uskl P) (pskl_to_uskl Q).
Proof.
  intros; unfold open_pskl_wrt_pskl, open_uskl_wrt_uskl;
    apply pskl_to_uskl_open_rec.
Qed.

Lemma pskl_to_uskl_open_var : forall P α,
  pskl_to_uskl (open_pskl_wrt_pskl P (pskl_var_f α))
  = open_uskl_wrt_uskl (pskl_to_uskl P) (uskl_var_f α).
Proof. intros; apply pskl_to_uskl_open. Qed.

Lemma uskl_to_pskl_open_rec : forall R0 R' k,
  uskl_to_pskl (open_uskl_wrt_uskl_rec k R' R0)
  = open_pskl_wrt_pskl_rec k (uskl_to_pskl R') (uskl_to_pskl R0).
Proof.
  induction R0; intros; simpl; f_equal; auto.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity.
Qed.

Lemma uskl_to_pskl_open : forall R α,
  uskl_to_pskl (open_uskl_wrt_uskl R (uskl_var_f α))
  = open_pskl_wrt_pskl (uskl_to_pskl R) (pskl_var_f α).
Proof.
  intros. unfold open_uskl_wrt_uskl, open_pskl_wrt_pskl.
  rewrite uskl_to_pskl_open_rec. reflexivity.
Qed.

Lemma strip_uskl_open : forall ψ α,
  pskl_to_uskl (uskl_to_pskl (open_uskl_wrt_uskl ψ (uskl_var_f α)))
  = open_uskl_wrt_uskl (pskl_to_uskl (uskl_to_pskl ψ)) (uskl_var_f α).
Proof.
  intros ψ α. rewrite uskl_to_pskl_open, pskl_to_uskl_open. reflexivity.
Qed.

Lemma btyp_to_bskl_open_rec : forall B B' k,
  btyp_to_bskl (open_btyp_wrt_btyp_rec k B' B)
  = open_bskl_wrt_bskl_rec k (btyp_to_bskl B') (btyp_to_bskl B).
Proof.
  intros B; induction B; intros B' k; default_simp.
Qed.

Lemma btyp_to_bskl_open : forall B B',
  btyp_to_bskl (open_btyp_wrt_btyp B B')
  = open_bskl_wrt_bskl (btyp_to_bskl B) (btyp_to_bskl B').
Proof.
  intros. unfold open_btyp_wrt_btyp, open_bskl_wrt_bskl.
  apply btyp_to_bskl_open_rec.
Qed.

Lemma utyp_to_btyp_open_rec : forall C1 C2 k,
    utyp_to_btyp (open_utyp_wrt_utyp_rec k C2 C1) =
    open_btyp_wrt_btyp_rec k (utyp_to_btyp C2) (utyp_to_btyp C1).
Proof.
  induction C1; intros C2 k; simpl; try solve [f_equal; auto 2].
  destruct (lt_eq_lt_dec n k) as [[|]|]; reflexivity.
Qed.

Lemma utyp_to_btyp_open : forall C1 C2,
    utyp_to_btyp (open_utyp_wrt_utyp C1 C2) =
    open_btyp_wrt_btyp (utyp_to_btyp C1) (utyp_to_btyp C2).
Proof.
  intros. unfold open_utyp_wrt_utyp, open_btyp_wrt_btyp.
  apply utyp_to_btyp_open_rec.
Qed.

Lemma btyp_to_utyp_syn_utyp_to_btyp_open_var : forall C α,
    btyp_to_utyp_syn (utyp_to_btyp (open_utyp_wrt_utyp C (utyp_var_f α)))
    = open_utyp_wrt_utyp (btyp_to_utyp_syn (utyp_to_btyp C)) (utyp_var_f α).
Proof.
  intros C α. rewrite utyp_to_btyp_open. simpl.
  rewrite btyp_to_utyp_syn_open. reflexivity.
Qed.

Lemma ptyp_to_pskl_subst : forall A0 α A,
  ptyp_to_pskl (subst_ptyp_in_ptyp A0 α A)
  = subst_pskl_in_pskl (ptyp_to_pskl A0) α (ptyp_to_pskl A).
Proof.
  intros A0 α A; induction A; simpl; try congruence.
  destruct_if; reflexivity.
Qed.

Lemma pskl_to_bskl_syn_subst : forall P0 α P,
  pskl_to_bskl_syn (subst_pskl_in_pskl P0 α P)
  = subst_bskl_in_bskl (pskl_to_bskl_syn P0) α (pskl_to_bskl_syn P).
Proof.
  intros P0 α P; induction P; simpl; try congruence.
  destruct_if; reflexivity.
Qed.

Lemma pskl_to_bskl_inh_subst : forall P0 α P,
  pskl_to_bskl_inh (subst_pskl_in_pskl P0 α P)
  = subst_bskl_in_bskl (pskl_to_bskl_inh P0) α (pskl_to_bskl_inh P).
Proof.
  intros P0 α P; induction P; simpl; try congruence.
  destruct_if; reflexivity.
Qed.

Lemma bskl_to_uskl_subst : forall Q0 α Q,
  bskl_to_uskl (subst_bskl_in_bskl Q0 α Q)
  = subst_uskl_in_uskl (bskl_to_uskl Q0) α (bskl_to_uskl Q).
Proof.
  intros Q0 α Q; induction Q; simpl; try congruence.
  destruct_if; reflexivity.
Qed.

Lemma btyp_to_bskl_subst : forall B0 α B,
  btyp_to_bskl (subst_btyp_in_btyp B0 α B)
  = subst_bskl_in_bskl (btyp_to_bskl B0) α (btyp_to_bskl B).
Proof.
  intros B0 α B; induction B; simpl; try congruence.
  destruct_if; reflexivity.
Qed.

Lemma btyp_to_ptyp_subst : forall B0 α B,
  btyp_to_ptyp (subst_btyp_in_btyp B0 α B)
  = subst_ptyp_in_ptyp (btyp_to_ptyp B0) α (btyp_to_ptyp B).
Proof.
  intros B0 α B; induction B; simpl; try congruence.
  destruct_if; reflexivity.
Qed.

Lemma ptyp_to_btyp_syn_subst : forall A0 α A,
  ptyp_to_btyp_syn (subst_ptyp_in_ptyp A0 α A)
  = subst_btyp_in_btyp (ptyp_to_btyp_syn A0) α (ptyp_to_btyp_syn A).
Proof.
  intros A0 α A; induction A; simpl; try congruence.
  destruct_if; reflexivity.
Qed.

Lemma ptyp_to_btyp_inh_subst : forall A0 α A,
  ptyp_to_btyp_inh (subst_ptyp_in_ptyp A0 α A)
  = subst_btyp_in_btyp (ptyp_to_btyp_inh A0) α (ptyp_to_btyp_inh A).
Proof.
  intros A0 α A; induction A; simpl; try congruence.
  destruct_if; reflexivity.
Qed.

Lemma pskl_to_bskl_inh_subst_unit : forall P α',
    subst_bskl_in_bskl bskl_unit α' (pskl_to_bskl_inh P)
    = pskl_to_bskl_inh (subst_pskl_in_pskl pskl_unit α' P).
Proof. intros P α'. symmetry. exact (pskl_to_bskl_inh_subst pskl_unit α' P). Qed.

Lemma pskl_to_bskl_syn_subst_unit : forall P α',
    subst_bskl_in_bskl bskl_unit α' (pskl_to_bskl_syn P)
    = pskl_to_bskl_syn (subst_pskl_in_pskl pskl_unit α' P).
Proof. intros P α'. symmetry. exact (pskl_to_bskl_syn_subst pskl_unit α' P). Qed.

Lemma bskl_to_uskl_subst_unit : forall Q α',
    subst_uskl_in_uskl uskl_unit α' (bskl_to_uskl Q)
    = bskl_to_uskl (subst_bskl_in_bskl bskl_unit α' Q).
Proof. intros Q α'. symmetry. exact (bskl_to_uskl_subst bskl_unit α' Q). Qed.

Lemma ptyp_to_pskl_subst_unit : forall A α',
    subst_pskl_in_pskl pskl_unit α' (ptyp_to_pskl A)
    = ptyp_to_pskl (subst_ptyp_in_ptyp ptyp_unit α' A).
Proof. intros A α'. symmetry. exact (ptyp_to_pskl_subst ptyp_unit α' A). Qed.

Lemma ptyp_to_btyp_syn_subst_unit : forall A α',
    subst_btyp_in_btyp btyp_unit α' (ptyp_to_btyp_syn A)
    = ptyp_to_btyp_syn (subst_ptyp_in_ptyp ptyp_unit α' A).
Proof. intros A α'. symmetry. exact (ptyp_to_btyp_syn_subst ptyp_unit α' A). Qed.

Lemma ptyp_to_btyp_inh_subst_unit : forall A α',
    subst_btyp_in_btyp btyp_unit α' (ptyp_to_btyp_inh A)
    = ptyp_to_btyp_inh (subst_ptyp_in_ptyp ptyp_unit α' A).
Proof. intros A α'. symmetry. exact (ptyp_to_btyp_inh_subst ptyp_unit α' A). Qed.

Lemma ptyp_to_utyp_syn_subst_unit : forall A α',
    subst_utyp_in_utyp utyp_unit α' (ptyp_to_utyp_syn A)
    = ptyp_to_utyp_syn (subst_ptyp_in_ptyp ptyp_unit α' A).
Proof.
  induction A; intros α'; simpl; try reflexivity;
    try (rewrite IHA1, IHA2; reflexivity); try (rewrite IHA; reflexivity).
  - destruct_if; reflexivity.
Qed.

Lemma btyp_to_bskl_subst_unit : forall B α',
    subst_bskl_in_bskl bskl_unit α' (btyp_to_bskl B)
    = btyp_to_bskl (subst_btyp_in_btyp btyp_unit α' B).
Proof. intros B α'. symmetry. exact (btyp_to_bskl_subst btyp_unit α' B). Qed.

Lemma btyp_to_ptyp_subst_unit : forall B α',
    subst_ptyp_in_ptyp ptyp_unit α' (btyp_to_ptyp B)
    = btyp_to_ptyp (subst_btyp_in_btyp btyp_unit α' B).
Proof. intros B α'. symmetry. exact (btyp_to_ptyp_subst btyp_unit α' B). Qed.

Lemma uskl_to_pskl_subst_unit : forall R α,
  uskl_to_pskl (subst_uskl_in_uskl uskl_unit α R)
  = subst_pskl_in_pskl pskl_unit α (uskl_to_pskl R).
Proof. intros R α. rewrite uskl_to_pskl_subst. reflexivity. Qed.

Lemma bskl_to_pskl_subst_unit : forall Q α,
  bskl_to_pskl (subst_bskl_in_bskl bskl_unit α Q)
  = subst_pskl_in_pskl pskl_unit α (bskl_to_pskl Q).
Proof. intros Q α. rewrite bskl_to_pskl_subst. reflexivity. Qed.

Set Implicit Arguments.

Lemma mono_ptyp_lc : forall A, mono_ptyp A -> lc_ptyp A.
Proof. intros A H; induction H; auto. Qed.

Lemma lc_bskl_to_pskl : forall Q,
    lc_bskl Q -> lc_pskl (bskl_to_pskl Q).
Proof.
  intros Q H; induction H; simpl; try solve [eauto 3 using lc_pskl].
  all: apply lc_pskl_all_syn; intros α; rewrite <- bskl_to_pskl_open; auto 2.
Qed.

Lemma lc_pskl_to_bskl_syn : forall P,
    lc_pskl P -> lc_bskl (pskl_to_bskl_syn P).
Proof.
  intros P H; induction H; simpl; try solve [eauto 3 using lc_bskl].
  all: apply lc_bskl_all_syn; intros α; rewrite <- pskl_to_bskl_syn_open; auto 2.
Qed.

Lemma ptyp_to_pskl_lc : forall A, lc_ptyp A -> lc_pskl (ptyp_to_pskl A).
Proof.
  intros A H; induction H; cbn; try solve [ constructor; auto ].

  apply lc_pskl_all_syn. intros α.
  rewrite <- ptyp_to_pskl_open. auto.
Qed.

Lemma degree_ptyp_to_pskl_inv : forall A k,
  degree_pskl_wrt_pskl k (ptyp_to_pskl A) -> degree_ptyp_wrt_ptyp k A.
Proof.
  induction A; cbn; intros k H; inversion H; subst;
    solve [ constructor | constructor; auto ].
Qed.

Lemma ptyp_to_pskl_lc_inv : forall A, lc_pskl (ptyp_to_pskl A) -> lc_ptyp A.
Proof.
  intros A H. apply lc_ptyp_of_degree, degree_ptyp_to_pskl_inv,
    degree_pskl_wrt_pskl_of_lc_pskl, H.
Qed.

Lemma mono_ptyp_to_pskl_lc : forall τ, mono_ptyp τ -> lc_pskl (ptyp_to_pskl τ).
Proof. induction 1; simpl; auto using lc_pskl. Qed.

Lemma is_sskl_pskl_to_bskl_syn : forall P,
    lc_pskl P -> is_sskl (pskl_to_bskl_syn P).
Proof.
  intros P Hlc; induction Hlc; simpl; try solve [ constructor; auto ].
  apply is_sskl__all with (L := {}).
  intros α _. rewrite <- pskl_to_bskl_syn_open. auto.
Qed.

Lemma is_dskl_lc : forall ψ, is_dskl ψ -> lc_uskl ψ.
Proof.
  intros ψ H; induction H; try (constructor; auto; fail).
  destruct (atom_fresh L) as [α Hα].
  eapply lc_uskl_all_tag_exists; eauto.
Qed.

Lemma lc_utyp_to_uskl : forall C, lc_utyp C -> lc_uskl (utyp_to_uskl C).
Proof.
  intros C H; induction H; simpl; try solve [eauto 3 using lc_uskl].
  all: constructor; intros α; rewrite <- utyp_to_uskl_open_var; auto 2.
Qed.

Lemma is_dskl_utyp_to_uskl : forall C, is_dtyp C -> is_dskl (utyp_to_uskl C).
Proof.
  intros C H; induction H; simpl; try solve [ constructor; auto ].
  apply is_dskl__all_tag with (L := L). intros α Hα.
  rewrite <- utyp_to_uskl_open_var. auto.
Qed.

Lemma degree_uskl_of_pskl : forall R' k,
  degree_pskl_wrt_pskl k (uskl_to_pskl R') -> degree_uskl_wrt_uskl k R'.
Proof.
  induction R'; intros k Hd; simpl in Hd; inversion Hd; subst;
    constructor; auto.
Qed.

Lemma lc_uskl_to_pskl : forall R, lc_uskl R -> lc_pskl (uskl_to_pskl R).
Proof.
  intros R H; induction H; simpl;
    try (constructor; auto; fail);
    constructor; intros α; rewrite <- uskl_to_pskl_open; auto.
Qed.

Lemma lc_uskl_of_pskl : forall T,
  lc_pskl (uskl_to_pskl T) -> lc_uskl T.
Proof.
  intros T H. apply lc_uskl_of_degree. apply degree_uskl_of_pskl.
  apply degree_pskl_wrt_pskl_of_lc_pskl. exact H.
Qed.

Lemma guarded_pskl_uskl_to_pskl : forall R,
  guarded_uskl R -> guarded_pskl (uskl_to_pskl R).
Proof.
  intros R H; inversion H; simpl; constructor;
    apply lc_uskl_to_pskl; assumption.
Qed.

Lemma guarded_uskl_of_uskl_to_pskl : forall T,
  guarded_pskl (uskl_to_pskl T) -> guarded_uskl T.
Proof.
  destruct T; simpl; intros H; inversion H; subst;
    try (constructor; apply lc_uskl_of_pskl; assumption).
Qed.

Lemma is_ityp_ptyp_to_btyp_inh : forall A, lc_ptyp A -> is_ityp (ptyp_to_btyp_inh A).
Proof.
  intros A H; induction H; simpl; try solve [eauto 3 using is_ityp].
  apply is_ityp__all with (L := empty); intros α _.
  change (btyp_var_f α) with (ptyp_to_btyp_inh (ptyp_var_f α)).
  rewrite <- ptyp_to_btyp_inh_open; auto 2.
Qed.

Lemma ptyp_to_btyp_inh_mono_syn : forall τ,
  mono_ptyp τ -> ptyp_to_btyp_inh τ = ptyp_to_btyp_syn τ.
Proof. intros τ Hm; induction Hm; simpl; congruence. Qed.

Unset Implicit Arguments.

Lemma is_styp_of_btyp_to_bskl : forall Q,
  is_sskl Q -> forall B, Q = btyp_to_bskl B -> is_styp B.
Proof.
  intros Q H; induction H; intros B0 HQ;
    destruct B0; simpl in HQ; try discriminate HQ; inversion HQ; subst;
    try solve [eauto 5 using is_styp].
  apply is_styp__all with (L := L); intros α Hα.
  eapply H0; [ exact Hα | rewrite btyp_to_bskl_open; reflexivity ].
Qed.

Lemma pskl_to_uskl_lc : forall P,
  lc_pskl P -> lc_uskl (pskl_to_uskl P).
Proof.
  intros P H; induction H; simpl; auto.
  apply lc_uskl_all_syn; intros α.
  rewrite <- pskl_to_uskl_open_var; auto.
Qed.

Lemma pskl_to_uskl_guarded : forall P,
  guarded_pskl P -> guarded_uskl (pskl_to_uskl P).
Proof.
  intros P H; inversion H; subst; simpl; constructor; auto using pskl_to_uskl_lc.
Qed.

Set Implicit Arguments.

Lemma lc_ptyp_to_btyp_syn : forall A, lc_ptyp A -> lc_btyp (ptyp_to_btyp_syn A).
Proof.
  intros A H; induction H; simpl; try solve [eauto 3 using lc_btyp].
  all: apply lc_btyp_all_syn; intros α;
    change (btyp_var_f α) with (ptyp_to_btyp_syn (ptyp_var_f α));
    rewrite <- ptyp_to_btyp_syn_open; auto 2.
Qed.

Lemma lc_ptyp_to_btyp_inh : forall A, lc_ptyp A -> lc_btyp (ptyp_to_btyp_inh A).
Proof.
  intros A H; induction H; simpl; try solve [eauto 3 using lc_btyp].
  all: apply lc_btyp_all_inh; intros α;
    change (btyp_var_f α) with (ptyp_to_btyp_inh (ptyp_var_f α));
    rewrite <- ptyp_to_btyp_inh_open; auto 2.
Qed.

Lemma lc_ptyp_to_utyp_syn : forall A, lc_ptyp A -> lc_utyp (ptyp_to_utyp_syn A).
Proof.
  intros A H; induction H; simpl; try solve [eauto 3 using lc_utyp].
  all: apply lc_utyp_all_syn; intros α;
    change (utyp_var_f α) with (ptyp_to_utyp_syn (ptyp_var_f α));
    rewrite <- ptyp_to_utyp_syn_open; auto 2.
Qed.

Lemma lc_ptyp_of_lc_utyp_syn : forall A,
    lc_utyp (ptyp_to_utyp_syn A) -> lc_ptyp A.
Proof.
  intros A Hlc. remember (ptyp_to_utyp_syn A) as C eqn:HC. revert A HC.
  induction Hlc; intros A0 HC; destruct A0; simpl in HC; inversion HC; subst;
    try (constructor; eauto; fail).
  - pick fresh α. apply (lc_ptyp_all_exists α).
    eapply (H0 α (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))).
    rewrite ptyp_to_utyp_syn_open. reflexivity.
Qed.

Lemma degree_ptyp_of_degree_btyp_inh : forall A k,
    degree_btyp_wrt_btyp k (ptyp_to_btyp_inh A) -> degree_ptyp_wrt_ptyp k A.
Proof.
  induction A; intros k H; simpl in H; inversion H; subst; constructor; auto.
Qed.

Lemma lc_ptyp_of_lc_btyp_inh : forall A, lc_btyp (ptyp_to_btyp_inh A) -> lc_ptyp A.
Proof.
  intros A H. apply lc_ptyp_of_degree. apply degree_ptyp_of_degree_btyp_inh.
  apply degree_btyp_wrt_btyp_of_lc_btyp. assumption.
Qed.

Lemma degree_ptyp_of_degree_btyp_syn : forall A k,
    degree_btyp_wrt_btyp k (ptyp_to_btyp_syn A) -> degree_ptyp_wrt_ptyp k A.
Proof.
  induction A; intros k H; simpl in H; inversion H; subst; constructor; auto.
Qed.

Lemma lc_ptyp_of_lc_btyp_syn : forall A, lc_btyp (ptyp_to_btyp_syn A) -> lc_ptyp A.
Proof.
  intros A H. apply lc_ptyp_of_degree. apply degree_ptyp_of_degree_btyp_syn.
  apply degree_btyp_wrt_btyp_of_lc_btyp. assumption.
Qed.

Lemma degree_btyp_of_degree_ptyp_erase : forall B k,
    degree_ptyp_wrt_ptyp k (btyp_to_ptyp B) -> degree_btyp_wrt_btyp k B.
Proof.
  induction B; intros k H; simpl in H; inversion H; subst; constructor; auto.
Qed.

Lemma degree_ptyp_btyp_to_ptyp : forall B k,
    degree_btyp_wrt_btyp k B -> degree_ptyp_wrt_ptyp k (btyp_to_ptyp B).
Proof.
  induction B; intros k H; simpl; inversion H; subst; constructor; auto.
Qed.

Lemma lc_ptyp_btyp_to_ptyp : forall B, lc_btyp B -> lc_ptyp (btyp_to_ptyp B).
Proof.
  intros B H. apply lc_ptyp_of_degree, degree_ptyp_btyp_to_ptyp,
    degree_btyp_wrt_btyp_of_lc_btyp, H.
Qed.

Lemma lc_btyp_of_lc_ptyp_erase : forall B,
    lc_ptyp (btyp_to_ptyp B) -> lc_btyp B.
Proof.
  intros B H. apply lc_btyp_of_degree, degree_btyp_of_degree_ptyp_erase,
    degree_ptyp_wrt_ptyp_of_lc_ptyp, H.
Qed.

Lemma lc_utyp_to_btyp : forall C, lc_utyp C -> lc_btyp (utyp_to_btyp C).
Proof.
  intros C H; induction H; simpl; try solve [eauto 3 using lc_btyp].
  all: apply lc_btyp_all_syn; intros α;
    change (btyp_var_f α) with (utyp_to_btyp (utyp_var_f α));
    rewrite <- utyp_to_btyp_open; auto 2.
Qed.

Lemma is_styp_utyp_to_btyp : forall C,
    lc_utyp C -> is_styp (utyp_to_btyp C).
Proof.
  intros C H; induction H; simpl; try solve [eauto 3 using is_styp].
  all: apply is_styp__all with (L := empty); intros α _;
    change (btyp_var_f α) with (utyp_to_btyp (utyp_var_f α));
    rewrite <- utyp_to_btyp_open; auto 2.
Qed.

Lemma is_styp_ptyp_to_btyp_syn : forall A,
    lc_ptyp A -> is_styp (ptyp_to_btyp_syn A).
Proof.
  intros A H; induction H; simpl; try solve [eauto 3 using is_styp].
  apply is_styp__all with (L := empty); intros α _.
  change (btyp_var_f α) with (ptyp_to_btyp_syn (ptyp_var_f α)).
  rewrite <- ptyp_to_btyp_syn_open; auto 2.
Qed.

Lemma guarded_bskl_to_pskl : forall Q,
    guarded_bskl Q -> guarded_pskl (bskl_to_pskl Q).
Proof.
  intros Q H; destruct H; simpl; eauto 5 using guarded_pskl, lc_bskl_to_pskl.
Qed.

Unset Implicit Arguments.

Lemma lc_utyp_of_lc_uskl_incl : forall R,
  lc_uskl R -> forall C, R = utyp_to_uskl C -> lc_utyp C.
Proof.
  intros R H; induction H; intros C0 HR;
    destruct C0; simpl in HR; try discriminate HR; inversion HR; subst;
    try solve [ constructor ].
  - apply lc_utyp_arrow; [ apply IHlc_uskl1 | apply IHlc_uskl2 ]; reflexivity.
  - apply lc_utyp_all_syn. intros α.
    apply (H0 α (open_utyp_wrt_utyp C0 (utyp_var_f α))).
    symmetry; apply utyp_to_uskl_open_var.
  - apply lc_utyp_all_tag. intros α.
    apply (H0 α (open_utyp_wrt_utyp C0 (utyp_var_f α))).
    symmetry; apply utyp_to_uskl_open_var.
Qed.

Lemma guarded_utyp_of_guarded_uskl_incl : forall C,
  guarded_uskl (utyp_to_uskl C) -> guarded_utyp C.
Proof.
  intros C H; destruct C; simpl in H; inversion H; subst;
    eauto 6 using guarded_utyp, lc_utyp_of_lc_uskl_incl.
Qed.

Lemma lc_pskl_of_lc_btyp : forall B,
  lc_btyp B -> lc_pskl (bskl_to_pskl (btyp_to_bskl B)).
Proof.
  intros B H; induction H; simpl; try solve [eauto 3 using lc_pskl].
  all: apply lc_pskl_all_syn; intros α;
    rewrite <- bskl_to_pskl_open;
    change (bskl_var_f α) with (btyp_to_bskl (btyp_var_f α));
    rewrite <- btyp_to_bskl_open; auto 2.
Qed.

Lemma ftvar_in_uskl_pskl : forall P,
  ftvar_in_uskl (pskl_to_uskl P) [=] ftvar_in_pskl P.
Proof.
  induction P; simpl; try fsetdec.
Qed.

Lemma ftvar_ptyp_to_btyp_syn : forall A,
    ftvar_in_btyp (ptyp_to_btyp_syn A) = ftvar_in_ptyp A.
Proof. induction A; simpl; try reflexivity; try (rewrite IHA1, IHA2); auto. Qed.

Lemma ftvar_ptyp_to_btyp_inh : forall A,
    ftvar_in_btyp (ptyp_to_btyp_inh A) = ftvar_in_ptyp A.
Proof. induction A; simpl; try reflexivity; try (rewrite IHA1, IHA2); auto. Qed.

Lemma ftvar_ptyp_to_utyp_syn : forall A,
    ftvar_in_utyp (ptyp_to_utyp_syn A) = ftvar_in_ptyp A.
Proof. induction A; simpl; try reflexivity; try (rewrite IHA1, IHA2); auto. Qed.

Lemma ftvar_btyp_to_ptyp : forall B,
    ftvar_in_ptyp (btyp_to_ptyp B) = ftvar_in_btyp B.
Proof. induction B; simpl; try reflexivity; try (rewrite IHB1, IHB2); auto. Qed.

Lemma ptyp_to_pskl_no_ghost : forall A, pskl_no_ghost (ptyp_to_pskl A).
Proof. induction A; simpl; tauto. Qed.

Lemma ftvar_ptyp_to_pskl : forall A,
  ftvar_in_pskl (ptyp_to_pskl A) [=] ftvar_in_ptyp A.
Proof. induction A; simpl; fsetdec. Qed.

Lemma ftvar_bskl_to_pskl : forall Q,
  ftvar_in_pskl (bskl_to_pskl Q) [=] ftvar_in_bskl Q.
Proof. induction Q; simpl; fsetdec. Qed.

Lemma ftvar_btyp_to_utyp_syn : forall B,
    ftvar_in_utyp (btyp_to_utyp_syn B) = ftvar_in_btyp B.
Proof. induction B; simpl; congruence. Qed.

Lemma ftvar_utyp_to_btyp : forall C,
    ftvar_in_btyp (utyp_to_btyp C) = ftvar_in_utyp C.
Proof. induction C; simpl; congruence. Qed.

Lemma ftvar_pskl_to_bskl_syn : forall P,
    ftvar_in_bskl (pskl_to_bskl_syn P) = ftvar_in_pskl P.
Proof.
  induction P; simpl; congruence.
Qed.

Lemma ftvar_btyp_to_bskl : forall B,
    ftvar_in_bskl (btyp_to_bskl B) = ftvar_in_btyp B.
Proof.
  induction B; simpl; congruence.
Qed.

Set Implicit Arguments.

Lemma ptyp_to_btyp_syn_btyp_to_ptyp : forall B,
    is_styp B ->
    ptyp_to_btyp_syn (btyp_to_ptyp B) = B.
Proof.
  intros B Hsyn. induction Hsyn; simpl; try reflexivity.
  - rewrite IHHsyn1, IHHsyn2; reflexivity.
  - f_equal.
    pick fresh α for (L `union` ftvar_in_btyp B).
    apply open_btyp_wrt_btyp_inj with (α1 := α).
    + rewrite ftvar_ptyp_to_btyp_syn, ftvar_btyp_to_ptyp. solve_notin_auto.
    + fsetdec.
    + specialize (H0 α ltac:(solve_notin_auto)).
      rewrite btyp_to_ptyp_open in H0.
      rewrite ptyp_to_btyp_syn_open in H0.
      exact H0.
Qed.

Lemma ptyp_to_btyp_inh_btyp_to_ptyp : forall B,
    is_ityp B -> ptyp_to_btyp_inh (btyp_to_ptyp B) = B.
Proof.
  induction 1; simpl; try reflexivity.
  - rewrite IHis_ityp1, IHis_ityp2. reflexivity.
  - f_equal.
    pick fresh α for (L `union` ftvar_in_btyp A).
    apply open_btyp_wrt_btyp_inj with (α1 := α).
    + rewrite ftvar_ptyp_to_btyp_inh, ftvar_btyp_to_ptyp. fsetdec.
    + fsetdec.
    + specialize (H0 α ltac:(solve_notin_auto)).
      unfold open_btyp_wrt_btyp in H0 |- *.
      rewrite btyp_to_ptyp_open_rec, ptyp_to_btyp_inh_open_rec in H0.
      simpl in H0. exact H0.
Qed.

Lemma utyp_to_btyp_btyp_to_utyp_syn : forall B,
    is_styp B -> utyp_to_btyp (btyp_to_utyp_syn B) = B.
Proof.
  intros B Hsyn.
  rewrite <- (ptyp_to_utyp_syn_btyp_to_ptyp B).
  rewrite utyp_to_btyp_ptyp_to_utyp_syn.
  apply ptyp_to_btyp_syn_btyp_to_ptyp; assumption.
Qed.

Unset Implicit Arguments.

Lemma inh_paint_bskl : forall B,
  is_ityp B ->
  btyp_to_bskl B = pskl_to_bskl_inh (bskl_to_pskl (btyp_to_bskl B)).
Proof.
  intros B H; induction H; simpl; try reflexivity.
  - f_equal; assumption.
  -
    f_equal.
    pick fresh α for (L `union` ftvar_in_btyp A
                      `union` ftvar_in_bskl
                                (pskl_to_bskl_inh
                                   (bskl_to_pskl (btyp_to_bskl A)))).
    apply open_bskl_wrt_bskl_inj with (α1 := α);
      [ rewrite ftvar_btyp_to_bskl; clear - Fr; fsetdec
      | clear - Fr; fsetdec | ].
    rewrite <- pskl_to_bskl_inh_open, <- bskl_to_pskl_open.
    change (bskl_var_f α) with (btyp_to_bskl (btyp_var_f α)).
    rewrite <- btyp_to_bskl_open.
    exact (H0 α ltac:(clear - Fr; fsetdec)).
Qed.

Lemma ftag_btyp_to_utyp_syn : forall B,
  ftag_in_utyp (btyp_to_utyp_syn B) [=] empty.
Proof. induction B; simpl; fsetdec. Qed.

Lemma ftag_bskl_to_uskl : forall Q,
  ftag_in_uskl (bskl_to_uskl Q) [=] empty.
Proof. induction Q; simpl; fsetdec. Qed.

Lemma ftag_utyp_to_uskl : forall C,
  ftag_in_uskl (utyp_to_uskl C) [=] ftag_in_utyp C.
Proof. induction C; simpl; fsetdec. Qed.

Lemma ptyp_to_pskl_inj : forall A B,
  ptyp_to_pskl A = ptyp_to_pskl B -> A = B.
Proof.
  induction A; destruct B; simpl; intros Heq; try discriminate;
    try reflexivity; injection Heq; intros; f_equal; auto.
Qed.

Lemma size_pskl_ptyp_to_pskl : forall A,
  size_pskl (ptyp_to_pskl A) = size_ptyp A.
Proof. induction A; simpl; auto. Qed.

Set Implicit Arguments.

Lemma pskl_to_uskl_ptyp : forall A,
  pskl_to_uskl (ptyp_to_pskl A) = ptyp_to_uskl_syn A.
Proof.
  induction A; unfold ptyp_to_uskl_syn in *; simpl; f_equal; auto.
Qed.

Lemma pskl_to_uskl_subst : forall P τ β,
  pskl_to_uskl (subst_pskl_in_pskl (ptyp_to_pskl τ) β P)
  = subst_uskl_in_uskl (ptyp_to_uskl_syn τ) β (pskl_to_uskl P).
Proof.
  induction P; intros; simpl; f_equal; auto.
  destruct (eq_var α β); simpl; auto using pskl_to_uskl_ptyp.
Qed.

Lemma ptyp_to_bskl_syn_open_var : forall A α,
  ptyp_to_bskl_syn (open_ptyp_wrt_ptyp A (ptyp_var_f α))
  = open_bskl_wrt_bskl (ptyp_to_bskl_syn A) (bskl_var_f α).
Proof.
  intros. unfold ptyp_to_bskl_syn, open_ptyp_wrt_ptyp, open_bskl_wrt_bskl.
  rewrite ptyp_to_pskl_open_rec. rewrite pskl_to_bskl_syn_open_rec.
  reflexivity.
Qed.

Lemma bskl_to_pskl_ptyp_to_bskl_syn : forall A,
  bskl_to_pskl (ptyp_to_bskl_syn A) = ptyp_to_pskl A.
Proof. intros; unfold ptyp_to_bskl_syn; apply bskl_to_pskl_pskl_to_bskl_syn. Qed.

Lemma ptyp_to_bskl_inh_syn_eq : forall A,
  mono_ptyp A ->
  pskl_to_bskl_inh (ptyp_to_pskl A) = ptyp_to_bskl_syn A.
Proof.
  unfold ptyp_to_bskl_syn.
  intros A Hm; induction Hm; simpl; f_equal; auto.
Qed.

Lemma ftvar_ptyp_to_uskl_syn : forall τ,
  ftvar_in_uskl (ptyp_to_uskl_syn τ) [=] ftvar_in_ptyp τ.
Proof.
  intros. rewrite <- pskl_to_uskl_ptyp.
  rewrite ftvar_in_uskl_pskl. apply ftvar_ptyp_to_pskl.
Qed.

Lemma ftvar_ptyp_to_bskl_syn : forall τ,
  ftvar_in_bskl (ptyp_to_bskl_syn τ) [=] ftvar_in_ptyp τ.
Proof.
  intros. rewrite <- (ftvar_bskl_to_pskl (ptyp_to_bskl_syn τ)).
  rewrite bskl_to_pskl_ptyp_to_bskl_syn. apply ftvar_ptyp_to_pskl.
Qed.

Lemma ptyp_to_bskl_syn_subst : forall τ α A,
  ptyp_to_bskl_syn (subst_ptyp_in_ptyp τ α A)
  = subst_bskl_in_bskl (ptyp_to_bskl_syn τ) α (ptyp_to_bskl_syn A).
Proof.
  intros. unfold ptyp_to_bskl_syn.
  rewrite ptyp_to_pskl_subst, pskl_to_bskl_syn_subst. reflexivity.
Qed.

Lemma ptyp_to_uskl_syn_subst : forall τ α A,
  ptyp_to_uskl_syn (subst_ptyp_in_ptyp τ α A)
  = subst_uskl_in_uskl (ptyp_to_uskl_syn τ) α (ptyp_to_uskl_syn A).
Proof.
  intros. unfold ptyp_to_uskl_syn.
  rewrite ptyp_to_bskl_syn_subst, bskl_to_uskl_subst. reflexivity.
Qed.

Lemma ptyp_to_btyp_inh_subst_mono : forall τ α A,
  mono_ptyp τ ->
  ptyp_to_btyp_inh (subst_ptyp_in_ptyp τ α A)
  = subst_btyp_in_btyp (ptyp_to_btyp_syn τ) α (ptyp_to_btyp_inh A).
Proof.
  intros τ α A Hm.
  rewrite ptyp_to_btyp_inh_subst, (ptyp_to_btyp_inh_mono_syn Hm). reflexivity.
Qed.

Lemma ptyp_to_bskl_syn_inj : forall A A',
  mono_ptyp A -> mono_ptyp A' ->
  ptyp_to_bskl_syn A = ptyp_to_bskl_syn A' ->
  A = A'.
Proof.
  unfold ptyp_to_bskl_syn.
  intros A A' HmA; revert A'; induction HmA as [ | α | A1 A2 Hm1 IH1 Hm2 IH2 ];
    intros A' HmB Heq; destruct HmB; simpl in Heq; try discriminate.
  - reflexivity.
  - inversion Heq; reflexivity.
  - inversion Heq. f_equal; [ apply IH1 | apply IH2 ]; auto.
Qed.

Lemma uskl_to_pskl_ptyp_to_uskl_syn : forall τ,
  ⌊ ptyp_to_uskl_syn τ ⌋ˢ = ptyp_to_pskl τ.
Proof.
  intros. rewrite <- pskl_to_uskl_ptyp.
  apply uskl_to_pskl_pskl_to_uskl.
Qed.

Lemma uskl_to_pskl_subst_mono : forall R' τ β,
  ⌊ subst_uskl_in_uskl (ptyp_to_uskl_syn τ) β R' ⌋ˢ
  = subst_pskl_in_pskl (ptyp_to_pskl τ) β ⌊ R' ⌋ˢ.
Proof.
  induction R'; intros; simpl; try (f_equal; auto; fail).
  repeat destruct_if; try contradiction;
    [ apply uskl_to_pskl_ptyp_to_uskl_syn | reflexivity ].
Qed.

Lemma pskl_to_uskl_not_tag : forall P ε ψ,
  pskl_to_uskl P <> uskl_all_tag ε ψ.
Proof. destruct P; simpl; discriminate. Qed.

Lemma pskl_to_uskl_not_dot_ghost : forall P,
  pskl_to_uskl P <> uskl_dot_ghost.
Proof. destruct P; simpl; discriminate. Qed.

Lemma pskl_to_uskl_not_dot_univ_ghost : forall P ψ,
  pskl_to_uskl P <> uskl_dot_univ_ghost ψ.
Proof. destruct P; simpl; discriminate. Qed.

Lemma uskl_to_pskl_open_gen : forall R ψg,
  ⌊ open_uskl_wrt_uskl R ψg ⌋ˢ
  = open_pskl_wrt_pskl ⌊ R ⌋ˢ ⌊ ψg ⌋ˢ.
Proof.
  intros. unfold open_uskl_wrt_uskl, open_pskl_wrt_pskl.
  generalize 0. induction R; intros k; simpl; try (f_equal; auto; fail).
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity.
Qed.

Lemma lc_uskl_arrow_inv : forall R R',
  lc_uskl (uskl_arrow R R') -> lc_uskl R /\ lc_uskl R'.
Proof. intros R R' H; inversion H; auto. Qed.

Lemma lc_uskl_univ_ghost_inv : forall R,
  lc_uskl (uskl_univ_ghost R) -> lc_uskl R.
Proof. intros R H; inversion H; auto. Qed.

Lemma lc_uskl_dot_univ_ghost_inv : forall R,
  lc_uskl (uskl_dot_univ_ghost R) -> lc_uskl R.
Proof. intros R H; inversion H; auto. Qed.

Unset Implicit Arguments.

Set Implicit Arguments.

Lemma ptyp_to_uskl_syn_unit_inv : forall τ,
  ptyp_to_uskl_syn τ = uskl_unit -> τ = ptyp_unit.
Proof. intros τ H; destruct τ; simpl in H; try discriminate; reflexivity. Qed.

Lemma ptyp_to_uskl_syn_var_inv : forall τ α,
  ptyp_to_uskl_syn τ = uskl_var_f α -> τ = ptyp_var_f α.
Proof.
  intros τ α H; destruct τ; simpl in H; try discriminate.
  inversion H; reflexivity.
Qed.

Lemma ptyp_to_uskl_syn_arrow_inv : forall τ ψ1 ψ2,
  ptyp_to_uskl_syn τ = uskl_arrow ψ1 ψ2 ->
  exists τ1 τ2, τ = ptyp_arrow τ1 τ2 /\
    ψ1 = ptyp_to_uskl_syn τ1 /\ ψ2 = ptyp_to_uskl_syn τ2.
Proof.
  intros τ ψ1 ψ2 H; destruct τ; simpl in H; try discriminate.
  inversion H; subst. exists τ1, τ2; repeat split; reflexivity.
Qed.

Lemma ptyp_to_uskl_syn_all_tag_absurd : forall τ ε ψ,
  ptyp_to_uskl_syn τ = uskl_all_tag ε ψ -> False.
Proof. intros τ ε ψ H; destruct τ; simpl in H; discriminate. Qed.

Lemma ptyp_to_uskl_syn_dot_univ_ghost_absurd : forall τ ψ,
  ptyp_to_uskl_syn τ = uskl_dot_univ_ghost ψ -> False.
Proof. intros τ ψ H; destruct τ; simpl in H; discriminate. Qed.

Lemma ptyp_to_bskl_syn_unit_inv : forall τ,
  ptyp_to_bskl_syn τ = bskl_unit -> τ = ptyp_unit.
Proof. intros τ H; destruct τ; simpl in H; try discriminate; reflexivity. Qed.

Lemma ptyp_to_bskl_syn_var_inv : forall τ α,
  ptyp_to_bskl_syn τ = bskl_var_f α -> τ = ptyp_var_f α.
Proof.
  intros τ α H; destruct τ; simpl in H; try discriminate.
  inversion H; reflexivity.
Qed.

Lemma ptyp_to_bskl_syn_arrow_inv : forall τ Q1 Q2,
  ptyp_to_bskl_syn τ = bskl_arrow Q1 Q2 ->
  exists τ1 τ2, τ = ptyp_arrow τ1 τ2 /\
    Q1 = ptyp_to_bskl_syn τ1 /\ Q2 = ptyp_to_bskl_syn τ2.
Proof.
  intros τ Q1 Q2 H; destruct τ; simpl in H; try discriminate.
  inversion H; subst. exists τ1, τ2; repeat split; reflexivity.
Qed.

Lemma ptyp_to_bskl_syn_all_inh_absurd : forall τ Q,
  ptyp_to_bskl_syn τ = bskl_all_inh Q -> False.
Proof. intros τ Q H; destruct τ; simpl in H; discriminate. Qed.

Lemma ptyp_to_bskl_syn_all_syn_mono_absurd : forall τ Q,
  mono_ptyp τ ->
  ptyp_to_bskl_syn τ = bskl_all_syn Q -> False.
Proof.
  intros τ Q Hm H; destruct τ; simpl in H; try discriminate.
  inversion Hm.
Qed.

Lemma ptyp_to_bskl_syn_univ_ghost_absurd : forall τ Q,
  ptyp_to_bskl_syn τ = bskl_univ_ghost Q -> False.
Proof. intros τ Q H; destruct τ; simpl in H; discriminate. Qed.

Lemma ptyp_to_bskl_syn_ghost_absurd : forall τ,
  ptyp_to_bskl_syn τ = bskl_ghost -> False.
Proof. intros τ H; destruct τ; simpl in H; discriminate. Qed.
Unset Implicit Arguments.
