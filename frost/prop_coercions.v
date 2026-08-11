(** Frost — properties of the paint / erase conversions.

    [coercions.v] DEFINES the maps between the six sorts ([ptyp] [btyp] [utyp]
    [pskl] [bskl] [uskl]); this file proves everything ABOUT them, and it is
    the only place any of it should live:

    | § | what |
    |---|---|
    | 1 | retractions — [erase ∘ paint = id] |
    | 2 | commutation with [open] / [open_rec] |
    | 3 | transport of local closure and of the shape predicates |
    | 4 | transport of free variables |

    ⚠️ THIS IS THE ONLY HOME FOR THEM — do not re-prove one downstream.  Two
    copies of a conversion fact under one name is a correctness hazard, not
    untidiness: which copy an unqualified [apply] resolves to then depends on
    import order.

    ⚙ Only the STRONGEST form of each fact is kept, and the weaker ones are
    left to follow at the use site — a Leibniz [=] gives both [ [=] ] and
    [ [<=] ] by [rewrite].

    ⚙ [prop_basic.v] re-exports this file, so the ~99 consumers that already
    import it need no change.  A file that imports [coercions.v] alone must
    [Require Import src.frost.prop_coercions] — [Require Import] is NOT
    transitive for name visibility. *)

Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.def_extra.

(** * 1. Retractions.

    Painting a colourless thing and erasing the colour again is the identity.
    (The other direction is NOT an identity — erasing forgets which colour was
    there — so these are retractions, not isomorphisms.) *)

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

(** Erasure is a retraction of the embedding. *)
Lemma uskl_to_pskl_pskl_to_uskl : forall P,
  uskl_to_pskl (pskl_to_uskl P) = P.
Proof. induction P; simpl; f_equal; auto. Qed.

(** * 2. Commutation with opening.

    Every conversion is a structural map that leaves bound indices alone, so
    it commutes with [open_rec] at every level.  The [_open] form is the [k=0]
    specialisation and is what the cofinite binder rules actually rewrite
    with.  Grouped by source sort, in the order [coercions.v] defines them. *)

(** ** btyp -> utyp *)

Lemma btyp_to_utyp_syn_open_rec : forall B1 B2 k,
    btyp_to_utyp_syn (open_btyp_wrt_btyp_rec k B2 B1) =
    open_utyp_wrt_utyp_rec k (btyp_to_utyp_syn B2) (btyp_to_utyp_syn B1).
Proof.
  induction B1; intros B2 k; simpl; try reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[|]|]; reflexivity.
  - rewrite IHB1_1. rewrite IHB1_2. reflexivity.
  - rewrite IHB1. reflexivity.
  - rewrite IHB1. reflexivity.
Qed.

Lemma btyp_to_utyp_syn_open : forall B1 B2,
    btyp_to_utyp_syn (open_btyp_wrt_btyp B1 B2) =
    open_utyp_wrt_utyp (btyp_to_utyp_syn B1) (btyp_to_utyp_syn B2).
Proof.
  intros B1 B2.
  unfold open_btyp_wrt_btyp, open_utyp_wrt_utyp.
  apply btyp_to_utyp_syn_open_rec.
Qed.

(** ** ptyp -> btyp, both colours *)

Lemma ptyp_to_btyp_syn_open_rec : forall A1 A2 k,
    ptyp_to_btyp_syn (open_ptyp_wrt_ptyp_rec k A2 A1) =
    open_btyp_wrt_btyp_rec k (ptyp_to_btyp_syn A2) (ptyp_to_btyp_syn A1).
Proof.
  induction A1; intros A2 k; simpl; try reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[|]|]; reflexivity.
  - rewrite IHA1_1. rewrite IHA1_2. reflexivity.
  - rewrite IHA1. reflexivity.
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
  induction A1; intros A2 k; simpl; try reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[|]|]; reflexivity.
  - rewrite IHA1_1. rewrite IHA1_2. reflexivity.
  - rewrite IHA1. reflexivity.
Qed.

Lemma ptyp_to_btyp_inh_open : forall A1 A2,
    ptyp_to_btyp_inh (open_ptyp_wrt_ptyp A1 A2) =
    open_btyp_wrt_btyp (ptyp_to_btyp_inh A1) (ptyp_to_btyp_inh A2).
Proof.
  intros A1 A2.
  unfold open_ptyp_wrt_ptyp, open_btyp_wrt_btyp.
  apply ptyp_to_btyp_inh_open_rec.
Qed.

(** ⚠️ The VARIABLE instance is a separate lemma, not a convenience.  The
    general form does NOT subsume it for [rewrite <-]: matching is syntactic,
    so unifying the pattern's [ptyp_to_btyp_inh ?A2] against a bare
    [btyp_var_f α] in the goal would need the fixpoint unfolded, and [rewrite]
    will not do that.  ⚙ Derived from the general form rather than re-proved —
    [ptyp_to_btyp_inh (ptyp_var_f α)] IS [btyp_var_f α] by computation, so the
    two statements differ only up to conversion, which [exact] accepts. *)
Lemma ptyp_to_btyp_inh_open_var : forall A α,
    ptyp_to_btyp_inh (open_ptyp_wrt_ptyp A (ptyp_var_f α)) =
    open_btyp_wrt_btyp (ptyp_to_btyp_inh A) (btyp_var_f α).
Proof. intros A α. exact (ptyp_to_btyp_inh_open A (ptyp_var_f α)). Qed.

Lemma ptyp_to_btyp_syn_open_var : forall A α,
    ptyp_to_btyp_syn (open_ptyp_wrt_ptyp A (ptyp_var_f α)) =
    open_btyp_wrt_btyp (ptyp_to_btyp_syn A) (btyp_var_f α).
Proof. intros A α. exact (ptyp_to_btyp_syn_open A (ptyp_var_f α)). Qed.

(** ** btyp -> ptyp *)

Lemma btyp_to_ptyp_open_rec : forall B1 B2 k,
    btyp_to_ptyp (open_btyp_wrt_btyp_rec k B2 B1) =
    open_ptyp_wrt_ptyp_rec k (btyp_to_ptyp B2) (btyp_to_ptyp B1).
Proof.
  induction B1; intros B2 k; simpl; try reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[|]|]; reflexivity.
  - rewrite IHB1_1, IHB1_2; reflexivity.
  - rewrite IHB1; reflexivity.
  - rewrite IHB1; reflexivity.
Qed.

Lemma btyp_to_ptyp_open : forall B1 B2,
    btyp_to_ptyp (open_btyp_wrt_btyp B1 B2) =
    open_ptyp_wrt_ptyp (btyp_to_ptyp B1) (btyp_to_ptyp B2).
Proof.
  intros. unfold open_btyp_wrt_btyp, open_ptyp_wrt_ptyp.
  apply btyp_to_ptyp_open_rec.
Qed.

(** The variable instance — see [ptyp_to_btyp_inh_open_var] for why the general
    form does not subsume it. *)
Lemma btyp_to_ptyp_open_var : forall B α,
    btyp_to_ptyp (open_btyp_wrt_btyp B (btyp_var_f α)) =
    open_ptyp_wrt_ptyp (btyp_to_ptyp B) (ptyp_var_f α).
Proof. intros B α. exact (btyp_to_ptyp_open B (btyp_var_f α)). Qed.

(** ** ptyp -> utyp *)

Lemma ptyp_to_utyp_syn_open_rec : forall A1 A2 k,
    ptyp_to_utyp_syn (open_ptyp_wrt_ptyp_rec k A2 A1) =
    open_utyp_wrt_utyp_rec k (ptyp_to_utyp_syn A2) (ptyp_to_utyp_syn A1).
Proof.
  induction A1; intros A2 k; simpl; try reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[|]|]; reflexivity.
  - rewrite IHA1_1. rewrite IHA1_2. reflexivity.
  - rewrite IHA1. reflexivity.
Qed.

Lemma ptyp_to_utyp_syn_open : forall A1 A2,
    ptyp_to_utyp_syn (open_ptyp_wrt_ptyp A1 A2) =
    open_utyp_wrt_utyp (ptyp_to_utyp_syn A1) (ptyp_to_utyp_syn A2).
Proof.
  intros A1 A2.
  unfold open_ptyp_wrt_ptyp, open_utyp_wrt_utyp.
  apply ptyp_to_utyp_syn_open_rec.
Qed.

(** ** bskl -> pskl *)

Lemma bskl_to_pskl_open_rec : forall Q Q' k,
    bskl_to_pskl (open_bskl_wrt_bskl_rec k Q' Q) =
    open_pskl_wrt_pskl_rec k (bskl_to_pskl Q') (bskl_to_pskl Q).
Proof.
  induction Q; intros Q' k; simpl; try reflexivity;
    try (rewrite IHQ; reflexivity);
    try (rewrite IHQ1, IHQ2; reflexivity).
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
Qed.

(** ⭐ Both erasures commute with substitution.  ⚙ [uskl_to_pskl_subst] used to
    live in deco_algo/prop_decorate_sub.v §4; it moved here 2026-08-11 with
    its conversion (one fact, one name, one file — CLAUDE.md), because
    decl/def_extra.v now needs the erasure for the paper's presupposition on
    skeleton consistency and is upstream of that file. *)
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

(** ** ptyp -> pskl *)

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

(** ** pskl -> bskl, both colours *)

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

(** ** bskl -> uskl (both ∀-colours collapse to [uskl_all_syn]) *)

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

(** ** utyp <-> uskl (the sort inclusion) *)

Lemma utyp_to_uskl_open_rec : forall C1 C2 k,
    utyp_to_uskl (open_utyp_wrt_utyp_rec k C2 C1) =
    open_uskl_wrt_uskl_rec k (utyp_to_uskl C2) (utyp_to_uskl C1).
Proof.
  induction C1; intros C2 k; simpl; try reflexivity;
    try (rewrite IHC1; reflexivity);
    try (rewrite IHC1_1, IHC1_2; reflexivity).
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
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
  induction R1; intros R2 k; simpl; try reflexivity;
    try (rewrite IHR1; reflexivity);
    try (rewrite IHR1_1, IHR1_2; reflexivity).
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
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

(** [uskl_to_utyp] is a left inverse of the inclusion — so a [uskl] in the
    image determines its [utyp], and the inclusion is injective. *)
Lemma uskl_to_utyp_utyp_to_uskl : forall C, uskl_to_utyp (utyp_to_uskl C) = C.
Proof. induction C; simpl; try reflexivity; congruence. Qed.

Lemma utyp_to_uskl_inj : forall C1 C2,
    utyp_to_uskl C1 = utyp_to_uskl C2 -> C1 = C2.
Proof.
  intros C1 C2 Heq.
  rewrite <- (uskl_to_utyp_utyp_to_uskl C1), <- (uskl_to_utyp_utyp_to_uskl C2).
  rewrite Heq. reflexivity.
Qed.

(** The two ways of painting a [ptyp] into the unresolved SKELETON sort agree:
    through [utyp] (what [d_sub] uses) and through [pskl]/[bskl] (what
    [ad_pat_sub] uses, i.e. [ptyp_to_uskl_syn]). *)
Lemma utyp_to_uskl_ptyp_to_utyp_syn : forall A,
    utyp_to_uskl (ptyp_to_utyp_syn A)
    = bskl_to_uskl (pskl_to_bskl_syn (ptyp_to_pskl A)).
Proof. induction A; simpl; try reflexivity; congruence. Qed.

(** Erasing the inclusion's result into [btyp] is the ordinary [utyp] erasure. *)
Lemma uskl_to_bskl_utyp_to_uskl : forall C,
    uskl_to_bskl (utyp_to_uskl C) = btyp_to_bskl (utyp_to_btyp C).
Proof. induction C; simpl; try reflexivity; congruence. Qed.

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

(** * 3. Transport of local closure and of the shape predicates.

    Every one of these is the same one-line induction whose ∀ case rewrites
    with the matching [_open] lemma from §2 — which is why the two sections
    belong in one file.

    ⚠️ [Set Implicit Arguments] is SCOPED TO THIS SECTION, and it is
    load-bearing.  Each lemma here has the shape [forall x, Pred x -> Pred' (f
    x)], whose subject is STRICTLY implicit — and most of these lemmas came
    from files that do set the flag ([algo/prop_flex.v],
    [algo/prop_solve_sub.v], [algo/prop_pat_sub.v]).  Without the flag the
    subject becomes explicit here and every call site that applies the lemma to
    its hypothesis directly breaks: [mono_ptyp_to_pskl_lc Hm] reads [Hm] as the
    [ptyp].  §1, §2 and §4 must stay OUTSIDE the region — their arguments occur
    in no later argument's type, so they are explicit in every source file and
    are passed explicitly at call sites ([ftvar_ptyp_to_btyp_syn (btyp_to_ptyp
    B)]).

    ⚙ Same hazard as [algo/prop_swap.v] §6, which sets the flag the other way:
    moving a lemma between an SIA and a non-SIA file silently re-elaborates its
    signature.  Neither `make quick` nor a name-visibility scan catches it —
    only [make coq]. *)

Set Implicit Arguments.

(** A monotype is locally closed.  It sits here rather than in the predicate
    layer because it is the entry point of the transport chain below: every
    [mono_ptyp]-to-[lc] step downstream goes through it. *)
Lemma mono_ptyp_lc : forall A, mono_ptyp A -> lc_ptyp A.
Proof. intros A H; induction H; auto. Qed.

(** [bskl_to_pskl] preserves local closure. *)
Lemma lc_bskl_to_pskl : forall Q,
    lc_bskl Q -> lc_pskl (bskl_to_pskl Q).
Proof.
  intros Q H. induction H; simpl.
  - apply lc_pskl_unit.
  - apply lc_pskl_var_f.
  - apply lc_pskl_arrow; auto.
  - apply lc_pskl_all_syn. intro α. rewrite <- bskl_to_pskl_open. auto.
  - apply lc_pskl_all_syn. intro α. rewrite <- bskl_to_pskl_open. auto.
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
  - apply lc_bskl_all_syn. intro α. rewrite <- pskl_to_bskl_syn_open. auto.
  - apply lc_bskl_hole.
  - apply lc_bskl_tophole; auto.
Qed.

(** [bskl_to_uskl] preserves local closure. *)
Lemma lc_bskl_to_uskl : forall Q,
    lc_bskl Q -> lc_uskl (bskl_to_uskl Q).
Proof.
  intros Q H. induction H; simpl.
  - apply lc_uskl_unit.
  - apply lc_uskl_var_f.
  - apply lc_uskl_arrow; auto.
  - apply lc_uskl_all_syn. intro α. rewrite <- bskl_to_uskl_open. auto.
  - apply lc_uskl_all_syn. intro α. rewrite <- bskl_to_uskl_open. auto.
  - apply lc_uskl_hole.
  - apply lc_uskl_tophole; auto.
Qed.

(** The painting of a type is locally closed as a skeleton. *)
Lemma ptyp_to_pskl_lc : forall A, lc_ptyp A -> lc_pskl (ptyp_to_pskl A).
Proof.
  intros A H; induction H; cbn; try solve [ constructor; auto ].
  (* ∀ : the cofinite family transports through the coercion *)
  apply lc_pskl_all_syn. intros α.
  rewrite <- ptyp_to_pskl_open. auto.
Qed.

(** …and for a monotype it needs no ∀ case at all. *)
Lemma mono_ptyp_to_pskl_lc : forall τ, mono_ptyp τ -> lc_pskl (ptyp_to_pskl τ).
Proof. induction 1; simpl; auto using lc_pskl. Qed.

(** The syn painting of an lc skeleton is synthesised.

    ⚙ It was proved TWICE, in algo/prop_soundness_sub.v and
    algo/sub/look/prop_rho_relation.v, and neither file imports the other — so
    it could not be deduped in place, and was lifted to prop_basic.v on
    2026-08-09 before landing here.  It belongs next to [lc_pskl_to_bskl_syn]:
    same painting, same one-line induction, same [pskl_to_bskl_syn_open]
    step. *)
Lemma is_sskl_pskl_to_bskl_syn : forall P,
    lc_pskl P -> is_sskl (pskl_to_bskl_syn P).
Proof.
  intros P Hlc; induction Hlc; simpl; try solve [ constructor; auto ].
  apply is_sskl__all with (L := {}).
  intros α _. rewrite <- pskl_to_bskl_syn_open. auto.
Qed.

(** A tagged skeleton is locally closed.  ⚙ The ε-tagged ∀ is EXISTS-fresh, so
    unlike its siblings this one picks a witness out of the rule's avoid
    set. *)
Lemma is_tskl_lc : forall ψ, is_tskl ψ -> lc_uskl ψ.
Proof.
  intros ψ H; induction H; try (constructor; auto; fail).
  destruct (atom_fresh L) as [α Hα].
  eapply lc_uskl_all_tag_exists; eauto.
Qed.

(** The sort inclusion preserves local closure and tagged-ness. *)
Lemma lc_utyp_to_uskl : forall C, lc_utyp C -> lc_uskl (utyp_to_uskl C).
Proof.
  intros C H; induction H; simpl.
  - apply lc_uskl_unit.
  - apply lc_uskl_var_f.
  - apply lc_uskl_arrow; auto.
  - apply lc_uskl_all_syn. intro α.
    rewrite <- utyp_to_uskl_open_var. auto.
  - apply lc_uskl_all_tag. intro α.
    rewrite <- utyp_to_uskl_open_var. auto.
Qed.

Lemma is_tskl_utyp_to_uskl : forall C, is_ttyp C -> is_tskl (utyp_to_uskl C).
Proof.
  intros C H; induction H; simpl; try solve [ constructor; auto ].
  apply is_tskl__all_tag with (L := L). intros α Hα.
  rewrite <- utyp_to_uskl_open_var. auto.
Qed.

Unset Implicit Arguments.

(** The sort inclusion [pskl_to_uskl] transports local closure and
    guardedness. *)
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

(** * 4. Transport of free variables.

    Every conversion is structural and renames nothing, so it preserves the
    free-variable set EXACTLY.  Each fact is stated once, in the strongest
    relation it holds in — Leibniz [=] where the two sets are the same term,
    setoid [ [=] ] where the [pskl] side reassociates a union.  A [ [<=] ]
    consumer rewrites with these rather than re-proving the weakening — one
    fact must not acquire a second name here. *)

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

Lemma ftvar_ptyp_to_pskl : forall A,
  ftvar_in_pskl (ptyp_to_pskl A) [=] ftvar_in_ptyp A.
Proof. induction A; simpl; fsetdec. Qed.

Lemma ftvar_bskl_to_pskl : forall Q,
  ftvar_in_pskl (bskl_to_pskl Q) [=] ftvar_in_bskl Q.
Proof. induction Q; simpl; fsetdec. Qed.

Lemma ftvar_utyp_to_uskl : forall C,
  ftvar_in_uskl (utyp_to_uskl C) = ftvar_in_utyp C.
Proof. induction C; simpl; try reflexivity; try (rewrite IHC1, IHC2); auto. Qed.

(** ⚙ [<=] and not [=]: the retraction sends every ghost to [1], so a
    [∀◇]-wrapper's free variables are dropped. *)
Lemma ftvar_uskl_to_utyp : forall R,
  ftvar_in_utyp (uskl_to_utyp R) [<=] ftvar_in_uskl R.
Proof. induction R; simpl; fsetdec. Qed.

(* ===================================================================== *)
(*  §5  ε TAGS ACROSS THE CONVERSIONS                                     *)
(*                                                                        *)
(*  A PAINTING invents no tag: [ptyp] / [btyp] have no ε slot at all, so   *)
(*  everything painted out of them is tag-free.  ⚙ Proved here and only   *)
(*  here.  ⚙ [ptyp_to_uskl_syn] is NOT one of these — it is defined only   *)
(*  in algo_decl/def_decl_algo.v, so its tag-freeness lives with the  *)
(*  rest of its shape facts in algo/prop_pat_sub.v.                        *)
(* ===================================================================== *)

Lemma ftag_btyp_to_utyp_syn : forall B,
  ftag_in_utyp (btyp_to_utyp_syn B) [=] empty.
Proof. induction B; simpl; fsetdec. Qed.

Lemma ftag_bskl_to_uskl : forall Q,
  ftag_in_uskl (bskl_to_uskl Q) [=] empty.
Proof. induction Q; simpl; fsetdec. Qed.

(** The SORT INCLUSION, by contrast, keeps every tag — which is how the
    conservativity bridge carries [ForallL]'s hygiene across the sorts. *)
Lemma ftag_utyp_to_uskl : forall C,
  ftag_in_uskl (utyp_to_uskl C) [=] ftag_in_utyp C.
Proof. induction C; simpl; fsetdec. Qed.
