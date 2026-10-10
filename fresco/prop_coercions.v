(** Fresco — properties of the paint / erase conversions.

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
    [Require Import src.fresco.prop_coercions] — [Require Import] is NOT
    transitive for name visibility. *)

Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.

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

(** Both routes from a decorated type down to a [pskl] land on the same
    skeleton.  This is what lets the TY sort discharge the leaf presupposition
    by REFLEXIVITY: at that sort there are no ghosts, and consistency preserves
    the erasure ([d_consis_btyp_erase]), so the two sides are already equal. *)
Lemma uskl_to_pskl_utyp_to_uskl : forall C,
  uskl_to_pskl (utyp_to_uskl C) = ptyp_to_pskl (btyp_to_ptyp (utyp_to_btyp C)).
Proof. induction C; simpl; f_equal; auto. Qed.

Lemma bskl_to_pskl_btyp_to_bskl : forall B,
  bskl_to_pskl (btyp_to_bskl B) = ptyp_to_pskl (btyp_to_ptyp B).
Proof. induction B; simpl; f_equal; auto. Qed.

(** A synthesised [btyp] is the syn-painting of its own forgetful image, so
    [d_consis_compose]'s [ptyp_to_btyp_syn A] middle can be fed an arbitrary
    [is_styp] btyp via [A := btyp_to_ptyp B]. *)
Lemma ptyp_to_utyp_syn_btyp_to_ptyp : forall B,
    ptyp_to_utyp_syn (btyp_to_ptyp B) = btyp_to_utyp_syn B.
Proof.
  induction B; simpl; try reflexivity;
    try (rewrite IHB1, IHB2; reflexivity); rewrite IHB; reflexivity.
Qed.

(** Paint round-trip: erasing a syn-painted [btyp] to a [utyp] equals the
    direct utyp painting (structural). *)
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

(** ⭐ Both erasures commute with substitution. *)
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

(** The CLOSE twin of the two above. *)
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

(** The two ways of painting a [ptyp] into the unresolved SKELETON sort agree:
    through [utyp] (what [d_sub] uses) and through [pskl]/[bskl] (what
    [ad_pat_sub] uses, i.e. [ptyp_to_uskl_syn]). *)
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

(** Erasure commutes with opening (converse direction of
    [pskl_to_uskl_open_rec] above). *)
Lemma uskl_to_pskl_open_rec : forall R0 R' k,
  uskl_to_pskl (open_uskl_wrt_uskl_rec k R' R0)
  = open_pskl_wrt_pskl_rec k (uskl_to_pskl R') (uskl_to_pskl R0).
Proof.
  induction R0; intros; simpl; f_equal; auto.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity.
Qed.

(** Erasure commutes with variable-opening. *)
Lemma uskl_to_pskl_open : forall R α,
  uskl_to_pskl (open_uskl_wrt_uskl R (uskl_var_f α))
  = open_pskl_wrt_pskl (uskl_to_pskl R) (pskl_var_f α).
Proof.
  intros. unfold open_uskl_wrt_uskl, open_pskl_wrt_pskl.
  rewrite uskl_to_pskl_open_rec. reflexivity.
Qed.

(** [strip ψ := pskl_to_uskl ⌊ψ⌋ˢ] commutes with opening. *)
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

(** [utyp_to_btyp] commutes with opening. *)
Lemma utyp_to_btyp_open_rec : forall C1 C2 k,
    utyp_to_btyp (open_utyp_wrt_utyp_rec k C2 C1) =
    open_btyp_wrt_btyp_rec k (utyp_to_btyp C2) (utyp_to_btyp C1).
Proof.
  induction C1; intros C2 k; simpl; try reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[|]|]; reflexivity.
  - rewrite IHC1_1, IHC1_2; reflexivity.
  - rewrite IHC1; reflexivity.
  - rewrite IHC1; reflexivity.
Qed.

Lemma utyp_to_btyp_open : forall C1 C2,
    utyp_to_btyp (open_utyp_wrt_utyp C1 C2) =
    open_btyp_wrt_btyp (utyp_to_btyp C1) (utyp_to_btyp C2).
Proof.
  intros. unfold open_utyp_wrt_utyp, open_btyp_wrt_btyp.
  apply utyp_to_btyp_open_rec.
Qed.

(** Erase ([btyp_to_utyp_syn ∘ utyp_to_btyp]) commutes with [open] on a
    variable. *)
Lemma btyp_to_utyp_syn_utyp_to_btyp_open_var : forall C α,
    btyp_to_utyp_syn (utyp_to_btyp (open_utyp_wrt_utyp C (utyp_var_f α)))
    = open_utyp_wrt_utyp (btyp_to_utyp_syn (utyp_to_btyp C)) (utyp_var_f α).
Proof.
  intros C α. rewrite utyp_to_btyp_open. simpl.
  rewrite btyp_to_utyp_syn_open. reflexivity.
Qed.

(** Substitution commutes with every coercion — each is structural, so it
    commutes with substitution when the substituted term is coerced too.
    ⚙ Moved here 2026-10-10 from algo/prop_suffix_erase.v §2;
    [ptyp_to_pskl_subst] also replaces this file's own reversed copy,
    [subst_ptyp_to_pskl_comm]. *)

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

(** Commutation with the [α := 1] substitution — what the [_subst_unit]
    strengthening lemmas of decl/ rewrite with: every conversion sends [unit]
    to the [unit] of its target sort.  Instances of the general commutations
    just above. *)
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

(** * 3. Transport of local closure and of the shape predicates.

    Every one of these is the same one-line induction whose ∀ case rewrites
    with the matching [_open] lemma from §2 — which is why the two sections
    belong in one file.

    ⚠️ [Set Implicit Arguments] is SCOPED TO THIS SECTION, and it is
    load-bearing.  Each lemma here has the shape [forall x, Pred x -> Pred' (f
    x)], whose subject is STRICTLY implicit — and most of these lemmas came
    from files that do set the flag ([algo/prop_basic.v],
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
  - apply lc_pskl_ghost.
  - apply lc_pskl_univ_ghost; auto.
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
  - apply lc_bskl_ghost.
  - apply lc_bskl_univ_ghost; auto.
Qed.

(** The painting of a type is locally closed as a skeleton. *)
Lemma ptyp_to_pskl_lc : forall A, lc_ptyp A -> lc_pskl (ptyp_to_pskl A).
Proof.
  intros A H; induction H; cbn; try solve [ constructor; auto ].
  (* ∀ : the cofinite family transports through the coercion *)
  apply lc_pskl_all_syn. intros α.
  rewrite <- ptyp_to_pskl_open. auto.
Qed.

(** ⭐ THE CONVERSE (2026-08-18).  [ptyp_to_pskl] is a CONSTRUCTOR
    RELABELLING, so local closure comes BACK through it — which is what a
    typing runner needs: its rules pin a subtyping premise's counterpart to
    [⌈A⌉], and what the caller owes is [lc_ptyp A].

    ⚠️ Neither induction on [A] nor on the [lc_pskl] derivation works
    directly: the [∀] row's IH would be about [A]'s body while the goal is
    about its OPENING, and [lc_pskl]'s index is the image, so inverting it
    never exposes [A]'s own constructor.  Go through [degree], which is
    indexed by the binder depth and therefore structural. *)
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

(** …and for a monotype it needs no ∀ case at all. *)
Lemma mono_ptyp_to_pskl_lc : forall τ, mono_ptyp τ -> lc_pskl (ptyp_to_pskl τ).
Proof. induction 1; simpl; auto using lc_pskl. Qed.

(** The syn painting of an lc skeleton is synthesised. *)
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
Lemma is_dskl_lc : forall ψ, is_dskl ψ -> lc_uskl ψ.
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

Lemma is_dskl_utyp_to_uskl : forall C, is_dtyp C -> is_dskl (utyp_to_uskl C).
Proof.
  intros C H; induction H; simpl; try solve [ constructor; auto ].
  apply is_dskl__all_tag with (L := L). intros α Hα.
  rewrite <- utyp_to_uskl_open_var. auto.
Qed.

(** Reflection of local closure / guardedness through the erasure. *)
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

(** The inh-painting of a (locally-closed) [ptyp] is fully inherited. *)
Lemma is_ityp_ptyp_to_btyp_inh : forall A, lc_ptyp A -> is_ityp (ptyp_to_btyp_inh A).
Proof.
  intros A H. induction H; simpl.
  - apply is_ityp__unit.
  - apply is_ityp__var.
  - apply is_ityp__arrow; assumption.
  - apply is_ityp__all with (L := empty). intros α _.
    change (btyp_var_f α) with (ptyp_to_btyp_inh (ptyp_var_f α)).
    rewrite <- ptyp_to_btyp_inh_open.
    match goal with Hb : forall _, is_ityp _ |- _ => apply Hb end.
Qed.

(** ⭐ A MONOTYPE HAS ONE COLOURING, so a single [τ] serves every sort at
    once: the inherited painting of the substituted variable is the
    synthesised one, which is what lets the [inh] and [syn] rows of the
    same derivation be substituted with the same object. *)
Lemma ptyp_to_btyp_inh_mono_syn : forall τ,
  mono_ptyp τ -> ptyp_to_btyp_inh τ = ptyp_to_btyp_syn τ.
Proof. intros τ Hm; induction Hm; simpl; congruence. Qed.

Unset Implicit Arguments.

(* ⚙ OUTSIDE the implicit-args region on purpose: its source file
   (algo_decl/prop_conserv.v) sets no such flag, so its call sites pass the
   subject explicitly. *)
Lemma is_styp_of_btyp_to_bskl : forall Q,
  is_sskl Q -> forall B, Q = btyp_to_bskl B -> is_styp B.
Proof.
  intros Q H; induction H; intros B0 HQ;
    destruct B0; simpl in HQ; try discriminate HQ; inversion HQ; subst.
  - apply is_styp__unit.
  - apply is_styp__var.
  - apply is_styp__arrow; [ apply IHis_sskl1 | apply IHis_sskl2 ]; reflexivity.
  - apply is_styp__all with (L := L). intros α Hα.
    apply (H0 α Hα (open_btyp_wrt_btyp B0 (btyp_var_f α))).
    rewrite btyp_to_bskl_open; reflexivity.
Qed.

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

(* ⚙ The lemmas between this toggle and the next were stated where implicit
   arguments are on; keep it so their callers' argument lists still fit. *)
Set Implicit Arguments.

Lemma lc_ptyp_to_btyp_syn : forall A, lc_ptyp A -> lc_btyp (ptyp_to_btyp_syn A).
Proof.
  intros A H. induction H; simpl.
  - constructor.
  - constructor.
  - constructor; assumption.
  - pick fresh α. apply (lc_btyp_all_syn_exists α).
    specialize (H0 α). rewrite ptyp_to_btyp_syn_open in H0. simpl in H0. exact H0.
Qed.

Lemma lc_ptyp_to_btyp_inh : forall A, lc_ptyp A -> lc_btyp (ptyp_to_btyp_inh A).
Proof.
  intros A H. induction H; simpl.
  - constructor.
  - constructor.
  - constructor; assumption.
  - pick fresh α. apply (lc_btyp_all_inh_exists α).
    specialize (H0 α). unfold open_btyp_wrt_btyp.
    unfold open_ptyp_wrt_ptyp in H0.
    rewrite ptyp_to_btyp_inh_open_rec in H0. simpl in H0. exact H0.
Qed.

Lemma lc_ptyp_to_utyp_syn : forall A, lc_ptyp A -> lc_utyp (ptyp_to_utyp_syn A).
Proof.
  intros A H. induction H; simpl.
  - constructor.
  - constructor.
  - constructor; assumption.
  - pick fresh α. apply (lc_utyp_all_syn_exists α).
    specialize (H0 α). rewrite ptyp_to_utyp_syn_open in H0. simpl in H0. exact H0.
Qed.

(** Reverse paint-lc: a locally-closed syn-painting comes from a
    locally-closed source.  Induction on the [lc_utyp] derivation. *)
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

(** Erasure preserves local closure. *)
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

(** …and back: erasure preserves STRUCTURE, so it reflects local closure
    too — needed where a rule states its domain as a [btyp] but its
    well-formedness as the erasure's ([d_sd_typing__abs_anno]). *)
Lemma lc_btyp_of_lc_ptyp_erase : forall B,
    lc_ptyp (btyp_to_ptyp B) -> lc_btyp B.
Proof.
  intros B H. apply lc_btyp_of_degree, degree_btyp_of_degree_ptyp_erase,
    degree_ptyp_wrt_ptyp_of_lc_ptyp, H.
Qed.

(** [utyp_to_btyp] preserves local closure (needed for the btyp-side
    subst/open commute in the substitution lemma). *)
Lemma lc_utyp_to_btyp : forall C, lc_utyp C -> lc_btyp (utyp_to_btyp C).
Proof.
  intros C H. induction H; simpl.
  - apply lc_btyp_unit.
  - apply lc_btyp_var_f.
  - apply lc_btyp_arrow; assumption.
  - apply lc_btyp_all_syn. intros α.
    change (btyp_var_f α) with (utyp_to_btyp (utyp_var_f α)).
    rewrite <- utyp_to_btyp_open. apply H0.
  - apply lc_btyp_all_syn. intros α.
    change (btyp_var_f α) with (utyp_to_btyp (utyp_var_f α)).
    rewrite <- utyp_to_btyp_open. apply H0.
Qed.

(** A [utyp]'s [btyp] erasure has only synthesised foralls, so it is [is_styp]
    once locally closed (lc rules out a dangling [var_b]). *)
Lemma is_styp_utyp_to_btyp : forall C,
    lc_utyp C -> is_styp (utyp_to_btyp C).
Proof.
  intros C Hlc. induction Hlc; simpl.
  - apply is_styp__unit.
  - apply is_styp__var.
  - apply is_styp__arrow; assumption.
  - apply is_styp__all with (L := empty). intros α Hα.
    replace (open_btyp_wrt_btyp (utyp_to_btyp C) (btyp_var_f α))
      with (utyp_to_btyp (open_utyp_wrt_utyp C (utyp_var_f α)))
      by (rewrite utyp_to_btyp_open; reflexivity).
    apply H0.
  - apply is_styp__all with (L := empty). intros α Hα.
    replace (open_btyp_wrt_btyp (utyp_to_btyp C) (btyp_var_f α))
      with (utyp_to_btyp (open_utyp_wrt_utyp C (utyp_var_f α)))
      by (rewrite utyp_to_btyp_open; reflexivity).
    apply H0.
Qed.

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
  intros C H; destruct C; simpl in H; inversion H; subst.
  - apply guarded_utyp__unit.
  - apply guarded_utyp__var.
  - apply guarded_utyp__arrow;
      [ apply (lc_utyp_of_lc_uskl_incl (utyp_to_uskl C1));
          [ assumption | reflexivity ]
      | apply (lc_utyp_of_lc_uskl_incl (utyp_to_uskl C2));
          [ assumption | reflexivity ] ].
Qed.

Lemma lc_pskl_of_lc_btyp : forall B,
  lc_btyp B -> lc_pskl (bskl_to_pskl (btyp_to_bskl B)).
Proof.
  intros B H; induction H; simpl;
    try solve [ constructor; assumption ].
  - apply lc_pskl_all_syn. intro α.
    rewrite <- bskl_to_pskl_open.
    change (bskl_var_f α) with (btyp_to_bskl (btyp_var_f α)).
    rewrite <- btyp_to_bskl_open. auto.
  - apply lc_pskl_all_syn. intro α.
    rewrite <- bskl_to_pskl_open.
    change (bskl_var_f α) with (btyp_to_bskl (btyp_var_f α)).
    rewrite <- btyp_to_bskl_open. auto.
Qed.

(** * 4. Transport of free variables.

    Every conversion is structural and renames nothing, so it preserves the
    free-variable set EXACTLY.  Each fact is stated once, in the strongest
    relation it holds in — Leibniz [=] where the two sets are the same term,
    setoid [ [=] ] where the [pskl] side reassociates a union.  A [ [<=] ]
    consumer rewrites with these rather than re-proving the weakening — one
    fact must not acquire a second name here. *)

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

(** A TYPE has no ghosts, so its skeleton view is ghost-free. *)
Lemma ptyp_to_pskl_no_ghost : forall A, pskl_no_ghost (ptyp_to_pskl A).
Proof. induction A; simpl; tauto. Qed.

Lemma ftvar_ptyp_to_pskl : forall A,
  ftvar_in_pskl (ptyp_to_pskl A) [=] ftvar_in_ptyp A.
Proof. induction A; simpl; fsetdec. Qed.

Lemma ftvar_bskl_to_pskl : forall Q,
  ftvar_in_pskl (bskl_to_pskl Q) [=] ftvar_in_bskl Q.
Proof. induction Q; simpl; fsetdec. Qed.

(** Coercions never introduce free type variables. *)
Lemma ftvar_btyp_to_utyp_syn : forall B,
    ftvar_in_utyp (btyp_to_utyp_syn B) = ftvar_in_btyp B.
Proof. induction B; simpl; congruence. Qed.

Lemma ftvar_utyp_to_btyp : forall C,
    ftvar_in_btyp (utyp_to_btyp C) = ftvar_in_utyp C.
Proof. induction C; simpl; congruence. Qed.

Lemma ftvar_pskl_to_bskl_syn : forall P,
    ftvar_in_bskl (pskl_to_bskl_syn P) = ftvar_in_pskl P.
Proof.
  induction P; simpl; try reflexivity;
    try (rewrite IHP1, IHP2; reflexivity); try (rewrite IHP; reflexivity).
Qed.

(* [btyp_to_bskl] / [bskl_to_uskl] preserve free tvars (only repaint). *)
Lemma ftvar_btyp_to_bskl : forall B,
    ftvar_in_bskl (btyp_to_bskl B) = ftvar_in_btyp B.
Proof.
  induction B; simpl; try reflexivity;
    try (rewrite IHB1, IHB2; reflexivity); try (rewrite IHB; reflexivity).
Qed.

(* ⚙ The lemmas between this toggle and the next were stated where implicit
   arguments are on; keep it so their callers' argument lists still fit. *)
Set Implicit Arguments.

(** ** Retractions up to colour — the binder cases need the free-variable
    facts above. *)

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

(** A fully-inherited [btyp] is the inh-painting of its own erasure: re-painting
    every (already-inh) quantifier returns the same type.  Needed by the
    [forall_r] case of the abstraction-tail subsumption lemmas, where the result
    [btyp_all_inh B] (with [is_ityp B]) must be matched against the painted
    result [btyp_all_inh (ptyp_to_btyp_inh A)] forced by [d_typing__forall]. *)
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

(** An INHERITED [btyp] paints as an inherited [pskl]: every ∀ it has is
    [btyp_all_inh], and [pskl_to_bskl_inh] paints every ∀ that way. *)
Lemma inh_paint_bskl : forall B,
  is_ityp B ->
  btyp_to_bskl B = pskl_to_bskl_inh (bskl_to_pskl (btyp_to_bskl B)).
Proof.
  intros B H; induction H; simpl; try reflexivity.
  - f_equal; assumption.
  - (* ⚙ the ∀ row's binder is the RULE's [A], not the statement's [B] *)
    f_equal.
    pick fresh α for (L `union` ftvar_in_btyp A
                      `union` ftvar_in_bskl
                                (pskl_to_bskl_inh
                                   (bskl_to_pskl (btyp_to_bskl A)))).
    apply open_bskl_wrt_bskl_inj with (α1 := α);
      [ rewrite ftvar_btyp_to_bskl; clear - Fr; fsetdec
      | clear - Fr; fsetdec | ].
    (* push the opening through the two paintings on the RIGHT, then the
       goal IS the cofinite hypothesis *)
    rewrite <- pskl_to_bskl_inh_open, <- bskl_to_pskl_open.
    change (bskl_var_f α) with (btyp_to_bskl (btyp_var_f α)).
    rewrite <- btyp_to_bskl_open.
    exact (H0 α ltac:(clear - Fr; fsetdec)).
Qed.

(* ===================================================================== *)
(*  §5  ε TAGS ACROSS THE CONVERSIONS                                     *)
(*                                                                        *)
(*  A PAINTING invents no tag: [ptyp] / [btyp] have no ε slot at all, so   *)
(*  everything painted out of them is tag-free.  ⚙ Proved here and only   *)
(*  here.  ⚙ [ptyp_to_uskl_syn] is NOT one of these — it is defined only   *)
(*  in algo_decl/def_consis_refine.v, so its tag-freeness lives with the  *)
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

Lemma ptyp_to_pskl_inj : forall A B,
  ptyp_to_pskl A = ptyp_to_pskl B -> A = B.
Proof.
  induction A; destruct B; simpl; intros Heq; try discriminate;
    try reflexivity; injection Heq; intros; f_equal; auto.
Qed.

(** [ptyp_to_pskl] preserves size (it never adds a node).  ⚙ The ONE copy:
    it was proved twice, in consis/prop_completeness_consis.v and in
    ext_algo/def_typing_impl.v, until 2026-10-10. *)
Lemma size_pskl_ptyp_to_pskl : forall A,
  size_pskl (ptyp_to_pskl A) = size_ptyp A.
Proof. induction A; simpl; auto. Qed.

(* ===================================================================== *)
(*  §6  The MONOTYPE EMBEDDINGS, and the stragglers                        *)
(*                                                                        *)
(*  Facts about [ptyp_to_bskl_syn] / [ptyp_to_uskl_syn] (coercions.v) and *)
(*  a few more conversion / local-closure facts.  ⚙ Gathered here         *)
(*  2026-10-10 from algo/prop_basic.v, algo/prop_suffix_erase.v,          *)
(*  algo/prop_mono_bridge.v, algo/prop_pat_sub.v and deco_algo/ — the      *)
(*  embeddings used to be defined in algo_decl/, which is what kept these *)
(*  out.  [Set Implicit Arguments] is scoped to this section, as in the    *)
(*  files they came from.                                                 *)
(* ===================================================================== *)

Set Implicit Arguments.

(** Embedding composition and substitution commutation for the fold step. *)
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

(** Erasure undoes the syn painting of a type.  ⚙ A coercion retraction:
    its home is fresco/prop_coercions.v; it lives here until it moves. *)
Lemma bskl_to_pskl_ptyp_to_bskl_syn : forall A,
  bskl_to_pskl (ptyp_to_bskl_syn A) = ptyp_to_pskl A.
Proof. intros; unfold ptyp_to_bskl_syn; apply bskl_to_pskl_pskl_to_bskl_syn. Qed.

(** On a MONOTYPE the inherited and synthesised paintings coincide — they only
    differ at quantifiers, and a monotype has none. *)
Lemma ptyp_to_bskl_inh_syn_eq : forall A,
  mono_ptyp A ->
  pskl_to_bskl_inh (ptyp_to_pskl A) = ptyp_to_bskl_syn A.
Proof.
  unfold ptyp_to_bskl_syn.
  intros A Hm; induction Hm; simpl; f_equal; auto.
Qed.

(** Free variables of monotype paintings. *)
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

(** The composite coercions, derived. *)
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

(** ⚙ [pskl_to_bskl_inh_subst_mono] — substituting a MONOTYPE into an
    inherited painting is the same substitution as into a synthesised one —
    is already in prop_pat_sub.v, oriented [subst (inh P) = inh (subst P)].
    Used below in that direction.

Note also: *)
Lemma ptyp_to_btyp_inh_subst_mono : forall τ α A,
  mono_ptyp τ ->
  ptyp_to_btyp_inh (subst_ptyp_in_ptyp τ α A)
  = subst_btyp_in_btyp (ptyp_to_btyp_syn τ) α (ptyp_to_btyp_inh A).
Proof.
  intros τ α A Hm.
  rewrite ptyp_to_btyp_inh_subst, (ptyp_to_btyp_inh_mono_syn Hm). reflexivity.
Qed.

(** The syn painting of a monotype determines it. *)
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

(** Erasure of a monotype painting, and of the painting substitution. *)
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
