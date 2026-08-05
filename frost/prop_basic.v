(** Frost — basic syntactic lemmas. Populated as Phase 2 needs them. *)

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.predicates.

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

(** [bskl_to_uskl] preserves local closure (both ∀-colours collapse to
    [uskl_all_syn]). *)
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

(** * Ghost-freeness — the TYPE sub-universe of [pskl] / [bskl].

    [pskl_ghost_free] (frost/predicates.v) is how the algorithmic rules say
    "this position is one of the paper's [A] / [B], not one of its [P] / [Q]".
    The purely syntactic half of its kit lives here, where the RULE
    definitions (algo/def_extra.v) and the proofs that CONSTRUCT them can
    both reach it; the semantic half (fills, decorations) stays in
    algo/prop_pat_sub.v. *)

(** A painting of a [ptyp] has no ghosts — this is the "⇐" of the
    characterisation, and the one every consumer uses: [guess^TY] outputs,
    annotations and [skmod{TY}] inputs are all [⌈A⌉]. *)
Lemma ptyp_to_pskl_ghost_free : forall A, pskl_ghost_free (ptyp_to_pskl A).
Proof. induction A; simpl; auto. Qed.

(** …and conversely, a ghost-free skeleton IS a painted type ("⇒").  Needed
    nowhere in the rules, but it is what justifies calling the predicate a
    SORT rather than a side condition. *)
Lemma pskl_ghost_free_to_ptyp : forall P,
  pskl_ghost_free P -> exists A, P = ptyp_to_pskl A.
Proof.
  induction P; simpl; intros Hg; try contradiction.
  - exists ptyp_unit; reflexivity.
  - exists (ptyp_var_b n); reflexivity.
  - exists (ptyp_var_f α); reflexivity.
  - destruct Hg as [Hg1 Hg2].
    destruct (IHP1 Hg1) as [A1 ->]; destruct (IHP2 Hg2) as [A2 ->].
    exists (ptyp_arrow A1 A2); reflexivity.
  - destruct (IHP Hg) as [A ->]. exists (ptyp_all A); reflexivity.
Qed.

Lemma pskl_ghost_free_open_rec : forall P α' k,
  pskl_ghost_free P ->
  pskl_ghost_free (open_pskl_wrt_pskl_rec k (pskl_var_f α') P).
Proof.
  induction P; intros α' k Hg; simpl in *; intuition.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; auto.
Qed.

Lemma pskl_ghost_free_open : forall P α',
  pskl_ghost_free P ->
  pskl_ghost_free (open_pskl_wrt_pskl P (pskl_var_f α')).
Proof. intros P α' Hg; apply pskl_ghost_free_open_rec; exact Hg. Qed.

(** Opening by an arbitrary GHOST-FREE skeleton — what [Sub-ForallL]'s
    instantiation needs ([guess^TY]'s output is a painted monotype). *)
Lemma pskl_ghost_free_open_rec_gen : forall P P' k,
  pskl_ghost_free P -> pskl_ghost_free P' ->
  pskl_ghost_free (open_pskl_wrt_pskl_rec k P' P).
Proof.
  induction P; intros P' k Hg Hg'; simpl in *; intuition.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; auto.
Qed.

Lemma pskl_ghost_free_open_gen : forall P P',
  pskl_ghost_free P -> pskl_ghost_free P' ->
  pskl_ghost_free (open_pskl_wrt_pskl P P').
Proof. intros P P' Hg Hg'; apply pskl_ghost_free_open_rec_gen; assumption. Qed.

Lemma pskl_ghost_free_close_rec : forall P α k,
  pskl_ghost_free P ->
  pskl_ghost_free (close_pskl_wrt_pskl_rec k α P).
Proof.
  induction P; intros α0 k Hg; simpl in *; try contradiction; auto.
  - destruct (lt_ge_dec n k); simpl; auto.
  - destruct_if; simpl; auto.
  - destruct Hg as [Hg1 Hg2]; split; auto.
Qed.

Lemma pskl_ghost_free_close : forall P α,
  pskl_ghost_free P -> pskl_ghost_free (close_pskl_wrt_pskl α P).
Proof. intros P α Hg; apply pskl_ghost_free_close_rec; exact Hg. Qed.

(** Ghost-freeness survives substitution by anything ghost-free. *)
Lemma pskl_ghost_free_subst : forall P P' β,
  pskl_ghost_free P -> pskl_ghost_free P' ->
  pskl_ghost_free (subst_pskl_in_pskl P' β P).
Proof.
  induction P; intros P' β Hg Hg'; simpl in *; intuition.
  destruct_if; simpl; auto.
Qed.

Lemma pskl_ghost_free_subst_var : forall P α β,
  pskl_ghost_free P ->
  pskl_ghost_free (subst_pskl_in_pskl (pskl_var_f α) β P).
Proof. intros P α β Hg; apply pskl_ghost_free_subst; [ exact Hg | exact I ]. Qed.

(** …in particular by a monotype painting. *)
Lemma pskl_ghost_free_subst_mono : forall P τ β,
  pskl_ghost_free P -> mono_ptyp τ ->
  pskl_ghost_free (subst_pskl_in_pskl (ptyp_to_pskl τ) β P).
Proof.
  intros P τ β Hg _; apply pskl_ghost_free_subst;
    [ exact Hg | apply ptyp_to_pskl_ghost_free ].
Qed.

Lemma bskl_ghost_free_open_rec : forall Q α' k,
  bskl_ghost_free Q ->
  bskl_ghost_free (open_bskl_wrt_bskl_rec k (bskl_var_f α') Q).
Proof.
  induction Q; intros α' k Hg; simpl in *; intuition.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; auto.
Qed.

Lemma pskl_to_bskl_inh_ghost_free : forall P,
  pskl_ghost_free P ->
  bskl_ghost_free (pskl_to_bskl_inh P).
Proof. induction P; simpl; intuition. Qed.

(** The workhorse for discharging a rule's SORT premise.  Every algorithmic
    type position is reached from another one by opening, closing, renaming or
    instantiating with a [guess^TY] output, so the closure kit above is
    complete for them; the final [simpl; intuition] handles the concrete
    skeletons of the test/counterexample files. *)
Ltac ghost_free_auto :=
  solve [ assumption
        | apply ptyp_to_pskl_ghost_free
        | (apply pskl_ghost_free_subst_var; ghost_free_auto)
        | (apply pskl_ghost_free_open; ghost_free_auto)
        | (apply pskl_ghost_free_close; ghost_free_auto)
        | (apply pskl_ghost_free_subst; ghost_free_auto)
        | (simpl; intuition) ].

(** The INVERSE of [pskl_ghost_free_open_rec]: opening a body cannot destroy
    a ghost either, so the sort of a ∀-body is read off any of its instances.
    This is what turns the cofinite [uskl_ghost_free] into the [Fixpoint]
    [pskl_ghost_free] across an erasure. *)
Lemma pskl_ghost_free_open_rec_inv : forall P P' k,
  pskl_ghost_free (open_pskl_wrt_pskl_rec k P' P) ->
  pskl_ghost_free P.
Proof.
  induction P; intros P' k Hg; simpl in *; auto.
  - destruct Hg as [Hg1 Hg2]; split; eauto.
  - eauto.
Qed.
