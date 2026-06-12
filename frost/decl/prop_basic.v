(** Frost — basic syntactic lemmas for the current split syntax. *)

Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.

Set Implicit Arguments.

(** * list_disjoint algebra. *)

Lemma list_disjoint_sym : forall (xs ys : list atom),
    list_disjoint xs ys -> list_disjoint ys xs.
Proof.
  unfold list_disjoint. intros xs ys H a Hy Hx.
  apply (H a); auto.
Qed.

Lemma list_disjoint_nil_l : forall (ys : list atom),
    list_disjoint nil ys.
Proof.
  intros ys a Hy. inversion Hy.
Qed.

Lemma list_disjoint_nil_r : forall (xs : list atom),
    list_disjoint xs nil.
Proof.
  intros xs a _ Hy. inversion Hy.
Qed.

Lemma list_disjoint_cons_l_inv : forall (a : atom) (xs ys : list atom),
    list_disjoint (a :: xs) ys ->
    ~ List.In a ys /\ list_disjoint xs ys.
Proof.
  intros a xs ys H. split.
  - intro Hin. apply (H a); [left; reflexivity | exact Hin].
  - intros b Hb Hin. apply (H b); [right; exact Hb | exact Hin].
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

Lemma list_disjoint_app_l_iff : forall (xs1 xs2 ys : list atom),
    list_disjoint (xs1 ++ xs2) ys <->
    list_disjoint xs1 ys /\ list_disjoint xs2 ys.
Proof.
  unfold list_disjoint. intros xs1 xs2 ys. split.
  - intros H. split; intros a Ha Hin; apply (H a); auto using in_or_app.
  - intros [H1 H2] a Hin Hy. apply in_app_or in Hin. destruct Hin.
    + apply (H1 a); auto.
    + apply (H2 a); auto.
Qed.

Lemma list_disjoint_app_r_iff : forall (xs ys1 ys2 : list atom),
    list_disjoint xs (ys1 ++ ys2) <->
    list_disjoint xs ys1 /\ list_disjoint xs ys2.
Proof.
  intros xs ys1 ys2. split.
  - intros H. apply list_disjoint_sym in H.
    apply list_disjoint_app_l_iff in H as [H1 H2].
    split; apply list_disjoint_sym; auto.
  - intros [H1 H2]. apply list_disjoint_sym.
    apply list_disjoint_app_l_iff. split; apply list_disjoint_sym; auto.
Qed.

Lemma list_disjoint_singleton_l : forall (a : atom) (ys : list atom),
    ~ List.In a ys ->
    list_disjoint (a :: nil) ys.
Proof.
  intros a ys Hni. apply list_disjoint_cons_l; auto using list_disjoint_nil_l.
Qed.

Lemma list_disjoint_singleton_r : forall (xs : list atom) (a : atom),
    ~ List.In a xs ->
    list_disjoint xs (a :: nil).
Proof.
  intros xs a Hni. apply list_disjoint_sym, list_disjoint_singleton_l, Hni.
Qed.

Lemma list_disjoint_perm_l : forall (xs xs' ys : list atom),
    Permutation xs xs' ->
    list_disjoint xs ys ->
    list_disjoint xs' ys.
Proof.
  intros xs xs' ys Hperm Hdis a Hin Hy.
  apply (Hdis a); auto.
  apply Permutation_sym in Hperm.
  eapply Permutation_in; eauto.
Qed.

Lemma list_disjoint_perm_r : forall (xs ys ys' : list atom),
    Permutation ys ys' ->
    list_disjoint xs ys ->
    list_disjoint xs ys'.
Proof.
  intros xs ys ys' Hperm Hdis.
  apply list_disjoint_sym.
  eapply list_disjoint_perm_l; eauto.
  apply list_disjoint_sym; auto.
Qed.

(** * Local closure for shape predicates. *)

Lemma mono_ptyp_lc : forall A, mono_ptyp A -> lc_ptyp A.
Proof.
  intros A H. induction H; constructor; auto.
Qed.

Lemma mono_btyp_lc : forall B, mono_btyp B -> lc_btyp B.
Proof.
  intros B H. induction H; constructor; auto.
Qed.

Lemma mono_utyp_lc : forall C, mono_utyp C -> lc_utyp C.
Proof.
  intros C H. induction H; constructor; auto.
Qed.

Lemma is_styp_lc : forall B, is_styp B -> lc_btyp B.
Proof.
  intros B H. induction H; eauto.
Qed.

Lemma is_ityp_lc : forall B, is_ityp B -> lc_btyp B.
Proof.
  intros B H. induction H; eauto.
Qed.

Lemma is_ttyp_lc : forall C, is_ttyp C -> lc_utyp C.
Proof.
  intros C H. induction H; eauto.
Qed.

Lemma is_sskl_lc : forall Q, is_sskl Q -> lc_bskl Q.
Proof.
  intros Q H. induction H; eauto.
Qed.

Lemma is_iskl_lc : forall Q, is_iskl Q -> lc_bskl Q.
Proof.
  intros Q H. induction H; eauto.
Qed.

Lemma is_tskl_lc : forall R, is_tskl R -> lc_uskl R.
Proof.
  intros R H. induction H; eauto.
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

Lemma is_ityp_is_inh : forall B, is_ityp B -> is_inh B.
Proof.
  intros B H. induction H.
  - constructor.
  - constructor.
  - constructor; auto.
  - apply is_inh__all with (L := L); auto.
Qed.

Lemma is_ttyp_is_ttyp_utyp : forall C, is_ttyp C -> is_ttyp_utyp C.
Proof.
  intros C H. induction H.
  - constructor.
  - constructor.
  - constructor; auto.
  - apply is_ttyp_utyp__all with (L := L); auto.
Qed.

Lemma is_sskl_is_syn_bskl : forall Q, is_sskl Q -> is_syn_bskl Q.
Proof.
  intros Q H. induction H.
  - constructor.
  - constructor.
  - constructor; auto.
  - apply is_syn_bskl__all with (L := L); auto.
  - constructor.
  - constructor; auto.
Qed.

(** * Coercion local-closure preservation. *)

Lemma ptyp_to_btyp_syn_lc : forall A,
    lc_ptyp A -> lc_btyp (ptyp_to_btyp_syn A).
Proof.
  intros A H. induction H; simpl.
  - apply lc_btyp_unit.
  - apply lc_btyp_var_f.
  - apply lc_btyp_arrow; assumption.
  - apply lc_btyp_all_syn. intros X.
    change (btyp_var_f X) with (ptyp_to_btyp_syn (ptyp_var_f X)).
    rewrite <- ptyp_to_btyp_syn_open.
    match goal with Hb : forall _, lc_btyp _ |- _ => apply Hb end.
Qed.

Lemma ptyp_to_btyp_inh_lc : forall A,
    lc_ptyp A -> lc_btyp (ptyp_to_btyp_inh A).
Proof.
  intros A H. induction H; simpl.
  - apply lc_btyp_unit.
  - apply lc_btyp_var_f.
  - apply lc_btyp_arrow; assumption.
  - apply lc_btyp_all_inh. intros X.
    change (btyp_var_f X) with (ptyp_to_btyp_inh (ptyp_var_f X)).
    rewrite <- ptyp_to_btyp_inh_open.
    match goal with Hb : forall _, lc_btyp _ |- _ => apply Hb end.
Qed.

Lemma ptyp_to_utyp_syn_lc : forall A,
    lc_ptyp A -> lc_utyp (ptyp_to_utyp_syn A).
Proof.
  intros A H. induction H; simpl.
  - apply lc_utyp_unit.
  - apply lc_utyp_var_f.
  - apply lc_utyp_arrow; assumption.
  - apply lc_utyp_all_syn. intros X.
    change (utyp_var_f X) with (ptyp_to_utyp_syn (ptyp_var_f X)).
    rewrite <- ptyp_to_utyp_syn_open.
    match goal with Hb : forall _, lc_utyp _ |- _ => apply Hb end.
Qed.

(** * Mutual induction principle for typing/pattern inference. *)

Scheme d_typing_mut := Induction for d_typing Sort Prop
  with d_pat_mut    := Induction for d_pat    Sort Prop.
