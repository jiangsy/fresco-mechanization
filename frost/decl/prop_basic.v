(** Frost — basic syntactic lemmas (Phase 2.A foundation). *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.decl.def_extra.

Set Implicit Arguments.

(** * list_disjoint algebra. *)

(** Symmetry. *)
Lemma list_disjoint_sym : forall (xs ys : list atom),
    list_disjoint xs ys -> list_disjoint ys xs.
Proof.
  unfold list_disjoint. intros xs ys H a Hy Hx.
  apply (H a); auto.
Qed.

(** Empty on the left. *)
Lemma list_disjoint_nil_l : forall (ys : list atom),
    list_disjoint nil ys.
Proof.
  intros ys a Hy. inversion Hy.
Qed.

(** Empty on the right. *)
Lemma list_disjoint_nil_r : forall (xs : list atom),
    list_disjoint xs nil.
Proof.
  intros xs a _ Hy. inversion Hy.
Qed.

(** Cons-left split. *)
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

(** Append-left distribution. *)
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

(** Append-right distribution (via symmetry). *)
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

(** If two lists are disjoint, removing an element preserves disjointness. *)
Lemma list_disjoint_remove_l : forall (a : atom) (xs ys : list atom),
    list_disjoint xs ys ->
    list_disjoint (List.remove eq_dec a xs) ys.
Proof.
  intros a xs ys H b Hb Hy.
  apply in_remove in Hb as [Hb _]. apply (H b); auto.
Qed.

(** Singleton disjointness. *)
Lemma list_disjoint_singleton_l : forall (a : atom) (ys : list atom),
    ~ List.In a ys ->
    list_disjoint (a :: nil) ys.
Proof.
  intros a ys Hni. apply list_disjoint_cons_l; auto using list_disjoint_nil_l.
Qed.

Lemma list_disjoint_singleton_r : forall (xs : list atom) (a : atom) ,
    ~ List.In a xs ->
    list_disjoint xs (a :: nil).
Proof.
  intros xs a Hni. apply list_disjoint_sym, list_disjoint_singleton_l, Hni.
Qed.
