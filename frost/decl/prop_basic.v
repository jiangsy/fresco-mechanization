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

(** * Locally-closed predicates.

    lngen generates [lc_typ] and [lc_exp] in [prop_ln.v]. Verified to cover
    all eight [typ] constructors (incl. four ∀ flavours: [typ_all_col],
    [typ_all_etag], [typ_all_plain], plus [typ_hole] / [typ_tophole]) and
    all seven [exp] constructors. No additions needed here; the lemmas
    [lc_typ_unique], [lc_typ_of_lc_set_*], [lc_typ_all_col_exists],
    [lc_typ_all_etag_exists], [lc_typ_all_plain_exists], etc. are exported
    via the transitive [Require Export prop_ln] in [notations.v]. *)

(** * Substitution composition aliases.

    Paper-friendly names for the three most-used lngen lemmas. These are
    not new theorems; the underlying proofs are lngen-generated. *)

(** [α/X][β/Y] commutes when X ≠ Y and X ∉ FV(β). *)
Definition subst_typ_typ_comm := subst_typ_in_typ_subst_typ_in_typ.

(** Push subst into open. *)
Definition subst_typ_open_typ := subst_typ_in_typ_open_typ_wrt_typ.

(** Pull subst out of var-open (the "intro" direction). *)
Definition subst_typ_intro := subst_typ_in_typ_intro.

(** * Category preservation under substitution.

    For each category predicate P, if [P A] and [P B], then
    [P (subst_typ_in_typ B X A)]. Proved by induction on the
    category-predicate derivation, using lngen's [subst_typ_open_typ]
    for the binder case. *)

(** ** is_typ. *)

Lemma is_typ_lc : forall A, is_typ A -> lc_typ A.
Proof.
  intros A H. induction H.
  - constructor.
  - constructor.
  - constructor; auto.
  - pick fresh X. apply lc_typ_all_col_exists with (X1 := X).
    apply H0. auto.
Qed.

Lemma is_typ_subst : forall A B X,
    is_typ A -> is_typ B -> is_typ (subst_typ_in_typ B X A).
Proof.
  intros A B X HA HB.
  induction HA; simpl.
  - constructor.
  - destruct (X0 == X); subst. exact HB. constructor.
  - constructor; auto.
  - apply is_typ__all with (L := L `union` singleton X).
    intros Y Hni.
    rewrite subst_typ_in_typ_open_typ_wrt_typ_var.
    + apply H0; fsetdec.
    + fsetdec.
    + apply is_typ_lc; exact HB.
Qed.

(** ** is_syn_typ. *)

Lemma is_syn_typ_lc : forall A, is_syn_typ A -> lc_typ A.
Proof.
  intros A H. induction H.
  - constructor.
  - constructor.
  - constructor; auto.
  - pick fresh X. apply lc_typ_all_col_exists with (X1 := X).
    apply H0. auto.
Qed.

Lemma is_syn_typ_subst : forall A B X,
    is_syn_typ A -> is_syn_typ B -> is_syn_typ (subst_typ_in_typ B X A).
Proof.
  intros A B X HA HB. induction HA; simpl.
  - constructor.
  - destruct (X0 == X); subst. exact HB. constructor.
  - constructor; auto.
  - apply is_syn_typ__all with (L := L `union` singleton X).
    intros Y Hni.
    rewrite subst_typ_in_typ_open_typ_wrt_typ_var.
    + apply H0; fsetdec.
    + fsetdec.
    + apply is_syn_typ_lc; exact HB.
Qed.

(** ** is_inh_typ. *)

Lemma is_inh_typ_lc : forall A, is_inh_typ A -> lc_typ A.
Proof.
  intros A H. induction H.
  - constructor.
  - constructor.
  - constructor; auto.
  - pick fresh X. apply lc_typ_all_col_exists with (X1 := X).
    apply H0. auto.
Qed.

Lemma is_inh_typ_subst : forall A B X,
    is_inh_typ A -> is_inh_typ B -> is_inh_typ (subst_typ_in_typ B X A).
Proof.
  intros A B X HA HB. induction HA; simpl.
  - constructor.
  - destruct (X0 == X); subst. exact HB. constructor.
  - constructor; auto.
  - apply is_inh_typ__all with (L := L `union` singleton X).
    intros Y Hni.
    rewrite subst_typ_in_typ_open_typ_wrt_typ_var.
    + apply H0; fsetdec.
    + fsetdec.
    + apply is_inh_typ_lc; exact HB.
Qed.

(** ** is_skel. *)

Lemma is_skel_lc : forall A, is_skel A -> lc_typ A.
Proof.
  intros A H. induction H.
  - constructor.
  - constructor.
  - constructor; auto.
  - pick fresh X. apply lc_typ_all_col_exists with (X1 := X).
    apply H0. auto.
  - constructor.
  - constructor; auto.
Qed.

Lemma is_skel_subst : forall A B X,
    is_skel A -> is_skel B -> is_skel (subst_typ_in_typ B X A).
Proof.
  intros A B X HA HB. induction HA; simpl.
  - constructor.
  - destruct (X0 == X); subst. exact HB. constructor.
  - constructor; auto.
  - apply is_skel__all with (L := L `union` singleton X).
    intros Y Hni.
    rewrite subst_typ_in_typ_open_typ_wrt_typ_var.
    + apply H0; fsetdec.
    + fsetdec.
    + apply is_skel_lc; exact HB.
  - constructor.
  - constructor; auto.
Qed.

(** ** is_ttyp.

    Substituting a typvar X in a tagged type with a replacement B requires
    B itself to be a tagged type — otherwise the result may contain
    non-ε-tagged ∀ structure or holes. *)

Lemma is_ttyp_lc : forall A, is_ttyp A -> lc_typ A.
Proof.
  intros A H. induction H.
  - constructor.
  - constructor.
  - constructor; auto.
  - pick fresh X. apply lc_typ_all_etag_exists with (X1 := X).
    apply H0. auto.
Qed.

Lemma is_ttyp_subst : forall A B X,
    is_ttyp A -> is_ttyp B -> is_ttyp (subst_typ_in_typ B X A).
Proof.
  intros A B X HA HB. induction HA; simpl.
  - constructor.
  - destruct (X0 == X); subst. exact HB. constructor.
  - constructor; auto.
  - apply is_ttyp__all with (L := L `union` singleton X) (ε := ε).
    intros Y Hni.
    rewrite subst_typ_in_typ_open_typ_wrt_typ_var.
    + apply H0; fsetdec.
    + fsetdec.
    + apply is_ttyp_lc; exact HB.
Qed.

(** ** is_utyp.

    Substitution target must be a ttyp (the more restrictive shape), since
    is_utyp permits both ε-tagged and plain ∀ at the head — but only ttyp
    matches the role of an instantiation φ in the paper. *)

Lemma is_utyp_lc : forall A, is_utyp A -> lc_typ A.
Proof.
  intros A H. induction H.
  - constructor.
  - constructor.
  - constructor; auto.
  - pick fresh X. apply lc_typ_all_etag_exists with (X1 := X).
    apply H0. auto.
  - pick fresh X. apply lc_typ_all_plain_exists with (X1 := X).
    apply H0. auto.
Qed.

(** Every is_ttyp is also an is_utyp (utyp's tall constructor accepts
    is_ttyp's all-etag structure). *)
Lemma is_ttyp_is_utyp : forall A, is_ttyp A -> is_utyp A.
Proof.
  intros A H. induction H.
  - constructor.
  - constructor.
  - constructor; auto.
  - apply is_utyp__tall with (L := L) (ε := ε). intros. apply H0; auto.
Qed.

Lemma is_utyp_subst : forall A B X,
    is_utyp A -> is_ttyp B -> is_utyp (subst_typ_in_typ B X A).
Proof.
  intros A B X HA HB. induction HA; simpl.
  - constructor.
  - destruct (X0 == X); subst.
    + apply is_ttyp_is_utyp; exact HB.
    + constructor.
  - constructor; auto.
  - apply is_utyp__tall with (L := L `union` singleton X) (ε := ε).
    intros Y Hni.
    rewrite subst_typ_in_typ_open_typ_wrt_typ_var.
    + apply H0; fsetdec.
    + fsetdec.
    + apply is_ttyp_lc; exact HB.
  - apply is_utyp__pall with (L := L `union` singleton X).
    intros Y Hni.
    rewrite subst_typ_in_typ_open_typ_wrt_typ_var.
    + apply H0; fsetdec.
    + fsetdec.
    + apply is_ttyp_lc; exact HB.
Qed.

(** ** is_tskel. *)

Lemma is_tskel_lc : forall A, is_tskel A -> lc_typ A.
Proof.
  intros A H. induction H.
  - constructor.
  - constructor.
  - constructor; auto.
  - pick fresh X. apply lc_typ_all_etag_exists with (X1 := X).
    apply H0. auto.
  - constructor.
  - constructor; auto.
Qed.

Lemma is_tskel_subst : forall A B X,
    is_tskel A -> is_tskel B -> is_tskel (subst_typ_in_typ B X A).
Proof.
  intros A B X HA HB. induction HA; simpl.
  - constructor.
  - destruct (X0 == X); subst. exact HB. constructor.
  - constructor; auto.
  - apply is_tskel__all with (L := L `union` singleton X) (ε := ε).
    intros Y Hni.
    rewrite subst_typ_in_typ_open_typ_wrt_typ_var.
    + apply H0; fsetdec.
    + fsetdec.
    + apply is_tskel_lc; exact HB.
  - constructor.
  - constructor; auto.
Qed.

(** ** is_uskel. *)

Lemma is_uskel_lc : forall A, is_uskel A -> lc_typ A.
Proof.
  intros A H. induction H.
  - constructor.
  - constructor.
  - constructor; auto.
  - pick fresh X. apply lc_typ_all_etag_exists with (X1 := X).
    apply H0. auto.
  - pick fresh X. apply lc_typ_all_plain_exists with (X1 := X).
    apply H0. auto.
  - constructor.
  - constructor; auto.
Qed.

(** Every is_tskel is also an is_uskel. *)
Lemma is_tskel_is_uskel : forall A, is_tskel A -> is_uskel A.
Proof.
  intros A H. induction H.
  - constructor.
  - constructor.
  - constructor; auto.
  - apply is_uskel__tall with (L := L) (ε := ε). intros. apply H0; auto.
  - constructor.
  - constructor; auto.
Qed.

Lemma is_uskel_subst : forall A B X,
    is_uskel A -> is_tskel B -> is_uskel (subst_typ_in_typ B X A).
Proof.
  intros A B X HA HB. induction HA; simpl.
  - constructor.
  - destruct (X0 == X); subst.
    + apply is_tskel_is_uskel; exact HB.
    + constructor.
  - constructor; auto.
  - apply is_uskel__tall with (L := L `union` singleton X) (ε := ε).
    intros Y Hni.
    rewrite subst_typ_in_typ_open_typ_wrt_typ_var.
    + apply H0; fsetdec.
    + fsetdec.
    + apply is_tskel_lc; exact HB.
  - apply is_uskel__pall with (L := L `union` singleton X).
    intros Y Hni.
    rewrite subst_typ_in_typ_open_typ_wrt_typ_var.
    + apply H0; fsetdec.
    + fsetdec.
    + apply is_tskel_lc; exact HB.
  - constructor.
  - constructor; auto.
Qed.

