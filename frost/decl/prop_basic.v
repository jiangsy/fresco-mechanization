(** Frost — basic syntactic lemmas (Phase 2.A foundation). *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Sorting.Permutation.
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

(** Permutation preserves [list_disjoint]: same elements ↔ same
    disjointness. *)
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

Lemma is_inh_skel_is_skel : forall A, is_inh_skel A -> is_skel A.
Proof.
  intros A H. induction H.
  - constructor.
  - constructor.
  - constructor; auto.
  - apply is_skel__all with (L := L). intros X Hni. apply H0; auto.
  - constructor.
  - constructor; auto.
Qed.

Lemma is_syn_skel_is_skel : forall A, is_syn_skel A -> is_skel A.
Proof.
  intros A H. induction H.
  - constructor.
  - constructor.
  - constructor; auto.
  - apply is_skel__all with (L := L). intros X Hni. apply H0; auto.
  - constructor.
  - constructor; auto.
Qed.

Lemma is_typ_is_skel : forall A, is_typ A -> is_skel A.
Proof.
  intros A H. induction H.
  - constructor.
  - constructor.
  - constructor; auto.
  - apply is_skel__all with (L := L). intros X Hni. apply H0; auto.
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
  - constructor.
  - constructor; auto.
Qed.

(** * Category inversion lemmas. *)

(** ** is_typ. *)

Lemma is_typ_inv_arrow : forall A B,
    is_typ (typ_arrow A B) -> is_typ A /\ is_typ B.
Proof. intros A B H. inversion H; subst. split; auto. Qed.

Lemma is_typ_inv_all : forall c A,
    is_typ (typ_all_col c A) ->
    exists L, forall X, X `notin` L ->
       is_typ (open_typ_wrt_typ A (typ_var_f X)).
Proof. intros c A H. inversion H; subst. exists L. auto. Qed.

Lemma is_typ_inv_hole : is_typ typ_hole -> False.
Proof. intros H. inversion H. Qed.

Lemma is_typ_inv_tophole : forall A, is_typ (typ_tophole A) -> False.
Proof. intros A H. inversion H. Qed.

Lemma is_typ_inv_etag : forall ε A, is_typ (typ_all_etag ε A) -> False.
Proof. intros ε A H. inversion H. Qed.

(* is_typ_inv_plain dropped: typ_all_plain no longer in typ. *)

(** ** is_syn_typ. *)

Lemma is_syn_typ_inv_arrow : forall A B,
    is_syn_typ (typ_arrow A B) -> is_syn_typ A /\ is_syn_typ B.
Proof. intros A B H. inversion H; subst. split; auto. Qed.

Lemma is_syn_typ_inv_all_syn : forall A,
    is_syn_typ (typ_all_col colour_syn A) ->
    exists L, forall X, X `notin` L ->
       is_syn_typ (open_typ_wrt_typ A (typ_var_f X)).
Proof. intros A H. inversion H; subst. exists L. auto. Qed.

Lemma is_syn_typ_inv_all_inh : forall A,
    is_syn_typ (typ_all_col colour_inh A) -> False.
Proof. intros A H. inversion H. Qed.

Lemma is_syn_typ_inv_hole : is_syn_typ typ_hole -> False.
Proof. intros H. inversion H. Qed.

Lemma is_syn_typ_inv_tophole : forall A, is_syn_typ (typ_tophole A) -> False.
Proof. intros A H. inversion H. Qed.

Lemma is_syn_typ_inv_etag : forall ε A, is_syn_typ (typ_all_etag ε A) -> False.
Proof. intros ε A H. inversion H. Qed.

(* is_syn_typ_inv_plain dropped: typ_all_plain no longer in typ. *)

(** ** is_inh_typ. *)

Lemma is_inh_typ_inv_arrow : forall A B,
    is_inh_typ (typ_arrow A B) -> is_inh_typ A /\ is_inh_typ B.
Proof. intros A B H. inversion H; subst. split; auto. Qed.

Lemma is_inh_typ_inv_all_inh : forall A,
    is_inh_typ (typ_all_col colour_inh A) ->
    exists L, forall X, X `notin` L ->
       is_inh_typ (open_typ_wrt_typ A (typ_var_f X)).
Proof. intros A H. inversion H; subst. exists L. auto. Qed.

Lemma is_inh_typ_inv_all_syn : forall A,
    is_inh_typ (typ_all_col colour_syn A) -> False.
Proof. intros A H. inversion H. Qed.

Lemma is_inh_typ_inv_hole : is_inh_typ typ_hole -> False.
Proof. intros H. inversion H. Qed.

Lemma is_inh_typ_inv_tophole : forall A, is_inh_typ (typ_tophole A) -> False.
Proof. intros A H. inversion H. Qed.

Lemma is_inh_typ_inv_etag : forall ε A, is_inh_typ (typ_all_etag ε A) -> False.
Proof. intros ε A H. inversion H. Qed.

(* is_inh_typ_inv_plain dropped: typ_all_plain no longer in typ. *)

(** ** is_ttyp. *)

Lemma is_ttyp_inv_arrow : forall A B,
    is_ttyp (typ_arrow A B) -> is_ttyp A /\ is_ttyp B.
Proof. intros A B H. inversion H; subst. split; auto. Qed.

Lemma is_ttyp_inv_etag : forall ε A,
    is_ttyp (typ_all_etag ε A) ->
    exists L, forall X, X `notin` L ->
       is_ttyp (open_typ_wrt_typ A (typ_var_f X)).
Proof. intros ε A H. inversion H; subst. exists L. auto. Qed.

Lemma is_ttyp_inv_col : forall c A, is_ttyp (typ_all_col c A) -> False.
Proof. intros c A H. inversion H. Qed.

(* is_ttyp_inv_plain dropped: typ_all_plain no longer in typ. *)

Lemma is_ttyp_inv_hole : is_ttyp typ_hole -> False.
Proof. intros H. inversion H. Qed.

Lemma is_ttyp_inv_tophole : forall A, is_ttyp (typ_tophole A) -> False.
Proof. intros A H. inversion H. Qed.

(** ** is_utyp. *)

Lemma is_utyp_inv_arrow : forall A B,
    is_utyp (typ_arrow A B) -> is_utyp A /\ is_utyp B.
Proof. intros A B H. inversion H; subst. split; auto. Qed.

Lemma is_utyp_inv_etag : forall ε A,
    is_utyp (typ_all_etag ε A) ->
    exists L, forall X, X `notin` L ->
       is_utyp (open_typ_wrt_typ A (typ_var_f X)).
Proof. intros ε A H. inversion H; subst. exists L. auto. Qed.

(* is_utyp_inv_plain dropped: typ_all_plain no longer in typ. *)

Lemma is_utyp_inv_col : forall c A, is_utyp (typ_all_col c A) -> False.
Proof. intros c A H. inversion H. Qed.

Lemma is_utyp_inv_hole : is_utyp typ_hole -> False.
Proof. intros H. inversion H. Qed.

Lemma is_utyp_inv_tophole : forall A, is_utyp (typ_tophole A) -> False.
Proof. intros A H. inversion H. Qed.

(** ** is_skel. *)

Lemma is_skel_inv_arrow : forall A B,
    is_skel (typ_arrow A B) -> is_skel A /\ is_skel B.
Proof. intros A B H. inversion H; subst. split; auto. Qed.

Lemma is_skel_inv_all : forall c A,
    is_skel (typ_all_col c A) ->
    exists L, forall X, X `notin` L ->
       is_skel (open_typ_wrt_typ A (typ_var_f X)).
Proof. intros c A H. inversion H; subst. exists L. auto. Qed.

Lemma is_skel_inv_tophole : forall A,
    is_skel (typ_tophole A) -> is_skel A.
Proof. intros A H. inversion H; subst. auto. Qed.

Lemma is_skel_inv_etag : forall ε A, is_skel (typ_all_etag ε A) -> False.
Proof. intros ε A H. inversion H. Qed.

(* is_skel_inv_plain dropped: typ_all_plain no longer in typ. *)

(** ** is_tskel. *)

Lemma is_tskel_inv_arrow : forall A B,
    is_tskel (typ_arrow A B) -> is_tskel A /\ is_tskel B.
Proof. intros A B H. inversion H; subst. split; auto. Qed.

Lemma is_tskel_inv_etag : forall ε A,
    is_tskel (typ_all_etag ε A) ->
    exists L, forall X, X `notin` L ->
       is_tskel (open_typ_wrt_typ A (typ_var_f X)).
Proof. intros ε A H. inversion H; subst. exists L. auto. Qed.

Lemma is_tskel_inv_tophole : forall A,
    is_tskel (typ_tophole A) -> is_tskel A.
Proof. intros A H. inversion H; subst. auto. Qed.

Lemma is_tskel_inv_col : forall c A, is_tskel (typ_all_col c A) -> False.
Proof. intros c A H. inversion H. Qed.

(* is_tskel_inv_plain dropped: typ_all_plain no longer in typ. *)

(** ** is_uskel. *)

Lemma is_uskel_inv_arrow : forall A B,
    is_uskel (typ_arrow A B) -> is_uskel A /\ is_uskel B.
Proof. intros A B H. inversion H; subst. split; auto. Qed.

Lemma is_uskel_inv_etag : forall ε A,
    is_uskel (typ_all_etag ε A) ->
    exists L, forall X, X `notin` L ->
       is_uskel (open_typ_wrt_typ A (typ_var_f X)).
Proof. intros ε A H. inversion H; subst. exists L. auto. Qed.

(* is_uskel_inv_plain dropped: typ_all_plain no longer in typ. *)

Lemma is_uskel_inv_tophole : forall A,
    is_uskel (typ_tophole A) -> is_uskel A.
Proof. intros A H. inversion H; subst. auto. Qed.

Lemma is_uskel_inv_col : forall c A, is_uskel (typ_all_col c A) -> False.
Proof. intros c A H. inversion H. Qed.

(** * Inversion lemmas for the [syn_color] / [inh_color] paintings.

    A [syn_color C] / [inh_color C] equal to a [typ] constructor pins
    down [C]'s head [ctyp] constructor. These are the [ctyp]-era
    analogues of the [is_typ_inv_*] family above: whenever a rule whose
    conclusion is [syn_color _] / [inh_color _] is inverted against a
    concrete [typ] shape, these lemmas recover the [ctyp] base. *)

Lemma syn_color_eq_unit_inv : forall C,
    syn_color C = typ_unit -> C = ctyp_unit.
Proof. intros C H. destruct C; simpl in H; try discriminate. reflexivity. Qed.

Lemma syn_color_eq_var_inv : forall C X,
    syn_color C = typ_var_f X -> C = ctyp_var_f X.
Proof. intros C X H. destruct C; simpl in H; try discriminate. congruence. Qed.

Lemma syn_color_eq_arrow_inv : forall C A B,
    syn_color C = typ_arrow A B ->
    exists C1 C2, C = ctyp_arrow C1 C2 /\ syn_color C1 = A /\ syn_color C2 = B.
Proof.
  intros C A B H. destruct C; simpl in H; try discriminate.
  injection H as H1 H2. eauto.
Qed.

Lemma syn_color_eq_all_inv : forall C c A,
    syn_color C = typ_all_col c A ->
    c = colour_syn /\ exists C0, C = ctyp_all C0 /\ syn_color C0 = A.
Proof.
  intros C c A H. destruct C; simpl in H; try discriminate.
  injection H as Hc H0. split; [auto | eauto].
Qed.

Lemma syn_color_eq_hole_inv : forall C,
    syn_color C = typ_hole -> C = ctyp_hole.
Proof. intros C H. destruct C; simpl in H; try discriminate. reflexivity. Qed.

Lemma syn_color_eq_tophole_inv : forall C A,
    syn_color C = typ_tophole A ->
    exists C0, C = ctyp_tophole C0 /\ syn_color C0 = A.
Proof.
  intros C A H. destruct C; simpl in H; try discriminate.
  injection H as H0. eauto.
Qed.

Lemma syn_color_not_etag : forall C ε A,
    syn_color C <> typ_all_etag ε A.
Proof. intros C ε A H. destruct C; simpl in H; discriminate. Qed.

(* syn_color_not_plain dropped: typ_all_plain no longer in typ. *)

Lemma inh_color_eq_unit_inv : forall C,
    inh_color C = typ_unit -> C = ctyp_unit.
Proof. intros C H. destruct C; simpl in H; try discriminate. reflexivity. Qed.

Lemma inh_color_eq_var_inv : forall C X,
    inh_color C = typ_var_f X -> C = ctyp_var_f X.
Proof. intros C X H. destruct C; simpl in H; try discriminate. congruence. Qed.

Lemma inh_color_eq_arrow_inv : forall C A B,
    inh_color C = typ_arrow A B ->
    exists C1 C2, C = ctyp_arrow C1 C2 /\ inh_color C1 = A /\ inh_color C2 = B.
Proof.
  intros C A B H. destruct C; simpl in H; try discriminate.
  injection H as H1 H2. eauto.
Qed.

Lemma inh_color_eq_all_inv : forall C c A,
    inh_color C = typ_all_col c A ->
    c = colour_inh /\ exists C0, C = ctyp_all C0 /\ inh_color C0 = A.
Proof.
  intros C c A H. destruct C; simpl in H; try discriminate.
  injection H as Hc H0. split; [auto | eauto].
Qed.

Lemma inh_color_eq_hole_inv : forall C,
    inh_color C = typ_hole -> C = ctyp_hole.
Proof. intros C H. destruct C; simpl in H; try discriminate. reflexivity. Qed.

Lemma inh_color_eq_tophole_inv : forall C A,
    inh_color C = typ_tophole A ->
    exists C0, C = ctyp_tophole C0 /\ inh_color C0 = A.
Proof.
  intros C A H. destruct C; simpl in H; try discriminate.
  injection H as H0. eauto.
Qed.

Lemma inh_color_not_etag : forall C ε A,
    inh_color C <> typ_all_etag ε A.
Proof. intros C ε A H. destruct C; simpl in H; discriminate. Qed.

(* inh_color_not_plain dropped: typ_all_plain no longer in typ. *)

(** * [typ]-level paintings, the [ctyp]-era successors of the Part-B
    [syn_color] / [inh_color] : typ → typ.

    The original ([typ]-domain) paintings were removed by the [ctyp]
    re-encoding (where [syn_color] / [inh_color] became [ctyp → typ]).
    The proof layer (notably [prop_typing.v]) still needs the [typ →
    typ] versions — e.g. to state [d_consis_gen]-narrowing as "the
    bound type is invariant under the [syn]-painting" as a [typ]-level
    equality. We restore them here as a separate [Fixpoint] over
    [typ], collapsing every [forall] flavour to [typ_all_col colour_syn]
    / [typ_all_col colour_inh] respectively. Functionally they equal
    [syn_color (erase _)] / [inh_color (erase _)] (composition with
    [erase]) but the [Fixpoint] form keeps tactics like [rewrite]
    matching their syntactic shape. *)
Fixpoint syn_color_t (A : typ) : typ :=
  match A with
  | typ_unit => typ_unit
  | typ_var_b n => typ_var_b n
  | typ_var_f X => typ_var_f X
  | typ_arrow A1 A2 => typ_arrow (syn_color_t A1) (syn_color_t A2)
  | typ_all_col _ A0 => typ_all_col colour_syn (syn_color_t A0)
  | typ_all_etag _ A0 => typ_all_col colour_syn (syn_color_t A0)
  | typ_hole => typ_hole
  | typ_tophole A0 => typ_tophole (syn_color_t A0)
  end.

Fixpoint inh_color_t (A : typ) : typ :=
  match A with
  | typ_unit => typ_unit
  | typ_var_b n => typ_var_b n
  | typ_var_f X => typ_var_f X
  | typ_arrow A1 A2 => typ_arrow (inh_color_t A1) (inh_color_t A2)
  | typ_all_col _ A0 => typ_all_col colour_inh (inh_color_t A0)
  | typ_all_etag _ A0 => typ_all_col colour_inh (inh_color_t A0)
  | typ_hole => typ_hole
  | typ_tophole A0 => typ_tophole (inh_color_t A0)
  end.

Lemma syn_color_t_open_var_rec : forall A k Y,
    syn_color_t (open_typ_wrt_typ_rec k (typ_var_f Y) A) =
    open_typ_wrt_typ_rec k (typ_var_f Y) (syn_color_t A).
Proof.
  induction A; intros k Y; simpl; try reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity.
  - rewrite IHA1, IHA2; reflexivity.
  - rewrite IHA; reflexivity.
  - rewrite IHA; reflexivity.
  - rewrite IHA; reflexivity.
Qed.

Lemma syn_color_t_open_var : forall A Y,
    syn_color_t (open_typ_wrt_typ A (typ_var_f Y)) =
    open_typ_wrt_typ (syn_color_t A) (typ_var_f Y).
Proof.
  intros A Y. unfold open_typ_wrt_typ. apply syn_color_t_open_var_rec.
Qed.

Lemma inh_color_t_open_var_rec : forall A k Y,
    inh_color_t (open_typ_wrt_typ_rec k (typ_var_f Y) A) =
    open_typ_wrt_typ_rec k (typ_var_f Y) (inh_color_t A).
Proof.
  induction A; intros k Y; simpl; try reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity.
  - rewrite IHA1, IHA2; reflexivity.
  - rewrite IHA; reflexivity.
  - rewrite IHA; reflexivity.
  - rewrite IHA; reflexivity.
Qed.

Lemma inh_color_t_open_var : forall A Y,
    inh_color_t (open_typ_wrt_typ A (typ_var_f Y)) =
    open_typ_wrt_typ (inh_color_t A) (typ_var_f Y).
Proof.
  intros A Y. unfold open_typ_wrt_typ. apply inh_color_t_open_var_rec.
Qed.

Lemma syn_color_t_ftvar : forall A,
    ftvar_in_typ (syn_color_t A) = ftvar_in_typ A.
Proof.
  induction A; simpl; try reflexivity.
  - rewrite IHA1, IHA2. reflexivity.
  - assumption.
  - assumption.
  - assumption.
Qed.

Lemma inh_color_t_ftvar : forall A,
    ftvar_in_typ (inh_color_t A) = ftvar_in_typ A.
Proof.
  induction A; simpl; try reflexivity.
  - rewrite IHA1, IHA2. reflexivity.
  - assumption.
  - assumption.
  - assumption.
Qed.

(** [syn_color_t] / [inh_color_t] are equivalent to [syn_color ∘ erase]
    / [inh_color ∘ erase]. The [syn_color_t] form keeps a syntactic
    match on [typ] for [rewrite] tactics; the [syn_color ∘ erase] form
    is what the [d_*_gen] rules' [ctyp] base produces. Same value, two
    presentations — relate them for cross-pollination. *)
Lemma syn_color_t_syn_color_erase : forall A,
    syn_color_t A = syn_color (erase A).
Proof.
  induction A; simpl; try reflexivity.
  - rewrite IHA1, IHA2. reflexivity.
  - rewrite IHA. reflexivity.
  - rewrite IHA. reflexivity.
  - rewrite IHA. reflexivity.
Qed.

Lemma inh_color_t_inh_color_erase : forall A,
    inh_color_t A = inh_color (erase A).
Proof.
  induction A; simpl; try reflexivity.
  - rewrite IHA1, IHA2. reflexivity.
  - rewrite IHA. reflexivity.
  - rewrite IHA. reflexivity.
  - rewrite IHA. reflexivity.
Qed.

(** [mono_typ] is preserved by stripping [syn_color_t] / [inh_color_t]
    paintings: if the painting is mono, so is the underlying type.
    The non-mono cases ([typ_all_*], [typ_hole], [typ_tophole]) get
    painted to non-mono shapes ([typ_all_col colour_syn/inh] or
    [typ_hole]/[typ_tophole]) which contradict the mono premise. *)
Lemma mono_typ_syn_color_t_inv : forall A,
    mono_typ (syn_color_t A) -> mono_typ A.
Proof.
  induction A; simpl; intro H; try (inversion H; subst).
  - apply mono_typ__unit.
  - apply mono_typ__var.
  - apply mono_typ__arrow; auto.
Qed.

Lemma mono_typ_inh_color_t_inv : forall A,
    mono_typ (inh_color_t A) -> mono_typ A.
Proof.
  induction A; simpl; intro H; try (inversion H; subst).
  - apply mono_typ__unit.
  - apply mono_typ__var.
  - apply mono_typ__arrow; auto.
Qed.

(** * Mutual induction principle for d_typing ↔ d_pat. *)

Scheme d_typing_mut := Induction for d_typing Sort Prop
  with d_pat_mut    := Induction for d_pat    Sort Prop.

Combined Scheme d_typing_pat_mut from d_typing_mut, d_pat_mut.

(** Smoke test: any mutual induction goal can be opened with the scheme.
    This trivial lemma is not used downstream; it just verifies the scheme
    is syntactically usable. *)
Lemma d_typing_pat_mut_smoke :
    (forall m Γ e A, d_typing m Γ e A -> True) /\
    (forall m Γ e P, d_pat m Γ e P -> True).
Proof.
  apply d_typing_pat_mut; intros; trivial.
Qed.

