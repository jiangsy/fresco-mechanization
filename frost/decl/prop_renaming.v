(** Tvar-renaming closure lemmas: every declarative judgment ([is_*], [guarded_*],
    [d_consis], [d_wf_utyp], [d_sub]) is closed under a free type-variable
    renaming [α -> β].  The tag context [Δ] is etag-only and untouched.  Built
    bottom-up: shape predicates, then [d_consis] / [d_wf_utyp] / [d_sub].
    Used by [prop_general_subsumption] for the CST [forall_r] cofinite cases. *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.def_extra.
Require Import src.frost.prop_etag.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.prop_weakening.

Set Implicit Arguments.

(** Coercions commute with type-variable substitution. *)


Lemma is_ityp_rename_tvar : forall B α1 β1,
    is_ityp B -> is_ityp (subst_btyp_in_btyp (btyp_var_f β1) α1 B).
Proof.
  intros B α1 β1 H. induction H; simpl.
  - constructor.
  - match goal with |- context [ ?a == ?b ] => destruct (a == b) end; constructor.
  - constructor; assumption.
  - apply is_ityp__all with (L := L `union` singleton α1 `union` singleton β1).
    intros α Hα.
    erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var
      by (solve [ fsetdec | apply lc_btyp_var_f ]).
    apply H0; fsetdec.
Qed.

Lemma is_ttyp_rename_tvar : forall C α1 β1,
    is_ttyp C -> is_ttyp (subst_utyp_in_utyp (utyp_var_f β1) α1 C).
Proof.
  intros C α1 β1 H. induction H; simpl.
  - constructor.
  - match goal with |- context [ ?a == ?b ] => destruct (a == b) end; constructor.
  - constructor; assumption.
  - apply is_ttyp__all_etag with (L := L `union` singleton α1 `union` singleton β1).
    intros α Hα.
    erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var
      by (solve [ fsetdec | apply lc_utyp_var_f ]).
    apply H0; fsetdec.
Qed.

Lemma guarded_utyp_rename_tvar : forall C α1 β1,
    guarded_utyp C -> guarded_utyp (subst_utyp_in_utyp (utyp_var_f β1) α1 C).
Proof.
  intros C α1 β1 H. induction H; simpl.
  - constructor.
  - match goal with |- context [ ?a == ?b ] => destruct (a == b) end; constructor.
  - constructor; apply subst_utyp_in_utyp_lc_utyp; auto; apply lc_utyp_var_f.
Qed.

(** [d_consis] is closed under tvar renaming (Δ is etag-only, untouched). *)
Lemma d_consis_rename_tvar : forall Δ Γ C B,
    Δ ⨟ Γ ⊢ C ∼ B ->
    forall Γ1 Γ2 α0 β,
      Γ = Γ1 ++ (α0 ~ dbind_tvar) ++ Γ2 ->
      β `notin` dom (Γ1 ++ (α0 ~ dbind_tvar) ++ Γ2) ->
      Δ ⨟ (Γ1 ++ (β ~ dbind_tvar) ++ Γ2) ⊢
         (subst_utyp_in_utyp (utyp_var_f β) α0 C)
         ∼ (subst_btyp_in_btyp (btyp_var_f β) α0 B).
Proof.
  intros Δ Γ C B H. induction H; intros Γ1 Γ2 α0 β Heq Hfr; subst; simpl.
  - apply d_consis__unit. assumption.
  - destruct_if.
    + apply d_consis__var; [ auto | assumption ].
    + apply d_consis__var; [ analyze_binds H; auto | assumption ].
  - eapply d_consis__arrow.
    + eapply IHd_consis1; [ reflexivity | exact Hfr ].
    + eapply IHd_consis2; [ reflexivity | exact Hfr ].
    + assumption.
  - eapply d_consis__forall_inh_tagged with
      (L := L `union` dom (Γ1 ++ (α0 ~ dbind_tvar) ++ Γ2) `union` singleton α0 `union` singleton β).
    + intros α2 Hα2.
      erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var by (solve [ fsetdec | apply lc_utyp_var_f ]).
      erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var by (solve [ fsetdec | apply lc_btyp_var_f ]).
      rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ (β ~ dbind_tvar) ++ Γ2).
      eapply (H0 α2); [ fsetdec | simpl; reflexivity | simpl; fsetdec ].
    + assumption.
  - apply d_consis__forall_inh_untagged with
      (L := L `union` dom (Γ1 ++ (α0 ~ dbind_tvar) ++ Γ2) `union` singleton α0 `union` singleton β).
    intros α2 Hα2.
    erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var by (solve [ fsetdec | apply lc_utyp_var_f ]).
    erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var by (solve [ fsetdec | apply lc_btyp_var_f ]).
    rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ (β ~ dbind_tvar) ++ Γ2).
    eapply (H0 α2); [ fsetdec | simpl; reflexivity | simpl; fsetdec ].
  - apply d_consis__forall_syn_tagged with
      (L := L `union` dom (Γ1 ++ (α0 ~ dbind_tvar) ++ Γ2) `union` singleton α0 `union` singleton β).
    intros α2 Hα2.
    erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var by (solve [ fsetdec | apply lc_utyp_var_f ]).
    erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var by (solve [ fsetdec | apply lc_btyp_var_f ]).
    rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ (β ~ dbind_tvar) ++ Γ2).
    eapply (H0 α2); [ fsetdec | simpl; reflexivity | simpl; fsetdec ].
  - apply d_consis__forall_syn with
      (L := L `union` dom (Γ1 ++ (α0 ~ dbind_tvar) ++ Γ2) `union` singleton α0 `union` singleton β).
    intros α2 Hα2.
    erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var by (solve [ fsetdec | apply lc_utyp_var_f ]).
    erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var by (solve [ fsetdec | apply lc_btyp_var_f ]).
    rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ (β ~ dbind_tvar) ++ Γ2).
    eapply (H0 α2); [ fsetdec | simpl; reflexivity | simpl; fsetdec ].
Qed.

(** [d_wf_utyp] is closed under tvar renaming (pure well-scopedness). *)
Lemma d_wf_utyp_rename_tvar : forall Γ C,
    Γ ⊢ᵤ C ->
    forall Γ1 Γ2 α0 β,
      Γ = Γ1 ++ (α0 ~ dbind_tvar) ++ Γ2 ->
      β `notin` dom (Γ1 ++ (α0 ~ dbind_tvar) ++ Γ2) ->
      (Γ1 ++ (β ~ dbind_tvar) ++ Γ2) ⊢ᵤ (subst_utyp_in_utyp (utyp_var_f β) α0 C).
Proof.
  intros Γ C H. induction H; intros Γ1 Γ2 α0 β Heq Hfr; subst; simpl.
  - apply d_wf_utyp__unit.
  - destruct_if.
    + apply d_wf_utyp__var. auto.
    + apply d_wf_utyp__var. analyze_binds H; auto.
  - apply d_wf_utyp__arrow.
    + eapply IHd_wf_utyp1; [ reflexivity | exact Hfr ].
    + eapply IHd_wf_utyp2; [ reflexivity | exact Hfr ].
  - apply d_wf_utyp__all_syn with
      (L := L `union` dom (Γ1 ++ (α0 ~ dbind_tvar) ++ Γ2) `union` singleton α0 `union` singleton β).
    intros α2 Hα2.
    erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var by (solve [ fsetdec | apply lc_utyp_var_f ]).
    rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ (β ~ dbind_tvar) ++ Γ2).
    eapply (H0 α2); [ fsetdec | simpl; reflexivity | simpl; fsetdec ].
  - apply d_wf_utyp__all_etag with
      (L := L `union` dom (Γ1 ++ (α0 ~ dbind_tvar) ++ Γ2) `union` singleton α0 `union` singleton β).
    intros α2 Hα2.
    erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var by (solve [ fsetdec | apply lc_utyp_var_f ]).
    rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ (β ~ dbind_tvar) ++ Γ2).
    eapply (H0 α2); [ fsetdec | simpl; reflexivity | simpl; fsetdec ].
Qed.

(** Shape predicates [is_styp]/[guarded_btyp] under tvar renaming (for
    [d_sub_rename_tvar]'s infer/check cases). *)
Lemma is_styp_rename_tvar : forall B α1 β1,
    is_styp B -> is_styp (subst_btyp_in_btyp (btyp_var_f β1) α1 B).
Proof.
  intros B α1 β1 H. induction H; simpl.
  - constructor.
  - match goal with |- context [ ?a == ?b ] => destruct (a == b) end; constructor.
  - constructor; assumption.
  - apply is_styp__all with (L := L `union` singleton α1 `union` singleton β1).
    intros α Hα.
    erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var
      by (solve [ fsetdec | apply lc_btyp_var_f ]).
    apply H0; fsetdec.
Qed.

Lemma guarded_btyp_rename_tvar : forall B α1 β1,
    guarded_btyp B -> guarded_btyp (subst_btyp_in_btyp (btyp_var_f β1) α1 B).
Proof.
  intros B α1 β1 H. induction H; simpl.
  - constructor.
  - match goal with |- context [ ?a == ?b ] => destruct (a == b) end; constructor.
  - constructor; apply subst_btyp_in_btyp_lc_btyp; auto; apply lc_btyp_var_f.
Qed.

(** [d_sub] is closed under tvar renaming ([Δ] is etag-only, untouched);
    closes the cofinite-uniform [forall_r] case of the transitivity lemmas. *)
Lemma d_sub_rename_tvar : forall m Δ Γ C B,
    Δ ⨟ Γ ⊢[ m ] C ⩽ B ->
    forall Γ1 Γ2 α0 β,
      Γ = Γ1 ++ (α0 ~ dbind_tvar) ++ Γ2 ->
      β `notin` dom (Γ1 ++ (α0 ~ dbind_tvar) ++ Γ2) ->
      Δ ⨟ (Γ1 ++ (β ~ dbind_tvar) ++ Γ2) ⊢[ m ]
         (subst_utyp_in_utyp (utyp_var_f β) α0 C)
         ⩽ (subst_btyp_in_btyp (btyp_var_f β) α0 B).
Proof.
  intros m Δ Γ C B H. induction H; intros Γ1 Γ2 α0 β Heq Hfr; subst; simpl.
  - (* infer *)
    apply d_sub__infer.
    + eapply d_consis_rename_tvar; [ eassumption | reflexivity | exact Hfr ].
    + apply is_styp_rename_tvar. assumption.
    + assumption.
  - (* check *)
    apply d_sub__check.
    + apply guarded_utyp_rename_tvar. assumption.
    + apply guarded_btyp_rename_tvar. assumption.
    + eapply d_consis_rename_tvar; [ eassumption | reflexivity | exact Hfr ].
    + apply is_ityp_rename_tvar. assumption.
  - (* forall_r *)
    apply d_sub__forall_r with
      (L := L `union` dom (Γ1 ++ (α0 ~ dbind_tvar) ++ Γ2) `union` singleton α0 `union` singleton β);
      [ change (is_ityp (subst_btyp_in_btyp (btyp_var_f β) α0 (btyp_all_inh B)));
        apply is_ityp_rename_tvar; assumption | ].
    intros α2 Hα2.
    erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var by (solve [ fsetdec | apply lc_btyp_var_f ]).
    rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ (β ~ dbind_tvar) ++ Γ2).
    eapply (H1 α2); [ fsetdec | simpl; reflexivity | simpl; fsetdec ].
  - (* arg *)
    eapply d_sub__arg.
    + eapply d_consis_rename_tvar; [ eassumption | reflexivity | exact Hfr ].
    + eapply IHd_sub; [ reflexivity | exact Hfr ].
    + assumption.
  - (* forall_l_tagged *)
    eapply d_sub__forall_l_tagged with (Ψ' := Ψ').
    + assumption.
    + assumption.
    + (* tag hygiene: a TYPE-variable renaming cannot change a tag *)
      change (utyp_all_etag ε (subst_utyp_in_utyp (utyp_var_f β) α0 C))
        with (subst_utyp_in_utyp (utyp_var_f β) α0 (utyp_all_etag ε C));
      rewrite ftag_in_utyp_subst_tagfree by reflexivity; assumption.
    + apply d_tags_subst_tvar. eassumption.
    + eapply d_wf_utyp_rename_tvar; [ eassumption | reflexivity | exact Hfr ].
    + apply is_ttyp_rename_tvar. assumption.
    + rewrite <- subst_utyp_in_utyp_open_utyp_wrt_utyp by apply lc_utyp_var_f.
      eapply IHd_sub; [ reflexivity | exact Hfr ].
  - (* forall_l_untagged *)
    eapply d_sub__forall_l_untagged with (Ψ' := Ψ').
    + assumption.
    + assumption.
    + change (utyp_all_syn (subst_utyp_in_utyp (utyp_var_f β) α0 C))
        with (subst_utyp_in_utyp (utyp_var_f β) α0 (utyp_all_syn C));
      rewrite ftag_in_utyp_subst_tagfree by reflexivity; assumption.
    + apply d_tags_subst_tvar. eassumption.
    + eapply d_wf_utyp_rename_tvar; [ eassumption | reflexivity | exact Hfr ].
    + apply is_ttyp_rename_tvar. assumption.
    + rewrite <- subst_utyp_in_utyp_open_utyp_wrt_utyp by apply lc_utyp_var_f.
      eapply IHd_sub; [ reflexivity | exact Hfr ].
Qed.
