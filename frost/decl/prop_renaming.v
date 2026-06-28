(** Tvar-renaming closure lemmas: every declarative judgment ([is_*], [guarded_*],
    [d_consis], [d_wf_utyp], [d_sub]) is closed under a free type-variable
    renaming [X -> Y].  The tag context [Δ] is etag-only and untouched.  Built
    bottom-up: shape predicates, then [d_consis] / [d_wf_utyp] / [d_sub].
    Used by [prop_general_subsumption] for the CST [forall_r] cofinite cases. *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.prop_weakening.

Set Implicit Arguments.

(** Coercions commute with type-variable substitution. *)


Lemma is_ityp_rename_tvar : forall B Z W,
    is_ityp B -> is_ityp (subst_btyp_in_btyp (btyp_var_f W) Z B).
Proof.
  intros B Z W H. induction H; simpl.
  - constructor.
  - match goal with |- context [ ?a == ?b ] => destruct (a == b) end; constructor.
  - constructor; assumption.
  - apply is_ityp__all with (L := L `union` singleton Z `union` singleton W).
    intros X HX.
    erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var
      by (solve [ fsetdec | apply lc_btyp_var_f ]).
    apply H0; fsetdec.
Qed.

Lemma is_ttyp_rename_tvar : forall C Z W,
    is_ttyp C -> is_ttyp (subst_utyp_in_utyp (utyp_var_f W) Z C).
Proof.
  intros C Z W H. induction H; simpl.
  - constructor.
  - match goal with |- context [ ?a == ?b ] => destruct (a == b) end; constructor.
  - constructor; assumption.
  - apply is_ttyp__all_etag with (L := L `union` singleton Z `union` singleton W).
    intros X HX.
    erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var
      by (solve [ fsetdec | apply lc_utyp_var_f ]).
    apply H0; fsetdec.
Qed.

Lemma guarded_utyp_rename_tvar : forall C Z W,
    guarded_utyp C -> guarded_utyp (subst_utyp_in_utyp (utyp_var_f W) Z C).
Proof.
  intros C Z W H. induction H; simpl.
  - constructor.
  - match goal with |- context [ ?a == ?b ] => destruct (a == b) end; constructor.
  - constructor; apply subst_utyp_in_utyp_lc_utyp; auto; apply lc_utyp_var_f.
Qed.

(** [d_consis] is closed under tvar renaming (Δ is etag-only, untouched). *)
Lemma d_consis_rename_tvar : forall Δ Γ C B,
    Δ ⨟ Γ ⊨ C ≈ B ->
    forall Γ1 Γ2 X0 Y,
      Γ = Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2 ->
      Y `notin` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) ->
      Δ ⨟ (Γ1 ++ (Y ~ dbind_tvar) ++ Γ2) ⊨
         (subst_utyp_in_utyp (utyp_var_f Y) X0 C)
         ≈ (subst_btyp_in_btyp (btyp_var_f Y) X0 B).
Proof.
  intros Δ Γ C B H. induction H; intros Γ1 Γ2 X0 Y Heq Hfr; subst; simpl.
  - apply d_consis__unit. assumption.
  - match goal with |- context [ if ?d then _ else _ ] => destruct d end.
    + apply d_consis__var; [ auto | assumption ].
    + apply d_consis__var; [ analyze_binds H; auto | assumption ].
  - eapply d_consis__arrow.
    + eapply IHd_consis1; [ reflexivity | exact Hfr ].
    + eapply IHd_consis2; [ reflexivity | exact Hfr ].
    + assumption.
  - eapply d_consis__forall_inh_tagged with
      (L := L `union` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) `union` singleton X0 `union` singleton Y).
    + intros Z HZ.
      erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var by (solve [ fsetdec | apply lc_utyp_var_f ]).
      erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var by (solve [ fsetdec | apply lc_btyp_var_f ]).
      rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (Y ~ dbind_tvar) ++ Γ2).
      eapply (H0 Z); [ fsetdec | simpl; reflexivity | simpl; fsetdec ].
    + assumption.
  - apply d_consis__forall_inh_untagged with
      (L := L `union` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) `union` singleton X0 `union` singleton Y).
    intros Z HZ.
    erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var by (solve [ fsetdec | apply lc_utyp_var_f ]).
    erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var by (solve [ fsetdec | apply lc_btyp_var_f ]).
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (Y ~ dbind_tvar) ++ Γ2).
    eapply (H0 Z); [ fsetdec | simpl; reflexivity | simpl; fsetdec ].
  - apply d_consis__forall_syn_tagged with
      (L := L `union` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) `union` singleton X0 `union` singleton Y).
    intros Z HZ.
    erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var by (solve [ fsetdec | apply lc_utyp_var_f ]).
    erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var by (solve [ fsetdec | apply lc_btyp_var_f ]).
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (Y ~ dbind_tvar) ++ Γ2).
    eapply (H0 Z); [ fsetdec | simpl; reflexivity | simpl; fsetdec ].
  - apply d_consis__forall_syn with
      (L := L `union` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) `union` singleton X0 `union` singleton Y).
    intros Z HZ.
    erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var by (solve [ fsetdec | apply lc_utyp_var_f ]).
    erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var by (solve [ fsetdec | apply lc_btyp_var_f ]).
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (Y ~ dbind_tvar) ++ Γ2).
    eapply (H0 Z); [ fsetdec | simpl; reflexivity | simpl; fsetdec ].
Qed.

(** [d_wf_utyp] is closed under tvar renaming (pure well-scopedness). *)
Lemma d_wf_utyp_rename_tvar : forall Γ C,
    Γ ⊢ᵤ C ->
    forall Γ1 Γ2 X0 Y,
      Γ = Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2 ->
      Y `notin` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) ->
      (Γ1 ++ (Y ~ dbind_tvar) ++ Γ2) ⊢ᵤ (subst_utyp_in_utyp (utyp_var_f Y) X0 C).
Proof.
  intros Γ C H. induction H; intros Γ1 Γ2 X0 Y Heq Hfr; subst; simpl.
  - apply d_wf_utyp__unit.
  - match goal with |- context [ if ?d then _ else _ ] => destruct d end.
    + apply d_wf_utyp__var. auto.
    + apply d_wf_utyp__var. analyze_binds H; auto.
  - apply d_wf_utyp__arrow.
    + eapply IHd_wf_utyp1; [ reflexivity | exact Hfr ].
    + eapply IHd_wf_utyp2; [ reflexivity | exact Hfr ].
  - apply d_wf_utyp__all_syn with
      (L := L `union` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) `union` singleton X0 `union` singleton Y).
    intros Z HZ.
    erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var by (solve [ fsetdec | apply lc_utyp_var_f ]).
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (Y ~ dbind_tvar) ++ Γ2).
    eapply (H0 Z); [ fsetdec | simpl; reflexivity | simpl; fsetdec ].
  - apply d_wf_utyp__all_etag with
      (L := L `union` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) `union` singleton X0 `union` singleton Y).
    intros Z HZ.
    erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var by (solve [ fsetdec | apply lc_utyp_var_f ]).
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (Y ~ dbind_tvar) ++ Γ2).
    eapply (H0 Z); [ fsetdec | simpl; reflexivity | simpl; fsetdec ].
Qed.

(** Shape predicates [is_styp]/[guarded_btyp] under tvar renaming (for
    [d_sub_rename_tvar]'s infer/check cases). *)
Lemma is_styp_rename_tvar : forall B Z W,
    is_styp B -> is_styp (subst_btyp_in_btyp (btyp_var_f W) Z B).
Proof.
  intros B Z W H. induction H; simpl.
  - constructor.
  - match goal with |- context [ ?a == ?b ] => destruct (a == b) end; constructor.
  - constructor; assumption.
  - apply is_styp__all with (L := L `union` singleton Z `union` singleton W).
    intros X HX.
    erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var
      by (solve [ fsetdec | apply lc_btyp_var_f ]).
    apply H0; fsetdec.
Qed.

Lemma guarded_btyp_rename_tvar : forall B Z W,
    guarded_btyp B -> guarded_btyp (subst_btyp_in_btyp (btyp_var_f W) Z B).
Proof.
  intros B Z W H. induction H; simpl.
  - constructor.
  - match goal with |- context [ ?a == ?b ] => destruct (a == b) end; constructor.
  - constructor; apply subst_btyp_in_btyp_lc_btyp; auto; apply lc_btyp_var_f.
Qed.

(** [d_sub] is closed under tvar renaming ([Δ] is etag-only, untouched);
    closes the cofinite-uniform [forall_r] case of the transitivity lemmas. *)
Lemma d_sub_rename_tvar : forall m Δ Γ C B,
    Δ ⨟ Γ ⊢[ m ] C ⊑ B ->
    forall Γ1 Γ2 X0 Y,
      Γ = Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2 ->
      Y `notin` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) ->
      Δ ⨟ (Γ1 ++ (Y ~ dbind_tvar) ++ Γ2) ⊢[ m ]
         (subst_utyp_in_utyp (utyp_var_f Y) X0 C)
         ⊑ (subst_btyp_in_btyp (btyp_var_f Y) X0 B).
Proof.
  intros m Δ Γ C B H. induction H; intros Γ1 Γ2 X0 Y Heq Hfr; subst; simpl.
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
      (L := L `union` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) `union` singleton X0 `union` singleton Y);
      [ change (is_ityp (subst_btyp_in_btyp (btyp_var_f Y) X0 (btyp_all_inh B)));
        apply is_ityp_rename_tvar; assumption | ].
    intros Z HZ.
    erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var by (solve [ fsetdec | apply lc_btyp_var_f ]).
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (Y ~ dbind_tvar) ++ Γ2).
    eapply (H1 Z); [ fsetdec | simpl; reflexivity | simpl; fsetdec ].
  - (* arg *)
    eapply d_sub__arg.
    + eapply d_consis_rename_tvar; [ eassumption | reflexivity | exact Hfr ].
    + eapply IHd_sub; [ reflexivity | exact Hfr ].
    + assumption.
  - (* forall_l_tagged *)
    eapply d_sub__forall_l_tagged with (Ψ' := Ψ').
    + assumption.
    + assumption.
    + apply d_tags_subst_tvar. eassumption.
    + eapply d_wf_utyp_rename_tvar; [ eassumption | reflexivity | exact Hfr ].
    + apply is_ttyp_rename_tvar. assumption.
    + rewrite <- subst_utyp_in_utyp_open_utyp_wrt_utyp by apply lc_utyp_var_f.
      eapply IHd_sub; [ reflexivity | exact Hfr ].
  - (* forall_l_untagged *)
    eapply d_sub__forall_l_untagged with (Ψ' := Ψ').
    + assumption.
    + assumption.
    + apply d_tags_subst_tvar. eassumption.
    + eapply d_wf_utyp_rename_tvar; [ eassumption | reflexivity | exact Hfr ].
    + apply is_ttyp_rename_tvar. assumption.
    + rewrite <- subst_utyp_in_utyp_open_utyp_wrt_utyp by apply lc_utyp_var_f.
      eapply IHd_sub; [ reflexivity | exact Hfr ].
Qed.

(** * NON-tvar binder relabel for the subtyping suite.

    [d_sub]/[d_consis]/[d_wf_utyp] never consult a *term* binding (only tvars),
    so relabeling a non-tvar binder [x ↦ y] is inert — and, unlike the tvar
    rename above, the TYPES are unchanged (they hold no term variables).  These
    discharge the [sub] case of the typing binder-rename [d_typing_rename_var]. *)
Lemma d_wf_utyp_rename_var : forall Γ C,
    Γ ⊢ᵤ C ->
    forall Γ1 x d Γ2 y, Γ = Γ1 ++ (x ~ d) ++ Γ2 -> d <> dbind_tvar ->
    (Γ1 ++ (y ~ d) ++ Γ2) ⊢ᵤ C.
Proof.
  intros Γ C H. induction H; intros Γ1 x0 d0 Γ2 y0 Heq Hd; subst.
  - apply d_wf_utyp__unit.
  - apply d_wf_utyp__var. analyze_binds H; try (exfalso; congruence); auto.
  - apply d_wf_utyp__arrow; [ eapply IHd_wf_utyp1 | eapply IHd_wf_utyp2 ]; eauto.
  - apply d_wf_utyp__all_syn with
      (L := L `union` dom (Γ1 ++ Γ2) `union` {{x0}} `union` {{y0}}).
    intros Z HZ. rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (y0 ~ d0) ++ Γ2).
    eapply (H0 Z); [ fsetdec | simpl_env; reflexivity | exact Hd ].
  - apply d_wf_utyp__all_etag with
      (L := L `union` dom (Γ1 ++ Γ2) `union` {{x0}} `union` {{y0}}).
    intros Z HZ. rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (y0 ~ d0) ++ Γ2).
    eapply (H0 Z); [ fsetdec | simpl_env; reflexivity | exact Hd ].
Qed.

Lemma d_consis_rename_var : forall Δ Γ C B,
    Δ ⨟ Γ ⊨ C ≈ B ->
    forall Γ1 x d Γ2 y, Γ = Γ1 ++ (x ~ d) ++ Γ2 -> d <> dbind_tvar ->
    Δ ⨟ (Γ1 ++ (y ~ d) ++ Γ2) ⊨ C ≈ B.
Proof.
  intros Δ Γ C B H. induction H; intros Γ1 x0 d0 Γ2 y0 Heq Hd; subst.
  - apply d_consis__unit. assumption.
  - apply d_consis__var; [ analyze_binds H; try (exfalso; congruence); auto | assumption ].
  - eapply d_consis__arrow;
      [ eapply IHd_consis1; [ reflexivity | exact Hd ]
      | eapply IHd_consis2; [ reflexivity | exact Hd ] | assumption ].
  - eapply d_consis__forall_inh_tagged with
      (L := L `union` dom (Γ1 ++ Γ2) `union` {{x0}} `union` {{y0}});
      [ intros Z HZ; rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (y0 ~ d0) ++ Γ2);
        eapply (H0 Z); [ fsetdec | simpl_env; reflexivity | exact Hd ]
      | assumption ].
  - apply d_consis__forall_inh_untagged with
      (L := L `union` dom (Γ1 ++ Γ2) `union` {{x0}} `union` {{y0}}).
    intros Z HZ. rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (y0 ~ d0) ++ Γ2).
    eapply (H0 Z); [ fsetdec | simpl_env; reflexivity | exact Hd ].
  - apply d_consis__forall_syn_tagged with
      (L := L `union` dom (Γ1 ++ Γ2) `union` {{x0}} `union` {{y0}}).
    intros Z HZ. rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (y0 ~ d0) ++ Γ2).
    eapply (H0 Z); [ fsetdec | simpl_env; reflexivity | exact Hd ].
  - apply d_consis__forall_syn with
      (L := L `union` dom (Γ1 ++ Γ2) `union` {{x0}} `union` {{y0}}).
    intros Z HZ. rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (y0 ~ d0) ++ Γ2).
    eapply (H0 Z); [ fsetdec | simpl_env; reflexivity | exact Hd ].
Qed.

Lemma d_sub_rename_var : forall m Δ Γ C B,
    Δ ⨟ Γ ⊢[ m ] C ⊑ B ->
    forall Γ1 x d Γ2 y, Γ = Γ1 ++ (x ~ d) ++ Γ2 -> d <> dbind_tvar ->
    Δ ⨟ (Γ1 ++ (y ~ d) ++ Γ2) ⊢[ m ] C ⊑ B.
Proof.
  intros m Δ Γ C B H. induction H; intros Γ1 x0 d0 Γ2 y0 Heq Hd; subst.
  - apply d_sub__infer;
      [ eapply d_consis_rename_var; [ eassumption | reflexivity | exact Hd ]
      | assumption | assumption ].
  - apply d_sub__check;
      [ assumption | assumption
      | eapply d_consis_rename_var; [ eassumption | reflexivity | exact Hd ]
      | assumption ].
  - apply d_sub__forall_r with
      (L := L `union` dom (Γ1 ++ Γ2) `union` {{x0}} `union` {{y0}});
      [ assumption | ].
    intros Z HZ. rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (y0 ~ d0) ++ Γ2).
    eapply (H1 Z); [ fsetdec | simpl_env; reflexivity | exact Hd ].
  - eapply d_sub__arg;
      [ eapply d_consis_rename_var; [ eassumption | reflexivity | exact Hd ]
      | eapply IHd_sub; [ reflexivity | exact Hd ] | assumption ].
  - eapply d_sub__forall_l_tagged with (Ψ' := Ψ');
      [ eassumption | eassumption | eassumption
      | eapply d_wf_utyp_rename_var; [ eassumption | reflexivity | exact Hd ]
      | eassumption | eapply IHd_sub; [ reflexivity | exact Hd ] ].
  - eapply d_sub__forall_l_untagged with (Ψ' := Ψ');
      [ eassumption | eassumption | eassumption
      | eapply d_wf_utyp_rename_var; [ eassumption | reflexivity | exact Hd ]
      | eassumption | eapply IHd_sub; [ reflexivity | exact Hd ] ].
Qed.
