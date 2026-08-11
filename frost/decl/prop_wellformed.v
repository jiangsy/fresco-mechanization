(** Frost — well-formedness lemmas for the current split syntax. *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.def_extra.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.

Set Implicit Arguments.

(** * Declarative contexts. *)

Inductive d_wf_denv : list (atom * dbind) -> Prop :=
| d_wf_denv__nil : d_wf_denv nil
| d_wf_denv__tvar : forall Γ α,
    d_wf_denv Γ ->
    α `notin` dom Γ ->
    d_wf_denv ((α ~ dbind_tvar) ++ Γ)
| d_wf_denv__typ : forall Γ x A,
    d_wf_denv Γ ->
    x `notin` dom Γ ->
    d_wf_ptyp Γ A ->
    d_wf_denv ((x ~ dbind_typ A) ++ Γ)
| d_wf_denv__skl : forall Γ x P,
    d_wf_denv Γ ->
    x `notin` dom Γ ->
    d_wf_pskl Γ nil P ->
    d_wf_denv ((x ~ dbind_skl P) ++ Γ).


(** * Weakening. *)

Lemma d_wf_ptyp_weakening : forall Γ1 Γ2 Γ3 A,
    d_wf_ptyp (Γ1 ++ Γ3) A ->
    d_wf_ptyp (Γ1 ++ Γ2 ++ Γ3) A.
Proof.
  intros Γ1 Γ2 Γ3 A H. dependent induction H.
  - constructor.
  - constructor. apply binds_app_iff in H. destruct H as [Hin | Hin].
    + apply binds_app_iff; auto.
    + apply binds_app_iff. right. apply binds_app_iff; auto.
  - constructor; auto.
  - inst_cofinites_for d_wf_ptyp__all.
    intros α Hα.
    rewrite_env (((α ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    apply H0; auto.
Qed.


Lemma d_wf_utyp_weakening : forall Γ1 Γ2 Γ3 C,
    (Γ1 ++ Γ3) ⊢ᵤ C ->
    (Γ1 ++ Γ2 ++ Γ3) ⊢ᵤ C.
Proof.
  intros Γ1 Γ2 Γ3 C H. dependent induction H.
  - constructor.
  - constructor. apply binds_app_iff in H. destruct H as [Hin | Hin].
    + apply binds_app_iff; auto.
    + apply binds_app_iff. right. apply binds_app_iff; auto.
  - econstructor; eauto.
  - inst_cofinites_for d_wf_utyp__all_syn.
    intros α Hα.
    rewrite_env (((α ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    apply H0; auto.
  - inst_cofinites_for d_wf_utyp__all_etag; auto.
    intros α Hα.
    rewrite_env (((α ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    apply H0; auto.
Qed.

(** [d_wf_pskl] is monotone in the scope set [Ψ]: enlarging [Ψ] only
    relaxes the [var] rule (and the [∀] rule under its binder).  Used by
    [d_refine_preserves_wf] to bridge a premise whose cleared context
    yields a [Ψ ⊆] the one the conclusion needs. *)
Lemma d_wf_pskl_Psi_mono : forall Ψ Γ P,
    Γ ⨟ Ψ ⊢ₚₛ P ->
    forall Ψ', (forall α, List.In α Ψ -> List.In α Ψ') ->
    Γ ⨟ Ψ' ⊢ₚₛ P.
Proof.
  intros Ψ Γ P H. induction H; intros Ψ' Hmono.
  - constructor.
  - constructor. destruct H as [Hin | Hb]; [ left; auto | right; auto ].
  - constructor; auto.
  - inst_cofinites_for d_wf_pskl__all. intros α Hα. apply H0; auto.
    intros β Hβ. simpl in Hβ |- *. destruct Hβ as [Hβ | Hβ]; [ left; auto | right; auto ].
  - constructor.
  - apply d_wf_pskl__tophole; auto.
Qed.

Lemma d_wf_pskl_weakening : forall Γ1 Γ2 Γ3 Ψ P,
    (Γ1 ++ Γ3) ⨟ Ψ ⊢ₚₛ P ->
    (Γ1 ++ Γ2 ++ Γ3) ⨟ Ψ ⊢ₚₛ P.
Proof.
  intros Γ1 Γ2 Γ3 Ψ P H. dependent induction H.
  - constructor.
  - constructor. destruct H as [Hin | Hin].
    + left; auto.
    + right. apply binds_app_iff in Hin. destruct Hin as [Hin | Hin].
      * apply binds_app_iff; auto.
      * apply binds_app_iff. right. apply binds_app_iff; auto.
  - constructor; auto.
  - inst_cofinites_for d_wf_pskl__all.
    intros α Hα. apply H0; auto.
  - constructor.
  - constructor; auto.
Qed.

Lemma d_wf_uskl_weakening : forall Γ1 Γ2 Γ3 Ψ R,
    (Γ1 ++ Γ3) ⨟ Ψ ⊢ᵤₛ R ->
    (Γ1 ++ Γ2 ++ Γ3) ⨟ Ψ ⊢ᵤₛ R.
Proof.
  intros Γ1 Γ2 Γ3 Ψ R H. dependent induction H.
  - constructor.
  - constructor. destruct H as [Hin | Hin].
    + left; auto.
    + right. apply binds_app_iff in Hin. destruct Hin as [Hin | Hin].
      * apply binds_app_iff; auto.
      * apply binds_app_iff. right. apply binds_app_iff; auto.
  - constructor; auto.
  - inst_cofinites_for d_wf_uskl__all_syn.
    intros α Hα. apply H0; auto.
  - inst_cofinites_for d_wf_uskl__all_etag.
    intros α Hα. apply H0; auto.
  - constructor.
  - constructor; auto.
  - constructor.         (* holeg, as hole *)
  - constructor; auto.   (* topholeg, as tophole *)
Qed.


(** * Tag-relation under renaming.

    The latest paper (WT review) factors the old combined premise
    [Δ | Γ ⊢ φ] of the [d_sub] / [d_pat_sub] ForallL rules into pure
    well-scopedness ([d_wf_utyp], which no longer tracks tags) plus the
    pure tag relation [d_tags].  The old [d_wf_utyp_d_tags] /
    [d_wf_uskl_d_tags_skl] bridges (which read tags off the wf relation's
    context) are therefore obsolete.  What the [d_sub] rename proof
    now needs is that [d_tags] is invariant under a type-variable
    renaming — tags are ε-atoms untouched by tvar substitution. *)

Lemma d_tags_subst_tvar : forall Δ C α β,
    d_tags Δ C ->
    d_tags Δ (subst_utyp_in_utyp (utyp_var_f β) α C).
Proof.
  intros Δ C α β H. induction H; simpl.
  - auto with frost.
  - destruct_if; auto with frost.
  - eauto with frost.
  - inst_cofinites_for d_tags__all_etag Ψ0 := Ψ0; [ | assumption | assumption ].
    intros α2 Hα2.
    erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var
      by (solve [ fsetdec | apply lc_utyp_var_f ]).
    apply H0; auto.
Qed.

(** * Set-equality morphisms for the tag-indexed relations.

    [atoms] is not extensional, so the rules carry their built context up to
    [=]; these lemmas let any tag context be replaced by a set-equal one.
    They are the device that makes [forall_l] reconstruct and the [B.2]
    composition lemmas go through. *)

Lemma d_consis_equiv : forall Δ Δo Γ C B,
    Δ [=] Δo -> Δ ⨟ Γ ⊢ C ∼ B -> Δo ⨟ Γ ⊢ C ∼ B.
Proof.
  intros Δ Δo Γ C B Heq H. revert Δo Heq. induction H; intros Δo Heq.
  - apply d_consis__unit. fsetdec.
  - apply d_consis__var; [ assumption | fsetdec ].
  - eapply d_consis__arrow; [ eassumption | eassumption | fsetdec ].
  - eapply d_consis__forall_inh_tagged; [ eassumption | fsetdec ].
  - apply d_consis__forall_inh_untagged with (L := L);
      intros α Hα; eauto.
  - apply d_consis__forall_syn_tagged with (L := L);
      intros α Hα; eauto.
  - apply d_consis__forall_syn with (L := L);
      intros α Hα; eauto.
Qed.

Lemma d_sub_equiv : forall m Δ Δo Γ C B,
    Δ [=] Δo -> Δ ⨟ Γ ⊢[ m ] C ⩽ B -> Δo ⨟ Γ ⊢[ m ] C ⩽ B.
Proof.
  intros m Δ Δo Γ C B Heq H. revert Δo Heq. induction H; intros Δo Heq.
  - apply d_sub__infer; [ assumption | assumption | fsetdec ].
  - apply d_sub__check; [ assumption | assumption | | assumption ].
    eapply d_consis_equiv; [ exact Heq | eassumption ].
  - apply d_sub__forall_r with (L := L);
      [ assumption | intros α Hα; eauto ].
  - eapply d_sub__arg; [ eassumption | eassumption | fsetdec ].
  - (* forall_l_tagged: outer context pass-through, premise via IH *)
    eapply d_sub__forall_l_tagged with (Ψ' := Ψ');
      [ assumption | fsetdec | assumption | eassumption | assumption
      | assumption | ].
    match goal with
    | IH : forall _, _ [=] _ -> _ |- _ => eapply IH; fsetdec
    end.
  - eapply d_sub__forall_l_untagged with (Ψ' := Ψ');
      [ assumption | fsetdec | assumption | eassumption | assumption
      | assumption | ].
    match goal with
    | IH : forall _, _ [=] _ -> _ |- _ => eapply IH; fsetdec
    end.
Qed.

(** * Preservation hooks.

    These are the shape-correct statements the later typing/subtyping
    ports should consume.  Some are currently left as axioms while the
    proof layer is being moved off the old unified syntax; they are
    intentionally stated over the latest categories. *)


(** Single-binding weakening (specialisations of the general weakening). *)
Lemma d_wf_ptyp_cons : forall x d Γ A,
    d_wf_ptyp Γ A -> d_wf_ptyp ((x ~ d) ++ Γ) A.
Proof. intros. apply (d_wf_ptyp_weakening nil (x ~ d) Γ). simpl. auto. Qed.

Lemma d_wf_pskl_cons : forall x d Ψ Γ P,
    Γ ⨟ Ψ ⊢ₚₛ P -> ((x ~ d) ++ Γ) ⨟ Ψ ⊢ₚₛ P.
Proof. intros. apply (d_wf_pskl_weakening nil (x ~ d) Γ). simpl. auto. Qed.

(** Bindings recorded in a well-formed context are well-formed there (the
    binding's type/skeleton is wf in the prefix, weaken to the whole context). *)
Lemma d_wf_denv_binds_typ : forall x A Γ,
    d_wf_denv Γ -> binds x (dbind_typ A) Γ -> d_wf_ptyp Γ A.
Proof.
  intros x A Γ Hwf. induction Hwf; intros Hb; try solve [ inversion Hb ];
    analyze_binds Hb;
    try (match goal with HV : dbind_typ _ = dbind_typ _ |- _ => inversion HV; subst end);
    apply d_wf_ptyp_cons; first [ assumption | apply IHHwf; assumption ].
Qed.

Lemma d_wf_denv_binds_skl : forall x P Γ,
    d_wf_denv Γ -> binds x (dbind_skl P) Γ -> Γ ⨟ nil ⊢ₚₛ P.
Proof.
  intros x P Γ Hwf. induction Hwf; intros Hb; try solve [ inversion Hb ];
    analyze_binds Hb;
    try (match goal with HV : dbind_skl _ = dbind_skl _ |- _ => inversion HV; subst end);
    apply d_wf_pskl_cons; first [ assumption | apply IHHwf; assumption ].
Qed.

(** [d_wf_ptyp] local-closure / scoping projections.  (These are also
    proven in prop_skeleton.v, which sits ABOVE this file in the dependency
    order; restated here so the wf lemmas below can use them.) *)
Lemma d_wf_ptyp_lc_loc : forall Γ A, d_wf_ptyp Γ A -> lc_ptyp A.
Proof.
  intros Γ A H. induction H.
  - constructor.
  - constructor.
  - constructor; assumption.
  - pick fresh α. apply (lc_ptyp_all_exists α). apply H0. auto.
Qed.

Lemma d_wf_ptyp_ftvar : forall Γ A,
    d_wf_ptyp Γ A ->
    forall α, α `in` ftvar_in_ptyp A -> binds α dbind_tvar Γ.
Proof.
  intros Γ A H. induction H; intros β Hβ; simpl in Hβ.
  - fsetdec.
  - apply singleton_1 in Hβ. subst. assumption.
  - apply union_1 in Hβ. destruct Hβ as [Hβ | Hβ]; auto.
  - pick fresh α for (L `union` ftvar_in_ptyp A `union` dom Γ `union` singleton β).
    assert (HYo : β `in` ftvar_in_ptyp (open_ptyp_wrt_ptyp A (ptyp_var_f α))).
    { eapply ftvar_in_ptyp_open_ptyp_wrt_ptyp_lower. eassumption. }
    specialize (H0 α ltac:(auto) β HYo). analyze_binds H0.
Qed.

(** * Well-formedness of bidirectional / unresolved types from lc + scoping.

    Modelled exactly on [d_wf_pskl_of_ptyp] (prop_skeleton.v): induct on
    local-closure; the binder cases use [inst_cofinites_for] then an
    open-commute step and the lngen upper bound on free vars under opening. *)

Lemma d_wf_btyp_of_lc_ftvar : forall B Γ,
    lc_btyp B ->
    (forall α, α `in` ftvar_in_btyp B -> binds α dbind_tvar Γ) ->
    d_wf_btyp Γ B.
Proof.
  intros B Γ Hlc. revert Γ. induction Hlc; intros Γ Hcov; simpl in *.
  - apply d_wf_btyp__unit.
  - apply d_wf_btyp__var. apply Hcov. simpl. fsetdec.
  - apply d_wf_btyp__arrow;
      [ apply IHHlc1 | apply IHHlc2 ]; intros β Hβ; apply Hcov; fsetdec.
  - inst_cofinites_for d_wf_btyp__all_syn. intros α Hα. apply H0.
    intros β Hβ. apply ftvar_in_btyp_open_btyp_wrt_btyp_upper in Hβ. simpl in Hβ.
    apply union_1 in Hβ. destruct Hβ as [Hβ | Hβ].
    + apply singleton_1 in Hβ. subst.
      apply binds_app_2. apply binds_one_3; reflexivity.
    + apply binds_app_3. apply Hcov; assumption.
  - inst_cofinites_for d_wf_btyp__all_inh. intros α Hα. apply H0.
    intros β Hβ. apply ftvar_in_btyp_open_btyp_wrt_btyp_upper in Hβ. simpl in Hβ.
    apply union_1 in Hβ. destruct Hβ as [Hβ | Hβ].
    + apply singleton_1 in Hβ. subst.
      apply binds_app_2. apply binds_one_3; reflexivity.
    + apply binds_app_3. apply Hcov; assumption.
Qed.

Lemma d_wf_utyp_of_lc_ftvar : forall C Γ,
    lc_utyp C ->
    (forall α, α `in` ftvar_in_utyp C -> binds α dbind_tvar Γ) ->
    d_wf_utyp Γ C.
Proof.
  intros C Γ Hlc. revert Γ. induction Hlc; intros Γ Hcov; simpl in *.
  - apply d_wf_utyp__unit.
  - apply d_wf_utyp__var. apply Hcov. simpl. fsetdec.
  - apply d_wf_utyp__arrow;
      [ apply IHHlc1 | apply IHHlc2 ]; intros β Hβ; apply Hcov; fsetdec.
  - inst_cofinites_for d_wf_utyp__all_syn. intros α Hα. apply H0.
    intros β Hβ. apply ftvar_in_utyp_open_utyp_wrt_utyp_upper in Hβ. simpl in Hβ.
    apply union_1 in Hβ. destruct Hβ as [Hβ | Hβ].
    + apply singleton_1 in Hβ. subst.
      apply binds_app_2. apply binds_one_3; reflexivity.
    + apply binds_app_3. apply Hcov; assumption.
  - inst_cofinites_for d_wf_utyp__all_etag. intros α Hα. apply H0.
    intros β Hβ. apply ftvar_in_utyp_open_utyp_wrt_utyp_upper in Hβ. simpl in Hβ.
    apply union_1 in Hβ. destruct Hβ as [Hβ | Hβ].
    + apply singleton_1 in Hβ. subst.
      apply binds_app_2. apply binds_one_3; reflexivity.
    + apply binds_app_3. apply Hcov; assumption.
Qed.

(** Conversely: a wf type is locally closed and its free vars are bound. *)

Lemma d_wf_btyp_lc : forall Γ B, d_wf_btyp Γ B -> lc_btyp B.
Proof.
  intros Γ B H. induction H.
  - constructor.
  - constructor.
  - constructor; assumption.
  - pick fresh α. apply (lc_btyp_all_syn_exists α). apply H0. auto.
  - pick fresh α. apply (lc_btyp_all_inh_exists α). apply H0. auto.
Qed.

Lemma d_wf_btyp_ftvar : forall Γ B,
    d_wf_btyp Γ B ->
    forall α, α `in` ftvar_in_btyp B -> binds α dbind_tvar Γ.
Proof.
  intros Γ B H. induction H; intros β Hβ; simpl in Hβ.
  - fsetdec.
  - apply singleton_1 in Hβ. subst. assumption.
  - apply union_1 in Hβ. destruct Hβ as [Hβ | Hβ]; auto.
  - pick fresh α for (L `union` ftvar_in_btyp B `union` dom Γ `union` singleton β).
    assert (HYo : β `in` ftvar_in_btyp (open_btyp_wrt_btyp B (btyp_var_f α))).
    { eapply ftvar_in_btyp_open_btyp_wrt_btyp_lower. eassumption. }
    specialize (H0 α ltac:(auto) β HYo). analyze_binds H0.
  - pick fresh α for (L `union` ftvar_in_btyp B `union` dom Γ `union` singleton β).
    assert (HYo : β `in` ftvar_in_btyp (open_btyp_wrt_btyp B (btyp_var_f α))).
    { eapply ftvar_in_btyp_open_btyp_wrt_btyp_lower. eassumption. }
    specialize (H0 α ltac:(auto) β HYo). analyze_binds H0.
Qed.

Lemma d_wf_utyp_lc : forall Γ C, d_wf_utyp Γ C -> lc_utyp C.
Proof.
  intros Γ C H. induction H.
  - constructor.
  - constructor.
  - constructor; assumption.
  - pick fresh α. apply (lc_utyp_all_syn_exists α). apply H0. auto.
  - pick fresh α. apply (lc_utyp_all_etag_exists α). apply H0. auto.
Qed.

Lemma d_wf_pskl_lc : forall Γ Δ P, Γ ⨟ Δ ⊢ₚₛ P -> lc_pskl P.
Proof.
  intros Γ Δ P H. induction H.
  - constructor.
  - constructor.
  - constructor; assumption.
  - pick fresh α. apply (lc_pskl_all_syn_exists α). apply H0. auto.
  - constructor.
  - constructor; assumption.
Qed.

Lemma d_wf_utyp_ftvar : forall Γ C,
    d_wf_utyp Γ C ->
    forall α, α `in` ftvar_in_utyp C -> binds α dbind_tvar Γ.
Proof.
  intros Γ C H. induction H; intros β Hβ; simpl in Hβ.
  - fsetdec.
  - apply singleton_1 in Hβ. subst. assumption.
  - apply union_1 in Hβ. destruct Hβ as [Hβ | Hβ]; auto.
  - pick fresh α for (L `union` ftvar_in_utyp C `union` dom Γ `union` singleton β).
    assert (HYo : β `in` ftvar_in_utyp (open_utyp_wrt_utyp C (utyp_var_f α))).
    { eapply ftvar_in_utyp_open_utyp_wrt_utyp_lower. eassumption. }
    specialize (H0 α ltac:(auto) β HYo). analyze_binds H0.
  - pick fresh α for (L `union` ftvar_in_utyp C `union` dom Γ `union` singleton β).
    assert (HYo : β `in` ftvar_in_utyp (open_utyp_wrt_utyp C (utyp_var_f α))).
    { eapply ftvar_in_utyp_open_utyp_wrt_utyp_lower. eassumption. }
    specialize (H0 α ltac:(auto) β HYo). analyze_binds H0.
Qed.

(** * Painting preserves well-formedness.

    Route via lc/ftvar: the paintings of a [ptyp] are lc whenever the
    [ptyp] is, and they have exactly the same free tvars; then apply the
    [_of_lc_ftvar] lemmas. *)

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

Lemma d_wf_btyp_painting_syn : forall Γ A,
    d_wf_ptyp Γ A -> d_wf_btyp Γ (ptyp_to_btyp_syn A).
Proof.
  intros Γ A H. apply d_wf_btyp_of_lc_ftvar.
  - apply lc_ptyp_to_btyp_syn. eapply d_wf_ptyp_lc_loc; eassumption.
  - rewrite ftvar_ptyp_to_btyp_syn. intros α Hα. eapply d_wf_ptyp_ftvar; eassumption.
Qed.

Lemma d_wf_btyp_painting_inh : forall Γ A,
    d_wf_ptyp Γ A -> d_wf_btyp Γ (ptyp_to_btyp_inh A).
Proof.
  intros Γ A H. apply d_wf_btyp_of_lc_ftvar.
  - apply lc_ptyp_to_btyp_inh. eapply d_wf_ptyp_lc_loc; eassumption.
  - rewrite ftvar_ptyp_to_btyp_inh. intros α Hα. eapply d_wf_ptyp_ftvar; eassumption.
Qed.

Lemma d_wf_utyp_painting_syn : forall Γ A,
    d_wf_ptyp Γ A -> d_wf_utyp Γ (ptyp_to_utyp_syn A).
Proof.
  intros Γ A H. apply d_wf_utyp_of_lc_ftvar.
  - apply lc_ptyp_to_utyp_syn. eapply d_wf_ptyp_lc_loc; eassumption.
  - rewrite ftvar_ptyp_to_utyp_syn. intros α Hα. eapply d_wf_ptyp_ftvar; eassumption.
Qed.

(** A [ptyp] is lc whenever its inh painting is.  Route via [degree]:
    the inh painting preserves binder structure exactly, so it preserves
    [degree] at every level; then bridge degree 0 back to [lc_ptyp]. *)
Lemma degree_btyp_inh_of_degree_ptyp : forall A k,
    degree_ptyp_wrt_ptyp k A -> degree_btyp_wrt_btyp k (ptyp_to_btyp_inh A).
Proof.
  induction A; intros k H; simpl; inversion H; subst; constructor; auto.
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

(** Inherited painting wf transfers to synthesised painting (same lc / ftvar). *)
Lemma d_wf_btyp_inh_to_syn : forall A Γ,
    d_wf_btyp Γ (ptyp_to_btyp_inh A) -> d_wf_btyp Γ (ptyp_to_btyp_syn A).
Proof.
  intros A Γ H. apply d_wf_btyp_of_lc_ftvar.
  - apply lc_ptyp_to_btyp_syn. apply lc_ptyp_of_lc_btyp_inh.
    eapply d_wf_btyp_lc; eassumption.
  - rewrite ftvar_ptyp_to_btyp_syn. intros α Hα.
    eapply (d_wf_btyp_ftvar H). rewrite ftvar_ptyp_to_btyp_inh. assumption.
Qed.

Lemma d_wf_btyp_syn_to_inh : forall A Γ,
    d_wf_btyp Γ (ptyp_to_btyp_syn A) -> d_wf_btyp Γ (ptyp_to_btyp_inh A).
Proof.
  intros A Γ H. apply d_wf_btyp_of_lc_ftvar.
  - apply lc_ptyp_to_btyp_inh. apply lc_ptyp_of_lc_btyp_syn.
    eapply d_wf_btyp_lc; eassumption.
  - rewrite ftvar_ptyp_to_btyp_inh. intros α Hα.
    eapply (d_wf_btyp_ftvar H). rewrite ftvar_ptyp_to_btyp_syn. assumption.
Qed.

(** [btyp_to_ptyp] (the erasing coercion) preserves free vars and reflects
    local closure — lets the [AbsAnno]/[App] cases recover [Barg]'s wf from
    its erasure's wf. *)
(** A fully-inherited [btyp] is the inh-painting of its own erasure: re-painting
    every (already-inh) quantifier returns the same type.  Needed by the
    [forall_r] case of the abstraction-tail subsumption lemmas, where the result
    [btyp_all_inh B] (with [is_ityp B]) must be matched against the painted
    result [btyp_all_inh (ptyp_to_btyp_inh A)] forced by [d_typing__forall]. *)
Lemma is_ityp_ptyp_to_btyp_inh : forall B,
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

(** The inh-painting of a (locally-closed) [ptyp] is fully inherited. *)
Lemma is_ityp_paint : forall A, lc_ptyp A -> is_ityp (ptyp_to_btyp_inh A).
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

Lemma degree_btyp_of_degree_ptyp_erase : forall B k,
    degree_ptyp_wrt_ptyp k (btyp_to_ptyp B) -> degree_btyp_wrt_btyp k B.
Proof.
  induction B; intros k H; simpl in H; inversion H; subst; constructor; auto.
Qed.

Lemma d_wf_btyp_of_wf_ptyp_erase : forall Γ B,
    d_wf_ptyp Γ (btyp_to_ptyp B) -> d_wf_btyp Γ B.
Proof.
  intros Γ B H. apply d_wf_btyp_of_lc_ftvar.
  - apply lc_btyp_of_degree. apply degree_btyp_of_degree_ptyp_erase.
    apply degree_ptyp_wrt_ptyp_of_lc_ptyp. eapply d_wf_ptyp_lc_loc; eassumption.
  - intros α Hα. eapply d_wf_ptyp_ftvar; [ eassumption | ].
    rewrite ftvar_btyp_to_ptyp. assumption.
Qed.

(** * Single-binding strengthening for [d_wf_btyp].
    A term binding ([dbind_typ] / [dbind_skl]) at the head of the context is
    never a [dbind_tvar], so the body type's wf does not depend on it. *)
Lemma d_wf_btyp_strengthen_head : forall x d Γ B,
    d_wf_btyp ((x ~ d) ++ Γ) B -> d <> dbind_tvar -> d_wf_btyp Γ B.
Proof.
  intros x d Γ B H Hd.
  apply d_wf_btyp_of_lc_ftvar.
  - eapply d_wf_btyp_lc; eassumption.
  - intros α Hα. pose proof (d_wf_btyp_ftvar H Hα) as Hb.
    analyze_binds Hb; try (subst; contradiction).
Qed.

(** * Consistency / subtyping preserve well-formedness (utyp ⇒ btyp). *)

Lemma d_consis_wf : forall Δ Γ C B,
    Δ ⨟ Γ ⊢ C ∼ B -> d_wf_utyp Γ C -> d_wf_btyp Γ B.
Proof.
  intros Δ Γ C B H. induction H; intros Hwf.
  - apply d_wf_btyp__unit.
  - apply d_wf_btyp__var. assumption.
  - inversion Hwf; subst. apply d_wf_btyp__arrow; auto.
  - (* forall_inh_tagged: utyp_all_etag ε C ∼ btyp_all_inh B *)
    inversion Hwf; subst. inst_cofinites_for d_wf_btyp__all_inh.
    intros α Hα. apply H0; auto.
  - (* forall_inh_untagged: utyp_all_syn C ∼ btyp_all_inh B *)
    inversion Hwf; subst. inst_cofinites_for d_wf_btyp__all_inh.
    intros α Hα. apply H0; auto.
  - (* forall_syn_tagged: utyp_all_etag ε C ∼ btyp_all_syn B *)
    inversion Hwf; subst. inst_cofinites_for d_wf_btyp__all_syn.
    intros α Hα. apply H0; auto.
  - (* forall_syn: utyp_all_syn C ∼ btyp_all_syn B *)
    inversion Hwf; subst. inst_cofinites_for d_wf_btyp__all_syn.
    intros α Hα. apply H0; auto.
Qed.

(** Substituting a well-formed [ph] for a head tvar preserves [d_wf_utyp]. *)
Lemma d_wf_utyp_subst_tvar : forall α Γ C' C,
    d_wf_utyp ((α ~ dbind_tvar) ++ Γ) C' ->
    d_wf_utyp Γ C ->
    d_wf_utyp Γ (subst_utyp_in_utyp C α C').
Proof.
  intros α Γ C' C HD Hph.
  apply d_wf_utyp_of_lc_ftvar.
  - apply subst_utyp_in_utyp_lc_utyp; [ eapply d_wf_utyp_lc; eassumption
                                      | eapply d_wf_utyp_lc; eassumption ].
  - intros β Hβ. apply ftvar_in_utyp_subst_utyp_in_utyp_upper in Hβ.
    apply union_1 in Hβ. destruct Hβ as [Hβ | Hβ].
    + eapply d_wf_utyp_ftvar; eassumption.
    + assert (HYne : β <> α).
      { intro Heq. subst. eapply remove_1; [ reflexivity | eassumption ]. }
      apply remove_3 in Hβ.
      pose proof (d_wf_utyp_ftvar HD Hβ) as Hb. analyze_binds Hb.
Qed.

Lemma d_sub_wf : forall m Δ Γ C B,
    Δ ⨟ Γ ⊢[ m ] C ⩽ B -> d_wf_utyp Γ C -> d_wf_btyp Γ B.
Proof.
  intros m Δ Γ C B H. induction H; intros Hwf.
  - (* infer *) eapply d_consis_wf; eassumption.
  - (* check *) eapply d_consis_wf; eassumption.
  - (* forall_r: C ⩽ btyp_all_inh B *)
    inst_cofinites_for d_wf_btyp__all_inh. intros α Hα.
    apply H1; auto. apply d_wf_utyp_weakening with (Γ1 := nil). simpl. assumption.
  - (* arg: utyp_arrow C1 C2 ⩽ btyp_arrow B1 B2 *)
    inversion Hwf; subst. apply d_wf_btyp__arrow.
    + eapply d_consis_wf; eassumption.
    + apply IHd_sub; assumption.
  - (* forall_l_tagged: utyp_all_etag ε C ⩽ B; recurse on opened body *)
    inversion Hwf; subst. apply IHd_sub.
    pick fresh α for (L `union` dom Γ `union` ftvar_in_utyp C).
    rewrite (subst_utyp_in_utyp_intro α) by auto.
    apply d_wf_utyp_subst_tvar; auto.
  - (* forall_l_untagged: utyp_all_syn C ⩽ B *)
    inversion Hwf; subst. apply IHd_sub.
    pick fresh α for (L `union` dom Γ `union` ftvar_in_utyp C).
    rewrite (subst_utyp_in_utyp_intro α) by auto.
    apply d_wf_utyp_subst_tvar; auto.
Qed.

(** For the [Sub] case: the subtyping LHS is [ptyp_to_utyp_syn] of the
    btyp [B1]'s erasure.  Its wf follows from [B1]'s wf via lc/ftvar. *)
Lemma lc_ptyp_btyp_to_ptyp : forall B, lc_btyp B -> lc_ptyp (btyp_to_ptyp B).
Proof.
  intros B H. apply lc_ptyp_of_degree.
  (* degree of erasure equals degree of B (structure preserved) *)
  assert (forall k, degree_btyp_wrt_btyp k B -> degree_ptyp_wrt_ptyp k (btyp_to_ptyp B)) as Hd.
  { clear H. induction B; intros k Hn; simpl in *; inversion Hn; subst; constructor; auto. }
  apply Hd. apply degree_btyp_wrt_btyp_of_lc_btyp. assumption.
Qed.

Lemma d_wf_utyp_painting_syn_btyp : forall Γ B,
    d_wf_btyp Γ B -> d_wf_utyp Γ (ptyp_to_utyp_syn (btyp_to_ptyp B)).
Proof.
  intros Γ B H. apply d_wf_utyp_of_lc_ftvar.
  - apply lc_ptyp_to_utyp_syn. apply lc_ptyp_btyp_to_ptyp.
    eapply d_wf_btyp_lc; eassumption.
  - rewrite ftvar_ptyp_to_utyp_syn. rewrite ftvar_btyp_to_ptyp.
    intros α Hα. eapply d_wf_btyp_ftvar; eassumption.
Qed.

(** * Typing preserves well-formedness of the synthesised/checked btyp.

    Standalone (NOT mutual with [d_pat]): the App case's result type wf
    comes from the FUNCTION premise via the IH + arrow inversion, never
    from the [d_pat] premise. *)
Lemma d_typing_wf_btyp : forall m Γ e B,
    d_typing m Γ e B -> d_wf_denv Γ -> d_wf_btyp Γ B.
Proof.
  intros m Γ e B H. induction H; intros Hwf.
  - (* unit *) apply d_wf_btyp__unit.
  - (* var *) apply d_wf_btyp_painting_syn. eapply d_wf_denv_binds_typ; eassumption.
  - (* anno *) apply d_wf_btyp_inh_to_syn. apply IHd_typing; assumption.
  - (* sub *) eapply d_sub_wf; [ eassumption | ].
    rewrite <- (btyp_to_ptyp_ptyp_to_btyp_syn A).
    apply d_wf_utyp_painting_syn_btyp. apply IHd_typing; assumption.
  - (* freeze *) apply d_wf_btyp_syn_to_inh. apply IHd_typing; assumption.
  - (* forall *) apply d_wf_btyp__all_inh with (L := L `union` dom Γ). intros α Hα.
    apply H1; auto. apply d_wf_denv__tvar; auto.
  - (* abs (general) *) apply d_wf_btyp__arrow.
    + apply d_wf_btyp_painting_inh. assumption.
    + pick fresh x for (L `union` dom Γ).
      eapply (d_wf_btyp_strengthen_head (x := x) (d := dbind_typ A)).
      * apply H2; auto. apply d_wf_denv__typ; auto.
      * discriminate.
  - (* abs_anno (general) *) apply d_wf_btyp__arrow.
    + apply d_wf_btyp_of_wf_ptyp_erase. rewrite H0. assumption.
    + pick fresh x for (L `union` dom Γ).
      eapply (d_wf_btyp_strengthen_head (x := x) (d := dbind_typ A)).
      * apply H3; auto. apply d_wf_denv__typ; auto.
      * discriminate.
  - (* app: result B2 from e1 : btyp_arrow B1 B2 *)
    assert (Harr : d_wf_btyp Γ (btyp_arrow B1 B2)) by (apply IHd_typing1; assumption).
    inversion Harr; subst. assumption.
Qed.

(** Subtyping preserves the colour/mode discipline [skmod{TY}]: its RHS colour
    matches its mode (the [sub]/[app] typing rules read their result colour off
    a subtyping / a function arrow, so this feeds [d_typing_skmod]). *)
Lemma d_sub_skmod : forall m Ψ Γ C B, Ψ ⨟ Γ ⊢[ m ] C ⩽ B -> mod_comp_ty B m.
Proof.
  intros m Ψ Γ C B H. induction H.
  - apply mod_comp_ty__ti; assumption.
  - apply mod_comp_ty__tc; assumption.
  - apply mod_comp_ty__tc; assumption.
  - apply mod_comp_ty__fn; assumption.
  - assumption.
  - assumption.
Qed.

(** Typing preserves the colour/mode discipline [skmod{TY}]: a well-formed
    [d_typing] derivation's result type is [M]-coloured.  Companion to
    [d_typing_wf_btyp] (this is the colour half of the implicit [skmod{TY}]
    well-formedness on the conclusion). *)
Lemma d_typing_skmod : forall m Γ e B,
    d_typing m Γ e B -> d_wf_denv Γ -> mod_comp_ty B m.
Proof.
  intros m Γ e B H. induction H; intros Hwf.
  - (* unit *) apply mod_comp_ty__ti. apply is_styp__unit.
  - (* var *) apply mod_comp_ty__ti. apply is_styp_ptyp_to_btyp_syn.
    eapply d_wf_ptyp_lc_loc. eapply d_wf_denv_binds_typ; eassumption.
  - (* anno: result syn A — lc A from the inherited premise (IH) *)
    apply mod_comp_ty__ti. apply is_styp_ptyp_to_btyp_syn.
    apply lc_ptyp_of_lc_btyp_inh. apply is_ityp_lc.
    assert (Hi : mod_comp_ty (ptyp_to_btyp_inh A) mode_tc) by (apply IHd_typing; assumption).
    inversion Hi; subst. assumption.
  - (* sub *) eapply d_sub_skmod; eassumption.
  - (* freeze: result inh A — lc A from the synthesised premise (IH) *)
    apply mod_comp_ty__tc. apply is_ityp_paint.
    apply lc_ptyp_of_lc_btyp_syn. apply is_styp_lc.
    assert (Hs : mod_comp_ty (ptyp_to_btyp_syn A) mode_ti) by (apply IHd_typing; assumption).
    inversion Hs; subst. assumption.
  - (* forall: result ∀-inherited — each instance is inherited (IH) *)
    apply mod_comp_ty__tc. apply is_ityp__all with (L := L `union` dom Γ).
    intros α Hα.
    assert (Hsk : mod_comp_ty (open_btyp_wrt_btyp (ptyp_to_btyp_inh A) (btyp_var_f α)) mode_tc)
      by (apply H1; [ auto | apply d_wf_denv__tvar; auto ]).
    inversion Hsk; subst. assumption.
  - (* abs: skmod premise is embedded on the rule *) assumption.
  - (* abs_anno: skmod premise is embedded on the rule *) assumption.
  - (* app: result B2 from the [fn m]-coloured function arrow *)
    assert (Hf : mod_comp_ty (btyp_arrow B1 B2) (mode_fn m)) by (apply IHd_typing1; assumption).
    inversion Hf; subst. assumption.
Qed.

(* RESTART NOTE: the pre-restart scaffold [d_typing_pat_preserves_wf]
   (typing/skeleton-inference outputs are well-formed) was an admitted stub
   with no users; dropped per the no-admits policy.  Re-prove on demand when
   the paper's proofs need output well-formedness. *)

(** * Well-formedness consequences used by variable head-factoring.

    The [d_wf_denv] context invariant carries [x ∉ dom Γ] at every
    extension and [d_wf_ptyp Γ A] at every term binding, so it yields
    both [uniq Γ] (needed to identify a variable's binding under the
    [d_typing__var] inversion) and the binding's well-formedness
    (needed by the consistency-transitivity steps). *)
Lemma d_wf_denv_uniq : forall Γ, d_wf_denv Γ -> uniq Γ.
Proof. intros Γ H; induction H; auto. Qed.

(** A term binding's type is well-formed in the full context (the
    invariant records it over the tail; weaken back up). *)
Lemma d_wf_denv_binds_ptyp : forall Γ x A,
    d_wf_denv Γ ->
    binds x (dbind_typ A) Γ ->
    d_wf_ptyp Γ A.
Proof.
  intros Γ x A Hwf. induction Hwf; intros Hb.
  - inversion Hb.
  - analyze_binds Hb.
    rewrite_env (nil ++ (α ~ dbind_tvar) ++ Γ).
    apply d_wf_ptyp_weakening. simpl. apply IHHwf; assumption.
  - analyze_binds Hb.
    + assert (A = A0) by congruence. subst A0.
      rewrite_env (nil ++ (x0 ~ dbind_typ A) ++ Γ).
      apply d_wf_ptyp_weakening. simpl. exact H0.
    + rewrite_env (nil ++ (x0 ~ dbind_typ A0) ++ Γ).
      apply d_wf_ptyp_weakening. simpl. apply IHHwf; assumption.
  - analyze_binds Hb.
    rewrite_env (nil ++ (x0 ~ dbind_skl P) ++ Γ).
    apply d_wf_ptyp_weakening. simpl. apply IHHwf; assumption.
Qed.

(** Consistency is reflexive on the synthesised painting: a
    well-formed [A] synthesises a [btyp] consistent with the
    [utyp] painting of the same [A] (empty tag context). *)
Lemma d_consis_syn_refl : forall Γ A,
    d_wf_ptyp Γ A ->
    empty ⨟ Γ ⊢ ptyp_to_utyp_syn A ∼ ptyp_to_btyp_syn A.
Proof.
  intros Γ A Hwf. induction Hwf; simpl.
  - apply d_consis__unit; reflexivity.
  - apply d_consis__var; [ exact H | reflexivity ].
  - apply d_consis__arrow with (Ψ1 := empty) (Ψ2 := empty);
      [ exact IHHwf1 | exact IHHwf2 | fsetdec ].
  - apply d_consis__forall_syn with (L := L). intros α Hα.
    specialize (H0 α Hα).
    rewrite ptyp_to_utyp_syn_open in H0.
    rewrite ptyp_to_btyp_syn_open in H0.
    simpl in H0. exact H0.
Qed.

(** Structural converse of [d_consis_syn_refl]: a synthesised painting is
    consistent ONLY with its own [btyp] synthesis.  Holds because the
    target is forced [is_styp] (synthesised) — that excludes the
    [d_consis__forall_inh_*] rules (whose RHS is inherited) and the tagged
    rules (whose LHS is [utyp_all_etag], never produced by a painting), so
    consistency collapses to structural congruence.  This is what makes a
    variable's [mode_ti] type EXACTLY its binding painting, hence the
    extracted [d_sub] lands at the empty tag context demanded by
    [d_typing__sub]. *)
Lemma d_consis_paint_syn_eq : forall B,
    is_styp B ->
    forall Δ Γ A, Δ ⨟ Γ ⊢ ptyp_to_utyp_syn A ∼ B -> B = ptyp_to_btyp_syn A.
Proof.
  intros B Hstyp. induction Hstyp; intros Δ Γ A Hc.
  - (* unit *) destruct A; simpl in Hc; inversion Hc; subst; reflexivity.
  - (* var *) destruct A; simpl in Hc; inversion Hc; subst; reflexivity.
  - (* arrow *)
    destruct A; simpl in Hc; inversion Hc; subst.
    simpl. f_equal; [ eapply IHHstyp1 | eapply IHHstyp2 ]; eassumption.
  - (* all_syn *)
    destruct A; simpl in Hc; inversion Hc; subst.
    simpl. f_equal.
    pick fresh α for (L `union` L0 `union` ftvar_in_btyp B `union` ftvar_in_ptyp A).
    specialize (H5 α ltac:(auto)).
    replace (utyp_var_f α) with (ptyp_to_utyp_syn (ptyp_var_f α)) in H5 by reflexivity.
    rewrite <- ptyp_to_utyp_syn_open in H5.
    specialize (H0 α ltac:(auto) Δ ((α ~ dbind_tvar) ++ Γ)
                  (open_ptyp_wrt_ptyp A (ptyp_var_f α)) H5).
    rewrite ptyp_to_btyp_syn_open in H0. simpl in H0.
    apply open_btyp_wrt_btyp_inj with (α1 := α).
    + fsetdec.
    + match goal with |- context [ ftvar_in_btyp (ptyp_to_btyp_syn ?A0) ] =>
        rewrite (ftvar_ptyp_to_btyp_syn A0) end. fsetdec.
    + exact H0.
Qed.

(** Well-formed plain types are locally closed. *)
Lemma d_wf_ptyp_lc : forall Γ A, d_wf_ptyp Γ A -> lc_ptyp A.
Proof.
  intros Γ A H. induction H.
  - apply lc_ptyp_unit.
  - apply lc_ptyp_var_f.
  - apply lc_ptyp_arrow; assumption.
  - pick fresh α. apply (lc_ptyp_all_exists α). auto.
Qed.
