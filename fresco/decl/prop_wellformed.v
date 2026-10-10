(** Fresco — well-formedness lemmas for the current split syntax. *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_basic.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.

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
    d_wf_pskl Γ empty P ->
    d_wf_denv ((x ~ dbind_skl P) ++ Γ).

(** * Context monotonicity.

    Every declarative judgement reads its context only through [binds], and
    all but the term-level ones ([d_pat], [d_sd_typing], [d_typing]) only
    through [binds α dbind_tvar].  So one relation per kind of lookup
    discharges weakening, exchange and every other context change at once
    (the decl twin of [aenv_binds_le] / [aenv_tbinds_le] in
    algo_decl/prop_ctx_mono.v): each judgement gets ONE [_mono] /
    [_tvar_mono] lemma, and weakening is an instance. *)

(** [Γ'] sees every entry [Γ] sees. *)
Definition denv_binds_le (Γ Γ' : list (atom * dbind)) : Prop :=
  forall x b, binds x b Γ -> binds x b Γ'.

(** [Γ'] sees every type variable [Γ] sees. *)
Definition denv_tbinds_le (Γ Γ' : list (atom * dbind)) : Prop :=
  forall α, binds α dbind_tvar Γ -> binds α dbind_tvar Γ'.

Lemma denv_binds_le_refl : forall Γ, denv_binds_le Γ Γ.
Proof. intros Γ x b H; exact H. Qed.

Lemma denv_binds_le_trans : forall Γ1 Γ2 Γ3,
    denv_binds_le Γ1 Γ2 -> denv_binds_le Γ2 Γ3 -> denv_binds_le Γ1 Γ3.
Proof. intros Γ1 Γ2 Γ3 H12 H23 x b H; auto. Qed.

Lemma denv_tbinds_le_of_binds_le : forall Γ Γ',
    denv_binds_le Γ Γ' -> denv_tbinds_le Γ Γ'.
Proof. intros Γ Γ' H α Hb; auto. Qed.

(** The shape every binder row needs: the SAME block pushed on both sides. *)
Lemma denv_binds_le_cons : forall Γ Γ' (Γ0 : list (atom * dbind)),
    denv_binds_le Γ Γ' -> denv_binds_le (Γ0 ++ Γ) (Γ0 ++ Γ').
Proof.
  intros Γ Γ' Γ0 H x b Hb.
  apply binds_app_iff in Hb as [Hb | Hb]; apply binds_app_iff; auto.
Qed.

Lemma denv_tbinds_le_cons : forall Γ Γ' (Γ0 : list (atom * dbind)),
    denv_tbinds_le Γ Γ' -> denv_tbinds_le (Γ0 ++ Γ) (Γ0 ++ Γ').
Proof.
  intros Γ Γ' Γ0 H α Hb.
  apply binds_app_iff in Hb as [Hb | Hb]; apply binds_app_iff; auto.
Qed.

(** Weakening in the middle (at the front when [Γ1 = nil]). *)
Lemma denv_binds_le_weaken : forall Γ1 Γ2 Γ3,
    denv_binds_le (Γ1 ++ Γ3) (Γ1 ++ Γ2 ++ Γ3).
Proof. intros Γ1 Γ2 Γ3 x b H. analyze_binds H. Qed.

Lemma denv_binds_le_weaken_l : forall Γ2 Γ, denv_binds_le Γ (Γ2 ++ Γ).
Proof. intros Γ2 Γ x b H. auto. Qed.

Lemma denv_tbinds_le_weaken : forall Γ1 Γ2 Γ3,
    denv_tbinds_le (Γ1 ++ Γ3) (Γ1 ++ Γ2 ++ Γ3).
Proof. intros. apply denv_tbinds_le_of_binds_le, denv_binds_le_weaken. Qed.

Lemma d_wf_ptyp_tvar_mono : forall Γ A,
    d_wf_ptyp Γ A -> forall Γ', denv_tbinds_le Γ Γ' -> d_wf_ptyp Γ' A.
Proof.
  intros Γ A H; induction H; intros Γ' Hle.
  - apply d_wf_ptyp__unit.
  - apply d_wf_ptyp__var. auto.
  - apply d_wf_ptyp__arrow; auto.
  - apply d_wf_ptyp__all with (L := L). intros α Hα.
    apply H0; [ exact Hα | apply denv_tbinds_le_cons; exact Hle ].
Qed.

Lemma d_wf_utyp_tvar_mono : forall Γ C,
    {{ Γ ⊢ᵤ C }}d -> forall Γ', denv_tbinds_le Γ Γ' -> {{ Γ' ⊢ᵤ C }}d.
Proof.
  intros Γ C H; induction H; intros Γ' Hle.
  - apply d_wf_utyp__unit.
  - apply d_wf_utyp__var. auto.
  - apply d_wf_utyp__arrow; auto.
  - apply d_wf_utyp__all_syn with (L := L). intros α Hα.
    apply H0; [ exact Hα | apply denv_tbinds_le_cons; exact Hle ].
  - apply d_wf_utyp__all_tag with (L := L). intros α Hα.
    apply H0; [ exact Hα | apply denv_tbinds_le_cons; exact Hle ].
Qed.

Lemma d_wf_ptyp_weakening : forall Γ1 Γ2 Γ3 A,
    d_wf_ptyp (Γ1 ++ Γ3) A ->
    d_wf_ptyp (Γ1 ++ Γ2 ++ Γ3) A.
Proof. intros. eapply d_wf_ptyp_tvar_mono; [ eassumption | apply denv_tbinds_le_weaken ]. Qed.

Lemma d_wf_utyp_weakening : forall Γ1 Γ2 Γ3 C,
    {{ (Γ1 ++ Γ3) ⊢ᵤ C }}d ->
    {{ (Γ1 ++ Γ2 ++ Γ3) ⊢ᵤ C }}d.
Proof. intros. eapply d_wf_utyp_tvar_mono; [ eassumption | apply denv_tbinds_le_weaken ]. Qed.

(** [d_wf_utyp] head-weakening (prepend a context). *)
Lemma d_wf_utyp_weakening_head : forall Γ' Γ C,
    {{ Γ ⊢ᵤ C }}d ->
    {{ (Γ' ++ Γ) ⊢ᵤ C }}d.
Proof.
  intros. eapply d_wf_utyp_tvar_mono;
    [ eassumption | apply denv_tbinds_le_of_binds_le, denv_binds_le_weaken_l ].
Qed.

Lemma d_wf_pskl_weakening : forall Γ1 Γ2 Γ3 Δ P,
    {{ (Γ1 ++ Γ3) ⨟ Δ ⊢ₚₛ P }}d ->
    {{ (Γ1 ++ Γ2 ++ Γ3) ⨟ Δ ⊢ₚₛ P }}d.
Proof. intros. eapply d_wf_pskl_tvar_mono; [ eassumption | apply denv_tbinds_le_weaken ]. Qed.

Lemma d_wf_uskl_weakening : forall Γ1 Γ2 Γ3 Δ R,
    {{ (Γ1 ++ Γ3) ⨟ Δ ⊢ᵤₛ R }}d ->
    {{ (Γ1 ++ Γ2 ++ Γ3) ⨟ Δ ⊢ᵤₛ R }}d.
Proof. intros. eapply d_wf_uskl_tvar_mono; [ eassumption | apply denv_tbinds_le_weaken ]. Qed.

(** Every free variable of a well-formed skeleton is a type variable of the
    context: a quantifier binds its variable in [Γ] as well as [Δ]. *)
Lemma d_wf_pskl_ftv : forall Γ Δ P,
    {{ Γ ⨟ Δ ⊢ₚₛ P }}d ->
    forall α, α `in` ftvar_in_pskl P -> binds α dbind_tvar Γ.
Proof.
  intros Γ Δ P H; induction H; intros β Hβ; simpl in Hβ.
  - fsetdec.
  - fsetdec.
  - assert (β = α) by fsetdec. subst. assumption.
  - destruct (union_1 Hβ); auto.
  - pick fresh α2 for (L `union` ftvar_in_pskl P `union` {{β}}).
    assert (HY' : β `in` ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f α2))).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_lower P (pskl_var_f α2)).
      fsetdec. }
    specialize (H0 α2 ltac:(fsetdec) β HY').
    apply binds_app_iff in H0. destruct H0 as [Hb | Hb]; [ | exact Hb ].
    apply binds_one_iff in Hb. destruct Hb as [-> _]. exfalso. fsetdec.
  - pose proof (IHd_wf_pskl β Hβ) as Hb. apply binds_denv_minus in Hb. tauto.
Qed.

Lemma d_wf_uskl_ftv : forall Γ Δ R,
    {{ Γ ⨟ Δ ⊢ᵤₛ R }}d ->
    forall α, α `in` ftvar_in_uskl R -> binds α dbind_tvar Γ.
Proof.
  intros Γ Δ R H; induction H; intros β Hβ; simpl in Hβ;
    try fsetdec.
  - assert (β = α) by fsetdec. subst. assumption.
  - destruct (union_1 Hβ); auto.
  - pick fresh α2 for (L `union` ftvar_in_uskl R `union` {{β}}).
    assert (HY' : β `in` ftvar_in_uskl (open_uskl_wrt_uskl R (uskl_var_f α2))).
    { pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f α2)).
      fsetdec. }
    specialize (H0 α2 ltac:(fsetdec) β HY').
    apply binds_app_iff in H0. destruct H0 as [Hb | Hb]; [ | exact Hb ].
    apply binds_one_iff in Hb. destruct Hb as [-> _]. exfalso. fsetdec.
  - pick fresh α2 for (L `union` ftvar_in_uskl R `union` {{β}}).
    assert (HY' : β `in` ftvar_in_uskl (open_uskl_wrt_uskl R (uskl_var_f α2))).
    { pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f α2)).
      fsetdec. }
    specialize (H0 α2 ltac:(fsetdec) β HY').
    apply binds_app_iff in H0. destruct H0 as [Hb | Hb]; [ | exact Hb ].
    apply binds_one_iff in Hb. destruct Hb as [-> _]. exfalso. fsetdec.
  - pose proof (IHd_wf_uskl β Hβ) as Hb. apply binds_denv_minus in Hb. tauto.
  - pose proof (IHd_wf_uskl β Hβ) as Hb. apply binds_denv_minus in Hb. tauto.
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

Lemma d_tags_subst_tvar : forall Ψ C α β,
    d_tags Ψ C ->
    d_tags Ψ (subst_utyp_in_utyp (utyp_var_f β) α C).
Proof.
  intros Ψ C α β H. induction H; simpl.
  - auto with fresco.
  - destruct_if; auto with fresco.
  - eauto with fresco.
  - inst_cofinites_for d_tags__all_tag Ψ0 := Ψ0; [ | assumption | assumption ].
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

Lemma d_consis_equiv : forall Ψ Ψo Γ C B,
    Ψ [=] Ψo -> {{ Ψ ⨟ Γ ⊢ C ∼ B }}d -> {{ Ψo ⨟ Γ ⊢ C ∼ B }}d.
Proof.
  intros Ψ Ψo Γ C B Heq H. revert Ψo Heq. induction H; intros Ψo Heq.
  - apply d_consis__unit. fsetdec.
  - apply d_consis__var; [ assumption | fsetdec ].
  - eapply d_consis__forall_inh_tagged; [ eassumption | fsetdec ].
  - apply d_consis__forall_inh_untagged with (L := L);
      intros α Hα; eauto.
  - apply d_consis__forall_syn_tagged with (L := L);
      intros α Hα; eauto.
  - apply d_consis__forall_syn with (L := L);
      intros α Hα; eauto.
  - eapply d_consis__arrow; [ eassumption | eassumption | fsetdec ].
Qed.

Lemma d_sub_equiv : forall m Ψ Ψo Γ C B,
    Ψ [=] Ψo -> {{ Ψ ⨟ Γ ⊢[ m ] C ⩽ B }}d -> {{ Ψo ⨟ Γ ⊢[ m ] C ⩽ B }}d.
Proof.
  intros m Ψ Ψo Γ C B Heq H. revert Ψo Heq. induction H; intros Ψo Heq.
  - apply d_sub__infer; [ assumption | assumption | fsetdec ].
  - apply d_sub__check; [ assumption | assumption | | assumption ].
    eapply d_consis_equiv; [ exact Heq | eassumption ].
  - apply d_sub__forall_r with (L := L);
      [ assumption | intros α Hα; eauto ].
  - eapply d_sub__arrow; [ eassumption | eassumption | fsetdec ].
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

(** A term binding recorded in a well-formed context is well-formed there
    (the binding's type is wf in the prefix; weaken to the whole context). *)
Lemma d_wf_denv_binds_ptyp : forall Γ x A,
    d_wf_denv Γ -> binds x (dbind_typ A) Γ -> d_wf_ptyp Γ A.
Proof.
  intros Γ x A Hwf. induction Hwf; intros Hb; try solve [ inversion Hb ];
    analyze_binds Hb;
    try (match goal with HV : dbind_typ _ = dbind_typ _ |- _ => inversion HV; subst end);
    (eapply d_wf_ptyp_tvar_mono; [ | apply denv_tbinds_le_of_binds_le, denv_binds_le_weaken_l ]);
    first [ eassumption | apply IHHwf; assumption ].
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
  - inst_cofinites_for d_wf_utyp__all_tag. intros α Hα. apply H0.
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
  - pick fresh α. apply (lc_utyp_all_tag_exists α). apply H0. auto.
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

(** Well-formed plain types are locally closed. *)
Lemma d_wf_ptyp_lc : forall Γ A, d_wf_ptyp Γ A -> lc_ptyp A.
Proof.
  intros Γ A H. induction H.
  - apply lc_ptyp_unit.
  - apply lc_ptyp_var_f.
  - apply lc_ptyp_arrow; assumption.
  - pick fresh α. apply (lc_ptyp_all_exists α). auto.
Qed.

Lemma d_wf_btyp_painting_syn : forall Γ A,
    d_wf_ptyp Γ A -> d_wf_btyp Γ (ptyp_to_btyp_syn A).
Proof.
  intros Γ A H. apply d_wf_btyp_of_lc_ftvar.
  - apply lc_ptyp_to_btyp_syn. eapply d_wf_ptyp_lc; eassumption.
  - rewrite ftvar_ptyp_to_btyp_syn. intros α Hα. eapply d_wf_ptyp_ftvar; eassumption.
Qed.

Lemma d_wf_btyp_painting_inh : forall Γ A,
    d_wf_ptyp Γ A -> d_wf_btyp Γ (ptyp_to_btyp_inh A).
Proof.
  intros Γ A H. apply d_wf_btyp_of_lc_ftvar.
  - apply lc_ptyp_to_btyp_inh. eapply d_wf_ptyp_lc; eassumption.
  - rewrite ftvar_ptyp_to_btyp_inh. intros α Hα. eapply d_wf_ptyp_ftvar; eassumption.
Qed.

Lemma d_wf_utyp_painting_syn : forall Γ A,
    d_wf_ptyp Γ A -> d_wf_utyp Γ (ptyp_to_utyp_syn A).
Proof.
  intros Γ A H. apply d_wf_utyp_of_lc_ftvar.
  - apply lc_ptyp_to_utyp_syn. eapply d_wf_ptyp_lc; eassumption.
  - rewrite ftvar_ptyp_to_utyp_syn. intros α Hα. eapply d_wf_ptyp_ftvar; eassumption.
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

(** The erasure's well-formedness gives back [B]'s — the [AbsAnno]/[App]
    cases recover [Barg]'s wf this way. *)
Lemma d_wf_btyp_of_wf_ptyp_erase : forall Γ B,
    d_wf_ptyp Γ (btyp_to_ptyp B) -> d_wf_btyp Γ B.
Proof.
  intros Γ B H. apply d_wf_btyp_of_lc_ftvar.
  - apply lc_btyp_of_lc_ptyp_erase. eapply d_wf_ptyp_lc; eassumption.
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

Lemma d_consis_wf : forall Ψ Γ C B,
    {{ Ψ ⨟ Γ ⊢ C ∼ B }}d -> d_wf_utyp Γ C -> d_wf_btyp Γ B.
Proof.
  intros Ψ Γ C B H. induction H; intros Hwf.
  - apply d_wf_btyp__unit.
  - apply d_wf_btyp__var. assumption.
  - (* forall_inh_tagged: utyp_all_tag ε C ∼ btyp_all_inh B *)
    inversion Hwf; subst. inst_cofinites_for d_wf_btyp__all_inh.
    intros α Hα. apply H0; auto.
  - (* forall_inh_untagged: utyp_all_syn C ∼ btyp_all_inh B *)
    inversion Hwf; subst. inst_cofinites_for d_wf_btyp__all_inh.
    intros α Hα. apply H0; auto.
  - (* forall_syn_tagged: utyp_all_tag ε C ∼ btyp_all_syn B *)
    inversion Hwf; subst. inst_cofinites_for d_wf_btyp__all_syn.
    intros α Hα. apply H0; auto.
  - (* forall_syn: utyp_all_syn C ∼ btyp_all_syn B *)
    inversion Hwf; subst. inst_cofinites_for d_wf_btyp__all_syn.
    intros α Hα. apply H0; auto.
  - inversion Hwf; subst. apply d_wf_btyp__arrow; auto.
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

(** …and hence a ∀ body, opened at an arbitrary well-formed [ph], is
    well-formed: the cofinite premise supplies it at ONE fresh variable and the
    substitution above moves it.  Every ForallL row wants this — [d_sub_wf]'s
    two below, and the TY-sort bridge's two (algo_decl/prop_conserv.v). *)
Lemma d_wf_utyp_open : forall L Γ C ph,
    (forall α, α `notin` L ->
       d_wf_utyp ((α ~ dbind_tvar) ++ Γ) (open_utyp_wrt_utyp C (utyp_var_f α))) ->
    d_wf_utyp Γ ph ->
    d_wf_utyp Γ (open_utyp_wrt_utyp C ph).
Proof.
  intros L Γ C ph Hcof Hph.
  pick fresh α for (L `union` dom Γ `union` ftvar_in_utyp C).
  rewrite (subst_utyp_in_utyp_intro α) by auto.
  apply d_wf_utyp_subst_tvar; auto.
Qed.

Lemma d_sub_wf : forall m Ψ Γ C B,
    {{ Ψ ⨟ Γ ⊢[ m ] C ⩽ B }}d -> d_wf_utyp Γ C -> d_wf_btyp Γ B.
Proof.
  intros m Ψ Γ C B H. induction H; intros Hwf.
  - (* infer *) eapply d_consis_wf; eassumption.
  - (* check *) eapply d_consis_wf; eassumption.
  - (* forall_r: C ⩽ btyp_all_inh B *)
    inst_cofinites_for d_wf_btyp__all_inh. intros α Hα.
    apply H1; auto. apply d_wf_utyp_weakening with (Γ1 := nil). simpl. assumption.
  - (* arg: utyp_arrow C1 C2 ⩽ btyp_arrow B1 B2 *)
    inversion Hwf; subst. apply d_wf_btyp__arrow.
    + eapply d_consis_wf; eassumption.
    + apply IHd_sub; assumption.
  - (* forall_l_tagged: utyp_all_tag ε C ⩽ B; recurse on opened body *)
    inversion Hwf; subst. apply IHd_sub. eapply d_wf_utyp_open; eassumption.
  - (* forall_l_untagged: utyp_all_syn C ⩽ B *)
    inversion Hwf; subst. apply IHd_sub. eapply d_wf_utyp_open; eassumption.
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
  - (* var *) apply d_wf_btyp_painting_syn. eapply d_wf_denv_binds_ptyp; eassumption.
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
Lemma d_sub_skmod : forall m Ψ Γ C B, {{ Ψ ⨟ Γ ⊢[ m ] C ⩽ B }}d -> mod_comp_ty B m.
Proof.
  intros m Ψ Γ C B H. induction H.
  - apply mod_comp_ty__ti; assumption.
  - apply mod_comp_ty__tc; assumption.
  - apply mod_comp_ty__tc; assumption.
  - apply mod_comp_ty__fn; assumption.
  - assumption.
  - assumption.
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

(** Consistency is reflexive on the synthesised painting: a
    well-formed [A] synthesises a [btyp] consistent with the
    [utyp] painting of the same [A] (empty tag context). *)
Lemma d_consis_syn_refl : forall Γ A,
    d_wf_ptyp Γ A ->
    {{ empty ⨟ Γ ⊢ ptyp_to_utyp_syn A ∼ ptyp_to_btyp_syn A }}d.
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
    rules (whose LHS is [utyp_all_tag], never produced by a painting), so
    consistency collapses to structural congruence.  This is what makes a
    variable's [mode_ti] type EXACTLY its binding painting, hence the
    extracted [d_sub] lands at the empty tag context demanded by
    [d_typing__sub]. *)
Lemma d_consis_paint_syn_eq : forall B,
    is_styp B ->
    forall Ψ Γ A, {{ Ψ ⨟ Γ ⊢ ptyp_to_utyp_syn A ∼ B }}d -> B = ptyp_to_btyp_syn A.
Proof.
  intros B Hstyp. induction Hstyp; intros Ψ Γ A Hc.
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
    specialize (H0 α ltac:(auto) Ψ ((α ~ dbind_tvar) ++ Γ)
                  (open_ptyp_wrt_ptyp A (ptyp_var_f α)) H5).
    rewrite ptyp_to_btyp_syn_open in H0. simpl in H0.
    apply open_btyp_wrt_btyp_inj with (α1 := α).
    + fsetdec.
    + match goal with |- context [ ftvar_in_btyp (ptyp_to_btyp_syn ?A0) ] =>
        rewrite (ftvar_ptyp_to_btyp_syn A0) end. fsetdec.
    + exact H0.
Qed.

