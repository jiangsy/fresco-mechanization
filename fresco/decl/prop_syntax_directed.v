Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.coercions.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_tag.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.decl.prop_wellformed.
Require Import src.fresco.decl.prop_ctx_mono.
Require Import src.fresco.decl.prop_renaming.
Require Import src.fresco.decl.prop_skeleton.
Require Import src.fresco.decl.prop_general_subsumption.

Lemma is_ityp_arrow_l : forall B1 B2, is_ityp (btyp_arrow B1 B2) -> is_ityp B1.
Proof. intros B1 B2 H. inversion H; assumption. Qed.
Lemma is_ityp_arrow_r : forall B1 B2, is_ityp (btyp_arrow B1 B2) -> is_ityp B2.
Proof. intros B1 B2 H. inversion H; assumption. Qed.
Lemma d_sd_typing_tc_abs_is_ityp : forall Γ e B,
    d_sd_typing mode_tc Γ (exp_abs e) B -> is_ityp B.
Proof.
  intros Γ e B H. dependent induction H.
  - exfalso; match goal with Hne : _ <> mode_tc |- _ => apply Hne; reflexivity end.
  - apply is_ityp__all with (L := L). intros α Hα. eauto.
  - apply is_ityp__arrow;
      [ apply is_ityp_ptyp_to_btyp_inh; eapply d_wf_ptyp_lc; eassumption | assumption ].
Qed.

Lemma d_sd_typing_tc_abs_anno_is_ityp : forall Γ A0 e B,
    d_sd_typing mode_tc Γ (exp_abs_anno A0 e) B -> is_ityp B.
Proof.
  intros Γ A0 e B H. dependent induction H.
  - exfalso; match goal with Hne : _ <> mode_tc |- _ => apply Hne; reflexivity end.
  - apply is_ityp__all with (L := L). intros α Hα. eauto.
  - apply is_ityp__arrow;
      [ apply is_ityp_ptyp_to_btyp_inh; eapply d_wf_ptyp_lc; eassumption | assumption ].
Qed.

Theorem d_sd_typing_sound : forall M Γ e B',
    d_sd_typing M Γ e B' -> d_typing M Γ e B'.
Proof.
  intros M Γ e B' H. induction H.
  -
    apply d_typing__sub with (A := ptyp_unit);
      [ apply d_typing__unit | assumption ].
  -
    apply d_typing__sub with (A := A);
      [ apply d_typing__var; assumption | assumption ].
  -
    apply d_typing__abs with (L := L) (A := A); assumption.
  -
    assert (Hit : is_ityp (btyp_all_inh B))
      by (eapply d_sd_typing_tc_abs_is_ityp; apply d_sd_typing__abs_check_step with (L := L); exact H).
    pose proof (ptyp_to_btyp_inh_btyp_to_ptyp Hit) as Hrt. simpl in Hrt. injection Hrt as Hrt.
    rewrite <- Hrt. apply d_typing__forall with (L := L) (A := btyp_to_ptyp B).
    + apply is_value__abs.
    + intros α Hα. rewrite Hrt. apply H0; assumption.
  -
    apply d_typing__abs with (L := L) (A := A);
      [ assumption
      | apply mod_comp_ty__tc; apply is_ityp__arrow;
          [ apply is_ityp_ptyp_to_btyp_inh; eapply d_wf_ptyp_lc; eassumption | assumption ]
      | assumption ].
  -
    apply d_typing__sub with (A := A);
      [ apply d_typing__anno; assumption | assumption ].
  -
    apply d_typing__abs_anno with (L := L) (A := A) (B1 := B1); assumption.
  -
    assert (Hit : is_ityp (btyp_all_inh B))
      by (eapply d_sd_typing_tc_abs_anno_is_ityp; apply d_sd_typing__abs_anno_check_step with (L := L); exact H).
    pose proof (ptyp_to_btyp_inh_btyp_to_ptyp Hit) as Hrt. simpl in Hrt. injection Hrt as Hrt.
    rewrite <- Hrt. apply d_typing__forall with (L := L) (A := btyp_to_ptyp B).
    + apply is_value__abs_anno.
    + intros α Hα. rewrite Hrt. apply H0; assumption.
  -
    apply d_typing__abs_anno with (L := L) (A := A) (B1 := ptyp_to_btyp_inh A).
    + assumption.
    + apply btyp_to_ptyp_ptyp_to_btyp_inh.
    + apply mod_comp_ty__tc; apply is_ityp__arrow;
        [ apply is_ityp_ptyp_to_btyp_inh; eapply d_wf_ptyp_lc; eassumption | assumption ].
    + assumption.
  - apply d_typing__freeze; assumption.
  -
    eapply d_typing__app; eassumption.
Qed.

Lemma is_ityp_subst_unit : forall B α, is_ityp B -> is_ityp (subst_btyp_in_btyp btyp_unit α B).
Proof.
  intros B α H. exact (@is_ityp_subst_mono B ptyp_unit α H mono_ptyp__unit).
Qed.

Lemma is_styp_subst_unit : forall B α, is_styp B -> is_styp (subst_btyp_in_btyp btyp_unit α B).
Proof.
  intros B α H. exact (@is_styp_subst_mono B ptyp_unit α H mono_ptyp__unit).
Qed.

Lemma guarded_btyp_subst_unit : forall B α, guarded_btyp B -> guarded_btyp (subst_btyp_in_btyp btyp_unit α B).
Proof.
  intros B α H. exact (@guarded_btyp_subst_mono B ptyp_unit α H mono_ptyp__unit).
Qed.

Lemma guarded_utyp_subst_unit : forall C α, guarded_utyp C -> guarded_utyp (subst_utyp_in_utyp utyp_unit α C).
Proof.
  intros C α H. exact (@guarded_utyp_subst_mono C ptyp_unit α H mono_ptyp__unit).
Qed.

Lemma is_dtyp_subst_unit : forall C α, is_dtyp C -> is_dtyp (subst_utyp_in_utyp utyp_unit α C).
Proof.
  intros C α H. exact (@is_dtyp_subst_mono C ptyp_unit α H mono_ptyp__unit).
Qed.

Lemma d_tags_subst_unit : forall Δ C α,
    d_tags Δ C ->
    d_tags Δ (subst_utyp_in_utyp utyp_unit α C).
Proof.
  intros Δ C α H. induction H; simpl.
  - auto with fresco.
  - destruct_if; auto with fresco.
  - eauto with fresco.
  - apply d_tags__all_tag with (L := L `union` {{α}}) (Ψ0 := Ψ0).
    + intros α2 Hα2.
      erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var
        by (solve [ fsetdec | apply lc_utyp_unit ]).
      apply H0; auto.
    + assumption.
    + assumption.
Qed.

Lemma d_wf_utyp_subst_unit : forall Γ C,
    {{ Γ ⊢ᵤ C }}d ->
    forall Γ1 α0 Γ2, Γ = Γ1 ++ (α0 ~ dbind_tvar) ++ Γ2 ->
    {{ (Γ1 ++ Γ2) ⊢ᵤ (subst_utyp_in_utyp utyp_unit α0 C) }}d.
Proof.
  intros Γ C H. induction H; intros Γ1 α0 Γ2 Heq; subst; simpl.
  - apply d_wf_utyp__unit.
  - destruct_if;
      [ apply d_wf_utyp__unit | apply d_wf_utyp__var; analyze_binds H ].
  - apply d_wf_utyp__arrow; [ eapply IHd_wf_utyp1 | eapply IHd_wf_utyp2 ]; reflexivity.
  - apply d_wf_utyp__all_syn with (L := L `union` dom (Γ1 ++ Γ2) `union` {{α0}}).
    intros α2 Hα2.
    rewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var by (first [ apply lc_utyp_unit | fsetdec ]).
    rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 α2); [ fsetdec | simpl_env; reflexivity ].
  - apply d_wf_utyp__all_tag with (L := L `union` dom (Γ1 ++ Γ2) `union` {{α0}}).
    intros α2 Hα2.
    rewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var by (first [ apply lc_utyp_unit | fsetdec ]).
    rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 α2); [ fsetdec | simpl_env; reflexivity ].
Qed.

Lemma d_sub_subst_unit : forall m Ψ Γ C B,
    {{ Ψ ⨟ Γ ⊢[ m ] C ⩽ B }}d ->
    forall Γ1 Γ2 α0,
      Γ = Γ1 ++ (α0 ~ dbind_tvar) ++ Γ2 ->
      {{ Ψ ⨟ (Γ1 ++ Γ2) ⊢[ m ]
        (subst_utyp_in_utyp utyp_unit α0 C) ⩽ (subst_btyp_in_btyp btyp_unit α0 B) }}d.
Proof.
  intros m Ψ Γ C B H. induction H; intros Γ1 Γ2 α0 Heq; subst; simpl.
  -
    apply d_sub__infer; [ | apply is_styp_subst_unit; assumption | assumption ].
    change btyp_unit with (utyp_to_btyp utyp_unit).
    eapply d_consis_subst_tvar;
      [ eassumption | reflexivity | apply d_wf_utyp__unit | apply is_dtyp__unit ].
  -
    apply d_sub__check;
      [ apply guarded_utyp_subst_unit; assumption
      | apply guarded_btyp_subst_unit; assumption
      | change btyp_unit with (utyp_to_btyp utyp_unit);
        eapply d_consis_subst_tvar;
          [ eassumption | reflexivity | apply d_wf_utyp__unit | apply is_dtyp__unit ]
      | apply is_ityp_subst_unit; assumption ].
  -
    apply d_sub__forall_r with (L := L `union` dom (Γ1 ++ Γ2) `union` singleton α0).
    intros α2 Hα2.
    rewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var
      by (first [ apply lc_btyp_unit | fsetdec ]).
    rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 α2); [ fsetdec | simpl_env; reflexivity ].
  -
    eapply d_sub__arrow.
    + change btyp_unit with (utyp_to_btyp utyp_unit).
      eapply d_consis_subst_tvar;
        [ eassumption | reflexivity | apply d_wf_utyp__unit | apply is_dtyp__unit ].
    + eapply IHd_sub; reflexivity.
    + assumption.
  -
    eapply d_sub__forall_l_tagged with
      (Ψ' := Ψ') (ph := subst_utyp_in_utyp utyp_unit α0 ph);
      [ assumption | assumption
      |
        change (utyp_all_tag ε (subst_utyp_in_utyp utyp_unit α0 C))
          with (subst_utyp_in_utyp utyp_unit α0 (utyp_all_tag ε C));
        rewrite ftag_in_utyp_subst_tagfree by reflexivity; assumption
      | apply d_tags_subst_unit; assumption
      | eapply d_wf_utyp_subst_unit; [ eassumption | reflexivity ]
      | apply is_dtyp_subst_unit; assumption
      | ].
    rewrite <- subst_utyp_in_utyp_open_utyp_wrt_utyp by (apply lc_utyp_unit).
    eapply IHd_sub; reflexivity.
  -
    eapply d_sub__forall_l_untagged with
      (Ψ' := Ψ') (ph := subst_utyp_in_utyp utyp_unit α0 ph);
      [ assumption | assumption
      |
        change (utyp_all_syn (subst_utyp_in_utyp utyp_unit α0 C))
          with (subst_utyp_in_utyp utyp_unit α0 (utyp_all_syn C));
        rewrite ftag_in_utyp_subst_tagfree by reflexivity; assumption
      | apply d_tags_subst_unit; assumption
      | eapply d_wf_utyp_subst_unit; [ eassumption | reflexivity ]
      | apply is_dtyp_subst_unit; assumption
      | ].
    rewrite <- subst_utyp_in_utyp_open_utyp_wrt_utyp by (apply lc_utyp_unit).
    eapply IHd_sub; reflexivity.
Qed.

Lemma is_iskl_subst_unit : forall Q α,
    is_iskl Q -> is_iskl (subst_bskl_in_bskl bskl_unit α Q).
Proof.
  intros Q α H. exact (@is_iskl_subst_mono Q ptyp_unit α H mono_ptyp__unit).
Qed.

Lemma d_refine_syn_subst_unit : forall Γ Δ Q Q',
    {{ Γ ⨟ Δ ⊢ᵣ Q ⊳ Q' }}d ->
    forall Γ' α0,
    {{ Γ' ⨟ Δ ⊢ᵣ
      (subst_bskl_in_bskl bskl_unit α0 Q) ⊳ (subst_bskl_in_bskl bskl_unit α0 Q') }}d.
Proof.
  intros Γ Δ Q Q' H. induction H; intros Γ' α0; simpl.
  - apply d_refine_syn__unit.
  - destruct_if.
    + apply d_refine_syn__unit.
    + apply d_refine_syn__var.
  - apply d_refine_syn__arrow; [ exact (@is_iskl_subst_unit _ α0 H) | auto | auto ].
  - apply d_refine_syn__all with (L := L `union` {{α0}}).
    { exact (@is_iskl_subst_unit _ α0 H). }
    intros α2 Hα2.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var
      by (first [ apply lc_bskl_unit | fsetdec ]).
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var
      by (first [ apply lc_bskl_unit | fsetdec ]).
    apply H1. fsetdec.
  - rewrite pskl_to_bskl_syn_subst_unit. apply d_refine_syn__ghost.
    pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P pskl_unit α0) as Hup.
    simpl in Hup. clear - H Hup. fsetdec.
  - apply d_refine_syn__univ_ghost_remove; [ exact (@is_iskl_subst_unit _ α0 H) | auto ].
  - apply d_refine_syn__univ_ghost_fill with (L := L `union` {{α0}}).
    { exact (@is_iskl_subst_unit _ α0 H). }
    intros α2 Hα2.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var
      by (first [ apply lc_bskl_unit | fsetdec ]).
    apply H1. fsetdec.
  - apply d_refine_syn__univ_ghost_keep; [ exact (@is_iskl_subst_unit _ α0 H) | auto ].
Qed.

Definition tvar_clean (α0 : atom) (Γ : list (atom * dbind)) : Prop :=
  (forall x A, binds x (dbind_typ A) Γ -> α0 `notin` ftvar_in_ptyp A) /\
  (forall x P, binds x (dbind_skl P) Γ -> α0 `notin` ftvar_in_pskl P).

Definition subst_unit_dbind (α0 : atom) (d : dbind) : dbind :=
  match d with
  | dbind_tvar => dbind_tvar
  | dbind_typ A => dbind_typ (subst_ptyp_in_ptyp ptyp_unit α0 A)
  | dbind_skl P => dbind_skl (subst_pskl_in_pskl pskl_unit α0 P)
  end.

Lemma map_subst_unit_dbind_cons : forall x d α0 Γ1,
    (x ~ subst_unit_dbind α0 d) ++ map (subst_unit_dbind α0) Γ1
    = map (subst_unit_dbind α0) ((x ~ d) ++ Γ1).
Proof. intros. simpl_env. reflexivity. Qed.

Lemma denv_tbinds_le_map_subst_unit : forall α0 Γ1 Γ2,
    denv_tbinds_le (Γ1 ++ Γ2) (map (subst_unit_dbind α0) Γ1 ++ Γ2).
Proof.
  intros α0 Γ1 Γ2 α Hb. apply binds_app_iff in Hb; apply binds_app_iff.
  destruct Hb as [Hb | Hb]; [ left | right; assumption ].
  change dbind_tvar with (subst_unit_dbind α0 dbind_tvar). apply binds_map_2. assumption.
Qed.

Lemma binds_typ_subst_unit_dbind : forall x A α0 Γ1 Γ2,
    binds x (dbind_typ A) (Γ1 ++ Γ2) -> tvar_clean α0 Γ2 ->
    binds x (dbind_typ (subst_ptyp_in_ptyp ptyp_unit α0 A))
          (map (subst_unit_dbind α0) Γ1 ++ Γ2).
Proof.
  intros x A α0 Γ1 Γ2 Hb [Ht Hs]. apply binds_app_iff in Hb. destruct Hb as [Hb | Hb].
  - apply binds_app_2.
    change (dbind_typ (subst_ptyp_in_ptyp ptyp_unit α0 A))
      with (subst_unit_dbind α0 (dbind_typ A)).
    apply binds_map_2. assumption.
  - apply binds_app_3.
    rewrite (subst_ptyp_in_ptyp_fresh_eq _ _ _ (Ht _ _ Hb)). assumption.
Qed.

Lemma binds_skl_subst_unit_dbind : forall x P α0 Γ1 Γ2,
    binds x (dbind_skl P) (Γ1 ++ Γ2) -> tvar_clean α0 Γ2 ->
    binds x (dbind_skl (subst_pskl_in_pskl pskl_unit α0 P))
          (map (subst_unit_dbind α0) Γ1 ++ Γ2).
Proof.
  intros x P α0 Γ1 Γ2 Hb [Ht Hs]. apply binds_app_iff in Hb. destruct Hb as [Hb | Hb].
  - apply binds_app_2.
    change (dbind_skl (subst_pskl_in_pskl pskl_unit α0 P))
      with (subst_unit_dbind α0 (dbind_skl P)).
    apply binds_map_2. assumption.
  - apply binds_app_3.
    rewrite (subst_pskl_in_pskl_fresh_eq _ _ _ (Hs _ _ Hb)). assumption.
Qed.

Lemma d_wf_ptyp_subst_unit_ctx : forall Γ A,
    {{ Γ ⊢ₚ A }}d -> forall Γ1 α0 Γ2, Γ = Γ1 ++ (α0 ~ dbind_tvar) ++ Γ2 ->
    {{ (map (subst_unit_dbind α0) Γ1 ++ Γ2) ⊢ₚ (subst_ptyp_in_ptyp ptyp_unit α0 A) }}d.
Proof.
  intros Γ A H Γ1 α0 Γ2 Heq.
  apply d_wf_ptyp_of_lc_ftvar.
  - apply subst_ptyp_in_ptyp_lc_ptyp; [ eapply d_wf_ptyp_lc; eassumption | apply lc_ptyp_unit ].
  - intros β Hβ.
    pose proof (ftvar_in_ptyp_subst_ptyp_in_ptyp_upper A ptyp_unit α0) as Hup.
    simpl in Hup.
    assert (HYA : β `in` ftvar_in_ptyp A) by (clear - Hβ Hup; fsetdec).
    assert (HYne : β <> α0).
    { clear - Hβ Hup. intro; subst. assert (α0 `notin` (remove α0 (ftvar_in_ptyp A))) by fsetdec. fsetdec. }
    assert (Hbnd : binds β dbind_tvar Γ) by (eapply d_wf_ptyp_ftvar; eassumption).
    subst Γ.

    assert (Hbnd' : binds β dbind_tvar (Γ1 ++ Γ2)).
    { analyze_binds Hbnd. }
    apply denv_tbinds_le_map_subst_unit. assumption.
Qed.

Lemma d_pat_subst_unit : forall m Γ e Q,
    {{ Γ ⊢ˢ[ m ] e ⦂ Q }}d ->
    forall Γ1 α0 Γ2, Γ = Γ1 ++ (α0 ~ dbind_tvar) ++ Γ2 ->
    tvar_clean α0 Γ2 ->
    {{ (map (subst_unit_dbind α0) Γ1 ++ Γ2) ⊢ˢ[ m ]
      (subst_ptyp_in_exp ptyp_unit α0 e) ⦂ (subst_bskl_in_bskl bskl_unit α0 Q) }}d.
Proof.
  intros m Γ e Q H. induction H; intros Γ1 α0 Γ2 Heq Hclean; subst; simpl.
  -
    apply d_pat__unit;
    [
      rewrite bskl_to_pskl_subst_unit;
      eapply d_wf_pskl_tvar_mono;
        [ eapply d_wf_pskl_subst_unit; [ eassumption | reflexivity ]
        | apply denv_tbinds_le_map_subst_unit ] | ].
    change uskl_unit with (subst_uskl_in_uskl uskl_unit α0 uskl_unit).
    eapply d_pat_sub_tvar_mono;
      [ eapply d_pat_sub_subst_unit; [ eassumption | reflexivity ]
      | apply denv_tbinds_le_map_subst_unit ].
  -
    destruct d as [ | A | P0 ]; simpl in H0.
    + discriminate.
    + injection H0 as H0. subst P.
      assert (Hb : binds x (dbind_typ A) (Γ1 ++ Γ2)) by (analyze_binds H).
      eapply d_pat__var with (d := dbind_typ (subst_ptyp_in_ptyp ptyp_unit α0 A));
        [ apply binds_typ_subst_unit_dbind; eassumption
        | reflexivity
        |
      rewrite bskl_to_pskl_subst_unit;
      eapply d_wf_pskl_tvar_mono;
        [ eapply d_wf_pskl_subst_unit; [ eassumption | reflexivity ]
        | apply denv_tbinds_le_map_subst_unit ] | ].
      rewrite <- ptyp_to_pskl_subst_unit.
      rewrite <- pskl_to_bskl_syn_subst_unit.
      rewrite <- bskl_to_uskl_subst_unit.
      eapply d_pat_sub_tvar_mono;
        [ eapply d_pat_sub_subst_unit; [ eassumption | reflexivity ]
        | apply denv_tbinds_le_map_subst_unit ].
    + injection H0 as H0. subst P.
      assert (Hb : binds x (dbind_skl P0) (Γ1 ++ Γ2)) by (analyze_binds H).
      eapply d_pat__var with (d := dbind_skl (subst_pskl_in_pskl pskl_unit α0 P0));
        [ apply binds_skl_subst_unit_dbind; eassumption
        | reflexivity
        |
      rewrite bskl_to_pskl_subst_unit;
      eapply d_wf_pskl_tvar_mono;
        [ eapply d_wf_pskl_subst_unit; [ eassumption | reflexivity ]
        | apply denv_tbinds_le_map_subst_unit ] | ].
      rewrite <- pskl_to_bskl_syn_subst_unit.
      rewrite <- bskl_to_uskl_subst_unit.
      eapply d_pat_sub_tvar_mono;
        [ eapply d_pat_sub_subst_unit; [ eassumption | reflexivity ]
        | apply denv_tbinds_le_map_subst_unit ].
  -
    apply d_pat__anno.
    +
      rewrite bskl_to_pskl_subst_unit;
      eapply d_wf_pskl_tvar_mono;
        [ eapply d_wf_pskl_subst_unit; [ eassumption | reflexivity ]
        | apply denv_tbinds_le_map_subst_unit ].
    + rewrite <- ptyp_to_pskl_subst_unit.
      rewrite <- pskl_to_bskl_syn_subst_unit.
      rewrite <- bskl_to_uskl_subst_unit.
      eapply d_pat_sub_tvar_mono;
        [ eapply d_pat_sub_subst_unit; [ eassumption | reflexivity ]
        | apply denv_tbinds_le_map_subst_unit ].
  -
    rewrite pskl_to_bskl_syn_subst_unit.
    apply d_pat__freeze. rewrite <- pskl_to_bskl_syn_subst_unit.
    eapply IHd_pat; [ reflexivity | assumption ].
  -
    rewrite pskl_to_bskl_inh_subst_unit.
    apply d_pat__abs with (L := L `union` {{α0}}) (P := subst_pskl_in_pskl pskl_unit α0 P).
    + assumption.
    + eapply d_wf_pskl_tvar_mono;
        [ eapply d_wf_pskl_subst_unit; [ eassumption | reflexivity ]
        | apply denv_tbinds_le_map_subst_unit ].
    +
      pose proof (mod_comp_sk_subst_unit α0 H1) as Hm.
      cbn [subst_bskl_in_bskl] in Hm.
      rewrite pskl_to_bskl_inh_subst_unit in Hm. exact Hm.
    + intros x Hx.
      rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var by (first [ apply lc_ptyp_unit | fsetdec ]).
      rewrite_env (((x ~ subst_unit_dbind α0 (dbind_skl P)) ++ map (subst_unit_dbind α0) Γ1) ++ Γ2).
      rewrite map_subst_unit_dbind_cons.
      eapply (H3 x ltac:(solve_notin_auto) ((x ~ dbind_skl P) ++ Γ1) α0 Γ2);
        [ simpl_env; reflexivity | assumption ].
  -
    rewrite btyp_to_bskl_subst_unit.
    eapply d_pat__abs_anno with (L := L `union` {{α0}}).
    + assumption.
    + eapply d_wf_ptyp_subst_unit_ctx; [ eassumption | reflexivity ].
    + symmetry. apply btyp_to_ptyp_subst_unit.
    +
      pose proof (mod_comp_sk_subst_unit α0 H2) as Hm.
      cbn [subst_bskl_in_bskl] in Hm.
      rewrite btyp_to_bskl_subst_unit in Hm. exact Hm.
    + intros x Hx.
      rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var by (first [ apply lc_ptyp_unit | fsetdec ]).
      rewrite_env (((x ~ subst_unit_dbind α0 (dbind_typ (btyp_to_ptyp B))) ++ map (subst_unit_dbind α0) Γ1) ++ Γ2).
      rewrite map_subst_unit_dbind_cons.
      eapply (H4 x ltac:(solve_notin_auto) ((x ~ dbind_typ (btyp_to_ptyp B)) ++ Γ1) α0 Γ2);
        [ simpl_env; reflexivity | assumption ].
  -
    rewrite pskl_to_bskl_syn_subst_unit.
    apply d_pat__abs_check with (L := L `union` {{α0}}) (P := subst_pskl_in_pskl pskl_unit α0 P).
    intros x Hx.
    rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var by (first [ apply lc_ptyp_unit | fsetdec ]).
    rewrite_env (((x ~ subst_unit_dbind α0 (dbind_skl pskl_ghost)) ++ map (subst_unit_dbind α0) Γ1) ++ Γ2).
    rewrite map_subst_unit_dbind_cons.
    rewrite <- pskl_to_bskl_syn_subst_unit.
    eapply (H0 x ltac:(solve_notin_auto) ((x ~ dbind_skl pskl_ghost) ++ Γ1) α0 Γ2);
      [ simpl_env; reflexivity | assumption ].
  -
    rewrite btyp_to_bskl_subst_unit. rewrite ptyp_to_btyp_syn_subst_unit.
    rewrite pskl_to_bskl_syn_subst_unit.
    apply d_pat__abs_anno_check with (L := L `union` {{α0}})
      (A := subst_ptyp_in_ptyp ptyp_unit α0 A) (P := subst_pskl_in_pskl pskl_unit α0 P).
    + eapply d_wf_ptyp_subst_unit_ctx; [ eassumption | reflexivity ].
    + intros x Hx.
      rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var by (first [ apply lc_ptyp_unit | fsetdec ]).
      rewrite_env (((x ~ subst_unit_dbind α0 (dbind_typ A)) ++ map (subst_unit_dbind α0) Γ1) ++ Γ2).
      rewrite map_subst_unit_dbind_cons.
      rewrite <- pskl_to_bskl_syn_subst_unit.
      eapply (H1 x ltac:(solve_notin_auto) ((x ~ dbind_typ A) ++ Γ1) α0 Γ2);
        [ simpl_env; reflexivity | assumption ].
  -
    eapply d_pat__app.
    + rewrite <- pskl_to_bskl_syn_subst_unit. eapply IHd_pat1; [ reflexivity | assumption ].
    + rewrite <- pskl_to_bskl_inh_subst_unit.
      eapply d_refine_syn_subst_unit; eassumption.
    + change (bskl_arrow (subst_bskl_in_bskl bskl_unit α0 Q1) (subst_bskl_in_bskl bskl_unit α0 Q2))
        with (subst_bskl_in_bskl bskl_unit α0 (bskl_arrow Q1 Q2)).
      eapply IHd_pat2; [ reflexivity | assumption ].
Qed.

Lemma mod_comp_ty_subst_unit : forall B m α0,
    mod_comp_ty B m -> mod_comp_ty (subst_btyp_in_btyp btyp_unit α0 B) m.
Proof.
  intros B m α0 H. exact (@mod_comp_ty_subst_mono B m ptyp_unit α0 H mono_ptyp__unit).
Qed.

Lemma d_sd_typing_subst_unit : forall m Γ e B,
    d_sd_typing m Γ e B ->
    forall Γ1 α0 Γ2, Γ = Γ1 ++ (α0 ~ dbind_tvar) ++ Γ2 ->
    tvar_clean α0 Γ2 ->
    d_sd_typing m (map (subst_unit_dbind α0) Γ1 ++ Γ2)
      (subst_ptyp_in_exp ptyp_unit α0 e) (subst_btyp_in_btyp btyp_unit α0 B).
Proof.
  intros m Γ e B H. induction H; intros Γ1 α0 Γ2 Heq Hclean; subst; simpl.
  -
    apply d_sd_typing__unit.
    change (ptyp_to_utyp_syn ptyp_unit)
      with (subst_utyp_in_utyp utyp_unit α0 (ptyp_to_utyp_syn ptyp_unit)).
    eapply d_sub_tvar_mono;
      [ eapply d_sub_subst_unit; [ eassumption | reflexivity ]
      | apply denv_tbinds_le_map_subst_unit ].
  -
    apply d_sd_typing__var with (A := subst_ptyp_in_ptyp ptyp_unit α0 A).
    + assert (Hb : binds x (dbind_typ A) (Γ1 ++ Γ2)) by (analyze_binds H).
      apply binds_typ_subst_unit_dbind; assumption.
    + rewrite <- ptyp_to_utyp_syn_subst_unit.
      eapply d_sub_tvar_mono;
        [ eapply d_sub_subst_unit; [ eassumption | reflexivity ]
        | apply denv_tbinds_le_map_subst_unit ].
  -
    rewrite ptyp_to_btyp_inh_subst_unit.
    apply d_sd_typing__abs with (L := L `union` {{α0}}).
    + assumption.
    + eapply d_wf_ptyp_subst_unit_ctx; [ eassumption | reflexivity ].
    + rewrite <- ptyp_to_btyp_inh_subst_unit.
      change (btyp_arrow (subst_btyp_in_btyp btyp_unit α0 (ptyp_to_btyp_inh A))
                         (subst_btyp_in_btyp btyp_unit α0 B))
        with (subst_btyp_in_btyp btyp_unit α0 (btyp_arrow (ptyp_to_btyp_inh A) B)).
      apply mod_comp_ty_subst_unit. assumption.
    + intros x Hx.
      rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var by (first [ apply lc_ptyp_unit | fsetdec ]).
      rewrite_env (((x ~ subst_unit_dbind α0 (dbind_typ A)) ++ map (subst_unit_dbind α0) Γ1) ++ Γ2).
      rewrite map_subst_unit_dbind_cons.
      eapply (H3 x ltac:(solve_notin_auto) ((x ~ dbind_typ A) ++ Γ1) α0 Γ2);
        [ simpl_env; reflexivity | assumption ].
  -
    apply d_sd_typing__abs_check_step with (L := L `union` {{α0}}).
    intros α Hα.
    rewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var by (first [ apply lc_btyp_unit | fsetdec ]).
    rewrite_env (((α ~ subst_unit_dbind α0 dbind_tvar) ++ map (subst_unit_dbind α0) Γ1) ++ Γ2).
    rewrite map_subst_unit_dbind_cons.
    eapply (H0 α ltac:(solve_notin_auto) ((α ~ dbind_tvar) ++ Γ1) α0 Γ2);
      [ simpl_env; reflexivity | assumption ].
  -
    rewrite ptyp_to_btyp_inh_subst_unit.
    apply d_sd_typing__abs_check_base with (L := L `union` {{α0}}).
    + eapply d_wf_ptyp_subst_unit_ctx; [ eassumption | reflexivity ].
    + apply is_ityp_subst_unit. assumption.
    + intros x Hx.
      rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var by (first [ apply lc_ptyp_unit | fsetdec ]).
      rewrite_env (((x ~ subst_unit_dbind α0 (dbind_typ A)) ++ map (subst_unit_dbind α0) Γ1) ++ Γ2).
      rewrite map_subst_unit_dbind_cons.
      eapply (H2 x ltac:(solve_notin_auto) ((x ~ dbind_typ A) ++ Γ1) α0 Γ2);
        [ simpl_env; reflexivity | assumption ].
  -
    eapply d_sd_typing__anno.
    + rewrite <- ptyp_to_btyp_inh_subst_unit.
      eapply IHd_sd_typing; [ reflexivity | assumption ].
    + rewrite <- ptyp_to_utyp_syn_subst_unit.
      eapply d_sub_tvar_mono;
        [ eapply d_sub_subst_unit; [ eassumption | reflexivity ]
        | apply denv_tbinds_le_map_subst_unit ].
  -
    apply d_sd_typing__abs_anno with (L := L `union` {{α0}})
      (B1 := subst_btyp_in_btyp btyp_unit α0 B1).
    + assumption.
    + eapply d_wf_ptyp_subst_unit_ctx; [ eassumption | reflexivity ].
    + symmetry. apply btyp_to_ptyp_subst_unit.
    + pose proof (mod_comp_ty_subst_unit (btyp_arrow B1 B2) m α0 H2) as Hsk. simpl in Hsk. exact Hsk.
    + intros x Hx.
      rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var by (first [ apply lc_ptyp_unit | fsetdec ]).
      rewrite_env (((x ~ subst_unit_dbind α0 (dbind_typ (btyp_to_ptyp B1))) ++ map (subst_unit_dbind α0) Γ1) ++ Γ2).
      rewrite map_subst_unit_dbind_cons.
      eapply (H4 x ltac:(solve_notin_auto) ((x ~ dbind_typ (btyp_to_ptyp B1)) ++ Γ1) α0 Γ2);
        [ simpl_env; reflexivity | assumption ].
  -
    apply d_sd_typing__abs_anno_check_step with (L := L `union` {{α0}}).
    intros α Hα.
    rewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var by (first [ apply lc_btyp_unit | fsetdec ]).
    rewrite_env (((α ~ subst_unit_dbind α0 dbind_tvar) ++ map (subst_unit_dbind α0) Γ1) ++ Γ2).
    rewrite map_subst_unit_dbind_cons.
    eapply (H0 α ltac:(solve_notin_auto) ((α ~ dbind_tvar) ++ Γ1) α0 Γ2);
      [ simpl_env; reflexivity | assumption ].
  -
    rewrite ptyp_to_btyp_inh_subst_unit.
    apply d_sd_typing__abs_anno_check_base with (L := L `union` {{α0}}).
    + eapply d_wf_ptyp_subst_unit_ctx; [ eassumption | reflexivity ].
    + apply is_ityp_subst_unit. assumption.
    + intros x Hx.
      rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var by (first [ apply lc_ptyp_unit | fsetdec ]).
      rewrite_env (((x ~ subst_unit_dbind α0 (dbind_typ A)) ++ map (subst_unit_dbind α0) Γ1) ++ Γ2).
      rewrite map_subst_unit_dbind_cons.
      eapply (H2 x ltac:(solve_notin_auto) ((x ~ dbind_typ A) ++ Γ1) α0 Γ2);
        [ simpl_env; reflexivity | assumption ].
  -
    rewrite ptyp_to_btyp_inh_subst_unit.
    apply d_sd_typing__freeze. rewrite <- ptyp_to_btyp_syn_subst_unit.
    eapply IHd_sd_typing; [ reflexivity | assumption ].
  -
    eapply d_sd_typing__app.
    + rewrite <- pskl_to_bskl_syn_subst_unit.
      eapply d_pat_subst_unit; [ eassumption | reflexivity | assumption ].
    + rewrite <- btyp_to_bskl_subst_unit. rewrite <- pskl_to_bskl_inh_subst_unit.
      eapply d_refine_syn_subst_unit; eassumption.
    + change (btyp_arrow (subst_btyp_in_btyp btyp_unit α0 B1)
                         (subst_btyp_in_btyp btyp_unit α0 B2))
        with (subst_btyp_in_btyp btyp_unit α0 (btyp_arrow B1 B2)).
      eapply IHd_sd_typing1; [ reflexivity | assumption ].
    + rewrite <- btyp_to_ptyp_subst_unit. rewrite <- ptyp_to_btyp_inh_subst_unit.
      eapply IHd_sd_typing2; [ reflexivity | assumption ].
Qed.

Definition ftvar_in_dbind (d : dbind) : atoms :=
  match d with
  | dbind_tvar => empty
  | dbind_typ A => ftvar_in_ptyp A
  | dbind_skl P => ftvar_in_pskl P
  end.

Fixpoint ftvar_in_denv (Γ : list (atom * dbind)) : atoms :=
  match Γ with
  | nil => empty
  | (_, d) :: Γ' => ftvar_in_dbind d `union` ftvar_in_denv Γ'
  end.

Lemma ftvar_in_denv_binds_typ : forall x A Γ,
    binds x (dbind_typ A) Γ -> ftvar_in_ptyp A [<=] ftvar_in_denv Γ.
Proof.
  induction Γ as [ | [y d] Γ' IH ]; intros Hb; simpl.
  - analyze_binds Hb.
  - analyze_binds Hb.
    + simpl. fsetdec.
    + apply IH in BindsTac. fsetdec.
Qed.

Lemma ftvar_in_denv_binds_skl : forall x P Γ,
    binds x (dbind_skl P) Γ -> ftvar_in_pskl P [<=] ftvar_in_denv Γ.
Proof.
  induction Γ as [ | [y d] Γ' IH ]; intros Hb; simpl.
  - analyze_binds Hb.
  - analyze_binds Hb.
    + simpl. fsetdec.
    + apply IH in BindsTac. fsetdec.
Qed.

Lemma tvar_clean_fresh : forall α Γ,
    α `notin` ftvar_in_denv Γ -> tvar_clean α Γ.
Proof.
  intros α Γ Hα. split; intros y T Hb.
  - apply ftvar_in_denv_binds_typ in Hb. fsetdec.
  - apply ftvar_in_denv_binds_skl in Hb. fsetdec.
Qed.

Lemma d_sd_typing_forall_admissible : forall L Γ V B,
    is_value V ->
    (forall α, α `notin` L ->
       d_sd_typing mode_tc ((α ~ dbind_tvar) ++ Γ) V (open_btyp_wrt_btyp B (btyp_var_f α))) ->
    d_sd_typing mode_tc Γ V (btyp_all_inh B).
Proof.
  intros L Γ V B Hv IH.
  inversion Hv; subst.
  -
    pick fresh α0 for (L `union` dom Γ `union` ftvar_in_btyp B).
    pose proof (IH α0 ltac:(solve_notin_auto)) as IH0. inversion IH0; subst.
    match goal with
    | Hs : {{ empty ⨟ _ ⊢[ mode_tc ] ptyp_to_utyp_syn ptyp_unit ⩽ _ }}d |- _ =>
        rename Hs into Hs0
    end.
    apply d_sd_typing__unit.
    apply d_sub__forall_r with (L := dom Γ `union` {{α0}} `union` ftvar_in_btyp B).
    intros α Hα.
    pose proof (d_sub_rename_tvar (β := α) Hs0 nil Γ α0
                  ltac:(reflexivity) ltac:(simpl; solve_notin_auto)) as Hren.
    simpl in Hren.

    rewrite <- (subst_btyp_in_btyp_intro α0 B (btyp_var_f α)) in Hren by fsetdec.
    exact Hren.
  -
    pick fresh α0 for (L `union` dom Γ `union` ftvar_in_btyp B `union` ftvar_in_denv Γ).
    pose proof (IH α0 ltac:(solve_notin_auto)) as IH0. inversion IH0; subst.
    match goal with
    | Hb : binds _ (dbind_typ _) ((α0 ~ dbind_tvar) ++ Γ),
      Hs : {{ empty ⨟ _ ⊢[ mode_tc ] ptyp_to_utyp_syn _ ⩽ _ }}d |- _ =>
        rename Hb into Hb0; rename Hs into Hs0
    end.
    match goal with
    | Hb0' : binds _ (dbind_typ ?AA) ((α0 ~ dbind_tvar) ++ Γ) |- _ =>
        assert (HbΓ : binds x (dbind_typ AA) Γ) by (analyze_binds Hb0');
        assert (HX0A : α0 `notin` ftvar_in_ptyp AA)
          by (pose proof (ftvar_in_denv_binds_typ _ _ _ HbΓ); fsetdec)
    end.
    eapply d_sd_typing__var; [ exact HbΓ | ].
    apply d_sub__forall_r with (L := dom Γ `union` {{α0}} `union` ftvar_in_btyp B).
    intros α Hα.
    pose proof (d_sub_rename_tvar (β := α) Hs0 nil Γ α0
                  ltac:(reflexivity) ltac:(simpl; solve_notin_auto)) as Hren.
    simpl in Hren.
    rewrite (subst_utyp_in_utyp_fresh_eq _ (utyp_var_f α) α0)
      in Hren by (rewrite ftvar_ptyp_to_utyp_syn; exact HX0A).
    rewrite <- (subst_btyp_in_btyp_intro α0 B (btyp_var_f α)) in Hren by fsetdec.
    exact Hren.
  -
    apply d_sd_typing__abs_check_step with (L := L); assumption.
  -
    apply d_sd_typing__abs_anno_check_step with (L := L); assumption.
  -
    pick fresh α0 for (L `union` dom Γ `union` ftvar_in_btyp B `union` ftvar_in_denv Γ
                         `union` ftvar_in_exp (exp_anno e A)).
    pose proof (IH α0 ltac:(solve_notin_auto)) as IH0. inversion IH0; subst.
    match goal with
    | Hp : d_sd_typing mode_tc ((α0 ~ dbind_tvar) ++ Γ) e (ptyp_to_btyp_inh A),
      Hs : {{ empty ⨟ _ ⊢[ mode_tc ] ptyp_to_utyp_syn A ⩽ _ }}d |- _ =>
        rename Hp into Hp0; rename Hs into Hs0
    end.
    assert (HX0A : α0 `notin` ftvar_in_ptyp A) by (simpl in Fr; fsetdec).
    eapply d_sd_typing__anno.
    + pose proof (d_sd_typing_subst_unit _ _ _ _ Hp0 nil α0 Γ
                    ltac:(reflexivity) ltac:(apply tvar_clean_fresh; solve_notin_auto)) as Hsg.
      simpl in Hsg.
      rewrite subst_ptyp_in_exp_fresh_eq in Hsg by (simpl in Fr; fsetdec).
      rewrite ptyp_to_btyp_inh_subst_unit in Hsg.
      rewrite (subst_ptyp_in_ptyp_fresh_eq A ptyp_unit α0) in Hsg by exact HX0A.
      exact Hsg.
    + apply d_sub__forall_r with
        (L := dom Γ `union` {{α0}} `union` ftvar_in_ptyp A `union` ftvar_in_btyp B).
      intros α Hα.
      pose proof (d_sub_rename_tvar (β := α) Hs0 nil Γ α0
                    ltac:(reflexivity) ltac:(simpl; solve_notin_auto)) as Hren.
      simpl in Hren.
      rewrite (subst_utyp_in_utyp_fresh_eq (ptyp_to_utyp_syn A) (utyp_var_f α) α0)
        in Hren by (rewrite ftvar_ptyp_to_utyp_syn; exact HX0A).
      rewrite <- (subst_btyp_in_btyp_intro α0 B (btyp_var_f α)) in Hren by fsetdec.
      exact Hren.
Qed.

Theorem d_sd_typing_complete : forall M Γ e B,
    {{ Γ ⊢[ M ] e ⦂ B }}d -> d_wf_denv Γ -> {{ Γ ⊢ˢᵈ[ M ] e ⦂ B }}d.
Proof.
  intros M Γ e B H. induction H; intros Hwf.
  -
    apply d_sd_typing__unit.
    apply d_sub__infer;
      [ apply d_consis__unit; fsetdec | apply is_styp__unit | fsetdec ].
  -
    assert (HwfA : d_wf_ptyp Γ A) by (eapply d_wf_denv_binds_ptyp; eauto).
    eapply d_sd_typing__var; [ eassumption | ].
    apply d_sub__infer;
      [ apply d_consis_syn_refl; exact HwfA
      | apply is_styp_ptyp_to_btyp_syn; eapply d_wf_ptyp_lc; exact HwfA
      | fsetdec ].
  -
    assert (HwfA : d_wf_ptyp Γ A).
    { apply d_wf_ptyp_of_btyp_inh. eapply d_typing_wf_btyp; eassumption. }
    eapply d_sd_typing__anno; [ apply IHd_typing; exact Hwf | ].
    apply d_sub__infer;
      [ apply d_consis_syn_refl; exact HwfA
      | apply is_styp_ptyp_to_btyp_syn; eapply d_wf_ptyp_lc; exact HwfA
      | fsetdec ].
  -
    eapply d_sd_typing_general_subsumption;
      [ exact Hwf | apply IHd_typing; exact Hwf | assumption ].
  -
    apply d_sd_typing__freeze. apply IHd_typing; exact Hwf.
  -
    apply d_sd_typing_forall_admissible with (L := L `union` dom Γ);
      [ assumption | ].
    intros α Hα. apply H1;
      [ fsetdec | apply d_wf_denv__tvar; [ exact Hwf | fsetdec ] ].
  -
    destruct m as [ | | m' ].
    + apply d_sd_typing__abs with (L := L `union` dom Γ);
        [ discriminate | assumption | assumption | ].
      intros x Hx. apply H2;
        [ fsetdec | apply d_wf_denv__typ; [ exact Hwf | fsetdec | assumption ] ].
    + apply d_sd_typing__abs_check_base with (L := L `union` dom Γ);
        [ assumption
        | apply is_ityp_arrow_r with (B1 := ptyp_to_btyp_inh A);
          apply mod_comp_ty_tc_inv; assumption
        | ].
      intros x Hx. apply H2;
        [ fsetdec | apply d_wf_denv__typ; [ exact Hwf | fsetdec | assumption ] ].
    + apply d_sd_typing__abs with (L := L `union` dom Γ);
        [ discriminate | assumption | assumption | ].
      intros x Hx. apply H2;
        [ fsetdec | apply d_wf_denv__typ; [ exact Hwf | fsetdec | assumption ] ].
  -
    destruct m as [ | | m' ].
    + apply d_sd_typing__abs_anno with (L := L `union` dom Γ) (B1 := B1);
        [ discriminate | assumption | assumption | assumption | ].
      intros x Hx. apply H3;
        [ fsetdec | apply d_wf_denv__typ; [ exact Hwf | fsetdec | assumption ] ].
    + assert (Hia : is_ityp (btyp_arrow B1 B2)) by (apply mod_comp_ty_tc_inv; assumption).
      assert (HB1 : ptyp_to_btyp_inh A = B1).
      { pose proof (ptyp_to_btyp_inh_btyp_to_ptyp (is_ityp_arrow_l _ _ Hia)) as HR.
        rewrite H0 in HR. exact HR. }
      rewrite <- HB1.
      apply d_sd_typing__abs_anno_check_base with (L := L `union` dom Γ);
        [ assumption | exact (is_ityp_arrow_r _ _ Hia) | ].
      intros x Hx. apply H3;
        [ fsetdec | apply d_wf_denv__typ; [ exact Hwf | fsetdec | assumption ] ].
    + apply d_sd_typing__abs_anno with (L := L `union` dom Γ) (B1 := B1);
        [ discriminate | assumption | assumption | assumption | ].
      intros x Hx. apply H3;
        [ fsetdec | apply d_wf_denv__typ; [ exact Hwf | fsetdec | assumption ] ].
  -
    eapply d_sd_typing__app;
      [ eassumption | eassumption
      | apply IHd_typing1; exact Hwf | apply IHd_typing2; exact Hwf ].
Qed.

Corollary d_typing_general_subsumption : forall Γ e A B m,
    {{ Γ ⊢[ mode_ti ] e ⦂ ptyp_to_btyp_syn A }}d ->
    {{ empty ⨟ Γ ⊢[ m ] (ptyp_to_utyp_syn A) ⩽ B }}d ->
    {{ Γ ⊢[ m ] e ⦂ B }}d.
Proof. intros. eapply d_typing__sub; eassumption. Qed.

Corollary d_typing_general_subsumption_spine : forall m1 Γ e Bfull,
    d_wf_denv Γ ->
    {{ Γ ⊢[ m1 ] e ⦂ Bfull }}d ->
    forall n B' M B Bres,
      is_fn_n n m1 ->
      btyp_spine n Bfull B' B Bres ->
      {{ empty ⨟ Γ ⊢[ M ] (btyp_to_utyp_syn B') ⩽ B }}d ->
      {{ Γ ⊢[ mode_fn_n_subst m1 M ] e ⦂ Bres }}d.
Proof.
  intros m1 Γ e Bfull Hwf Hty n B' M B Bres Hfn Hspine Htail.
  apply d_sd_typing_sound.
  eapply d_sd_typing_general_subsumption_spine;
    [ apply d_sd_typing_complete; [ exact Hty | exact Hwf ]
    | apply denv_binds_le_refl
    | eassumption | eassumption | eassumption ].
Qed.

Lemma d_sd_typing_target_lc : forall M Γ e B,
    {{ Γ ⊢ˢᵈ[ M ] e ⦂ B }}d -> d_wf_denv Γ -> lc_btyp B.
Proof.
  intros M Γ e B H; induction H; intros Hwf.
  -
    eapply d_sub_lc_btyp; [ eassumption | apply lc_utyp_unit ].
  -
    eapply d_sub_lc_btyp; [ eassumption | ].
    apply lc_ptyp_to_utyp_syn. eapply d_wf_ptyp_lc.
    eapply d_wf_denv_binds_ptyp; eassumption.
  -
    pick fresh x for (L `union` dom Γ). apply lc_btyp_arrow;
      [ apply lc_ptyp_to_btyp_inh; eapply d_wf_ptyp_lc; eassumption | ].
    apply (H3 x); [ solve_notin_auto
                  | apply d_wf_denv__typ;
                      [ exact Hwf | solve_notin_auto | assumption ] ].
  -
    pick fresh α for (L `union` dom Γ).
    apply lc_btyp_all_inh_exists with (α1 := α).
    apply H0; [ solve_notin_auto
              | apply d_wf_denv__tvar; [ exact Hwf | solve_notin_auto ] ].
  -
    pick fresh x for (L `union` dom Γ). apply lc_btyp_arrow;
      [ apply lc_ptyp_to_btyp_inh; eapply d_wf_ptyp_lc; eassumption | ].
    apply (H2 x); [ solve_notin_auto
                  | apply d_wf_denv__typ;
                      [ exact Hwf | solve_notin_auto | assumption ] ].
  -
    eapply d_sub_lc_btyp; [ eassumption | ].
    apply lc_ptyp_to_utyp_syn, lc_ptyp_of_lc_btyp_inh.
    apply IHd_sd_typing; exact Hwf.
  -
    pick fresh x for (L `union` dom Γ). apply lc_btyp_arrow.
    + apply lc_btyp_of_lc_ptyp_erase.
      rewrite H1. eapply d_wf_ptyp_lc; eassumption.
    + apply (H4 x); [ solve_notin_auto
                    | apply d_wf_denv__typ;
                        [ exact Hwf | solve_notin_auto | assumption ] ].
  -
    pick fresh α for (L `union` dom Γ).
    apply lc_btyp_all_inh_exists with (α1 := α).
    apply H0; [ solve_notin_auto
              | apply d_wf_denv__tvar; [ exact Hwf | solve_notin_auto ] ].
  -
    pick fresh x for (L `union` dom Γ). apply lc_btyp_arrow;
      [ apply lc_ptyp_to_btyp_inh; eapply d_wf_ptyp_lc; eassumption | ].
    apply (H2 x); [ solve_notin_auto
                  | apply d_wf_denv__typ;
                      [ exact Hwf | solve_notin_auto | assumption ] ].
  -
    apply lc_ptyp_to_btyp_inh, lc_ptyp_of_lc_btyp_syn.
    apply IHd_sd_typing; exact Hwf.
  -
    assert (Ha : lc_btyp (btyp_arrow B1 B2)) by (apply IHd_sd_typing1; exact Hwf).
    inversion Ha; subst; assumption.
Qed.
