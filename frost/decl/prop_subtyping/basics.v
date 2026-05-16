(** Frost — declarative subtyping metatheory: reflexivity, mono basics,
    weakening, tvar morphism, and monotype-substitution lemmas. *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Sorting.Permutation.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.

Set Implicit Arguments.

(** * Reflexivity (on monotypes).

    The paper's [d_consis] is asymmetric: the LHS is an unresolved type
    ([is_utyp]) and the RHS is a coloured ("bidirectional") type
    ([is_typ]). Reflexivity in the strict sense [d_consis nil Γ A A] only
    makes sense when LHS-form = RHS-form — i.e. on monomorphic types,
    where both forms coincide. *)

Lemma d_consis_refl_mono : forall Γ A,
    mono_typ A ->
    d_wf_typ Γ A ->
    nil ⨟ Γ ⊨ A ≈ A.
Proof.
  intros Γ A H. induction H; intros Hwf.
  - apply d_consis__unit.
  - inversion Hwf; subst. apply d_consis__var. auto.
  - inversion Hwf; subst.
    rewrite_env (@nil atom ++ (@nil atom)).
    apply d_consis__arrow; auto.
    intros ? ? ?; auto.
Qed.

(** Every monotype is in [is_syn_typ] (no quantifiers at all). *)
Lemma mono_typ_is_syn_typ : forall A,
    mono_typ A -> is_syn_typ A.
Proof.
  intros A H. induction H; constructor; auto.
Qed.

(** Every monotype is in [is_inh_typ]. *)
Lemma mono_typ_is_inh_typ : forall A,
    mono_typ A -> is_inh_typ A.
Proof.
  intros A H. induction H; constructor; auto.
Qed.

(** A monotype is colour-free: it round-trips through [erase] / any
    colouring. (No [forall] / hole nodes, so [syn_color] and
    [inh_color] are the identity on [erase A].) *)
Lemma mono_typ_syn_color_erase : forall A,
    mono_typ A -> syn_color (erase A) = A.
Proof.
  intros A H. induction H; simpl; try reflexivity.
  rewrite IHmono_typ1, IHmono_typ2. reflexivity.
Qed.

Lemma mono_typ_inh_color_erase : forall A,
    mono_typ A -> inh_color (erase A) = A.
Proof.
  intros A H. induction H; simpl; try reflexivity.
  rewrite IHmono_typ1, IHmono_typ2. reflexivity.
Qed.

(** Every monotype is guarded (mono ⊆ {unit, var, arrow}). *)
Lemma mono_typ_guarded : forall A,
    mono_typ A -> guarded_typ A.
Proof. intros A H. destruct H; constructor. Qed.

(** [is_syn_typ] / [is_inh_typ] types round-trip through their
    [colour]-painting + [erase]. They are [syn_color]/[inh_color]
    images of their own [erase] — same role for the colour-discipline
    lemmas as [mono_typ_*_color_erase] for monos. The cofinite [all]
    case closes via [open_typ_wrt_typ_inj] on a fresh witness, using
    [erase_ftvar] + [{syn,inh}_color_ftvar] to discharge the freshness
    side conditions (the shared [erase]-image makes both freshness
    sets coincide with [ftvar_in_typ A]). *)
Lemma is_syn_typ_syn_color_erase : forall A,
    is_syn_typ A -> syn_color (erase A) = A.
Proof.
  intros A H. induction H.
  - reflexivity.
  - reflexivity.
  - simpl. f_equal; auto.
  - simpl. f_equal.
    pick fresh X for (L `union` ftvar_in_typ A).
    specialize (H0 X ltac:(auto)).
    rewrite erase_open_typ in H0.
    simpl in H0.
    rewrite syn_color_open_ctyp in H0.
    simpl in H0.
    apply open_typ_wrt_typ_inj in H0; auto.
    rewrite syn_color_ftvar. rewrite erase_ftvar. auto.
Qed.

Lemma is_inh_typ_inh_color_erase : forall A,
    is_inh_typ A -> inh_color (erase A) = A.
Proof.
  intros A H. induction H.
  - reflexivity.
  - reflexivity.
  - simpl. f_equal; auto.
  - simpl. f_equal.
    pick fresh X for (L `union` ftvar_in_typ A).
    specialize (H0 X ltac:(auto)).
    rewrite erase_open_typ in H0.
    simpl in H0.
    rewrite inh_color_open_ctyp in H0.
    simpl in H0.
    apply open_typ_wrt_typ_inj in H0; auto.
    rewrite inh_color_ftvar. rewrite erase_ftvar. auto.
Qed.

(** Substituting a *monotype* [B] into a colouring pushes through to a
    [ctyp]-substitution on the base (via [B = syn_color (erase B)] etc.
    + the colouring/subst commutation). *)
Lemma mono_subst_syn_color : forall B X C,
    mono_typ B ->
    subst_typ_in_typ B X (syn_color C) = syn_color (subst_ctyp_in_ctyp (erase B) X C).
Proof.
  intros B X C Hmono.
  rewrite <- (mono_typ_syn_color_erase Hmono) at 1.
  apply syn_color_subst_ctyp.
Qed.

Lemma mono_subst_inh_color : forall B X C,
    mono_typ B ->
    subst_typ_in_typ B X (inh_color C) = inh_color (subst_ctyp_in_ctyp (erase B) X C).
Proof.
  intros B X C Hmono.
  rewrite <- (mono_typ_inh_color_erase Hmono) at 1.
  apply inh_color_subst_ctyp.
Qed.

Lemma d_sub_refl_mono : forall Γ A,
    mono_typ A ->
    d_wf_typ Γ A ->
    Γ ⊢[ mode_ti ; nil ] A ⊑ A.
Proof.
  intros Γ A H Hwf.
  rewrite <- (mono_typ_syn_color_erase H).
  apply d_sub__infer.
  rewrite (mono_typ_syn_color_erase H).
  apply d_consis_refl_mono; auto.
Qed.

(** * Weakening for [d_consis] and [d_sub] (used internally). *)

Lemma d_consis_weakening : forall Γ1 Γ2 Γ3 Δ T A,
    Δ ⨟ (Γ1 ++ Γ3) ⊨ T ≈ A ->
    Δ ⨟ (Γ1 ++ Γ2 ++ Γ3) ⊨ T ≈ A.
Proof.
  intros Γ1 Γ2 Γ3 Δ T A H.
  dependent induction H.
  - apply d_consis__unit.
  - apply d_consis__var.
    apply binds_app_iff in H. destruct H as [Hin|Hin].
    + apply binds_app_iff. auto.
    + apply binds_app_iff. right. apply binds_app_iff. auto.
  - apply d_consis__forall_inh_tagged with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)); auto.
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_consis__forall_syn_tagged with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_consis__forall_syn with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_consis__forall_inh with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_consis__arrow; eauto.
Qed.

Lemma d_consis_weakening_head : forall Γ Γ' Δ T A,
    Δ ⨟ Γ ⊨ T ≈ A ->
    Δ ⨟ (Γ' ++ Γ) ⊨ T ≈ A.
Proof.
  intros Γ Γ' Δ T A H.
  rewrite_env (nil ++ Γ' ++ Γ).
  apply d_consis_weakening. simpl. exact H.
Qed.

(** [d_consis] is preserved by any context morphism that preserves
    tvar bindings (similar to [d_wf_typ_tvar_morph]). *)
Lemma d_consis_tvar_morph : forall Γ Γ' Δ T A,
    (forall X, binds X dbind_tvar Γ -> binds X dbind_tvar Γ') ->
    Δ ⨟ Γ ⊨ T ≈ A ->
    Δ ⨟ Γ' ⊨ T ≈ A.
Proof.
  intros Γ Γ' Δ T A Hmorph H. generalize dependent Γ'.
  induction H; intros Γ' Hmorph.
  - apply d_consis__unit.
  - apply d_consis__var. apply Hmorph; auto.
  - apply d_consis__forall_inh_tagged with (L := L `union` dom Γ'); auto.
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY.
    destruct HbY as [Hin | Hin]; apply binds_app_iff;
      [left; auto | right; auto].
  - apply d_consis__forall_syn_tagged with (L := L `union` dom Γ').
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY.
    destruct HbY as [Hin | Hin]; apply binds_app_iff;
      [left; auto | right; auto].
  - apply d_consis__forall_syn with (L := L `union` dom Γ').
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY.
    destruct HbY as [Hin | Hin]; apply binds_app_iff;
      [left; auto | right; auto].
  - apply d_consis__forall_inh with (L := L `union` dom Γ').
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY.
    destruct HbY as [Hin | Hin]; apply binds_app_iff;
      [left; auto | right; auto].
  - apply d_consis__arrow; auto.
Qed.

Lemma d_sub_weakening : forall Γ1 Γ2 Γ3 M Δ T A,
    (Γ1 ++ Γ3) ⊢[ M ; Δ ] T ⊑ A ->
    (Γ1 ++ Γ2 ++ Γ3) ⊢[ M ; Δ ] T ⊑ A.
Proof.
  intros Γ1 Γ2 Γ3 M Δ T A H. dependent induction H.
  - (* __infer: single [d_consis] premise (post colour re-encoding). *)
    apply d_sub__infer. apply d_consis_weakening.
    match goal with Hc : d_consis nil (Γ1 ++ Γ3) _ _ |- _ => exact Hc end.
  - (* __check: [guarded_typ] + [d_consis] premises. *)
    apply d_sub__check; auto. apply d_consis_weakening.
    match goal with Hc : d_consis _ (Γ1 ++ Γ3) _ _ |- _ => exact Hc end.
  - apply d_sub__forall_r with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_sub__arg.
    + apply d_consis_weakening. exact H.
    + apply IHd_sub; auto.
  - eapply d_sub__forall_l_tagged; eauto.
    eapply d_wf_ttyp_weakening. exact H1.
Qed.

Lemma d_sub_weakening_head : forall Γ Γ' M Δ T A,
    Γ ⊢[ M ; Δ ] T ⊑ A ->
    (Γ' ++ Γ) ⊢[ M ; Δ ] T ⊑ A.
Proof.
  intros Γ Γ' M Δ T A H. rewrite_env (nil ++ Γ' ++ Γ).
  apply d_sub_weakening. simpl. exact H.
Qed.

(** [d_consis] respects monotype substitution. This is the key subst
    lemma for closing [__forall_r] cases via atom renaming (set [B] to
    [typ_var_f X'] for a fresh [X']). *)
Lemma d_consis_subst_mono : forall Γ1 Γ2 Δ X T A B,
    Δ ⨟ (Γ1 ++ (X ~ dbind_tvar) ++ Γ2) ⊨ T ≈ A ->
    mono_typ B ->
    d_wf_typ Γ2 B ->
    Δ ⨟ (Γ1 ++ Γ2) ⊨ subst_typ_in_typ B X T ≈ subst_typ_in_typ B X A.
Proof.
  intros Γ1 Γ2 Δ X T A B Hc HBmono HBwf.
  dependent induction Hc; simpl.
  - apply d_consis__unit.
  - (* __var *)
    destruct (X0 == X); subst.
    + (* Y = X: result reduces to d_consis nil Γ B B. *)
      replace (if X == X then B else typ_var_f X) with B
        by (destruct (X == X); [reflexivity|contradiction]).
      apply d_consis_refl_mono; auto.
      apply d_wf_typ_weakening_head; auto.
    + replace (if X0 == X then B else typ_var_f X0) with (typ_var_f X0)
        by (destruct (X0 == X); [contradiction|reflexivity]).
      apply binds_remove_mid in H; auto.
      apply d_consis__var. apply binds_app_iff in H. destruct H; apply binds_app_iff; auto.
  - (* __forall_inh_tagged *)
    apply d_consis__forall_inh_tagged with (L := L `union` singleton X `union` dom (Γ1 ++ Γ2)); auto.
    intros Y HY.
    rewrite subst_typ_in_typ_open_typ_wrt_typ_var; [| fsetdec | apply (d_wf_typ_lc HBwf)].
    rewrite subst_typ_in_typ_open_typ_wrt_typ_var; [| fsetdec | apply (d_wf_typ_lc HBwf)].
    rewrite_env (((Y ~ dbind_tvar) ++ Γ1) ++ Γ2).
    apply H0; auto.
  - (* __forall_syn_tagged *)
    apply d_consis__forall_syn_tagged with (L := L `union` singleton X `union` dom (Γ1 ++ Γ2)).
    intros Y HY.
    rewrite subst_typ_in_typ_open_typ_wrt_typ_var; [| fsetdec | apply (d_wf_typ_lc HBwf)].
    rewrite subst_typ_in_typ_open_typ_wrt_typ_var; [| fsetdec | apply (d_wf_typ_lc HBwf)].
    rewrite_env (((Y ~ dbind_tvar) ++ Γ1) ++ Γ2).
    apply H0; auto.
  - (* __forall_syn (post-refactor new rule) *)
    apply d_consis__forall_syn with (L := L `union` singleton X `union` dom (Γ1 ++ Γ2)).
    intros Y HY.
    rewrite subst_typ_in_typ_open_typ_wrt_typ_var; [| fsetdec | apply (d_wf_typ_lc HBwf)].
    rewrite subst_typ_in_typ_open_typ_wrt_typ_var; [| fsetdec | apply (d_wf_typ_lc HBwf)].
    rewrite_env (((Y ~ dbind_tvar) ++ Γ1) ++ Γ2).
    apply H0; auto.
  - (* __forall_inh *)
    apply d_consis__forall_inh with (L := L `union` singleton X `union` dom (Γ1 ++ Γ2)).
    intros Y HY.
    rewrite subst_typ_in_typ_open_typ_wrt_typ_var; [| fsetdec | apply (d_wf_typ_lc HBwf)].
    rewrite subst_typ_in_typ_open_typ_wrt_typ_var; [| fsetdec | apply (d_wf_typ_lc HBwf)].
    rewrite_env (((Y ~ dbind_tvar) ++ Γ1) ++ Γ2).
    apply H0; auto.
  - apply d_consis__arrow; eauto.
Qed.

(** Monotypes that are well-formed in Γ inhabit [d_wf_ttyp nil Γ].
    Mono types are arrow trees of unit/var leaves; no quantifiers, so the
    tag-set Δ is uniformly nil. *)
Lemma mono_typ_d_wf_ttyp : forall Γ B,
    mono_typ B -> d_wf_typ Γ B -> d_wf_ttyp nil Γ B.
Proof.
  intros Γ B Hmono. induction Hmono; intros Hwf.
  - apply d_wf_ttyp__unit.
  - apply d_wf_ttyp__var. inversion Hwf; subst; auto.
  - inversion Hwf; subst.
    rewrite_env (@nil atom ++ @nil atom).
    apply d_wf_ttyp__arrow; auto.
    apply list_disjoint_nil_l.
Qed.

(** Helper: monotypes can't be typ_all_etag at top. *)
Lemma mono_not_etag : forall B ε T, mono_typ B -> B <> typ_all_etag ε T.
Proof. intros B ε T H; destruct H; discriminate. Qed.

(* mono_not_plain dropped post-refactor: typ_all_plain no longer exists. *)

(** Mono-substituting B for X in T preserves "T not typ_all_etag at top".
    Cases: T = unit/var/arrow → still not etag (constructor preserved).
    T = typ_var_f X (the substituted one) → subst gives B (mono, not etag). *)
Lemma subst_typ_not_etag : forall B X T,
    mono_typ B ->
    (forall ε T', T <> typ_all_etag ε T') ->
    forall ε T', subst_typ_in_typ B X T <> typ_all_etag ε T'.
Proof.
  intros B X T HBmono Hne ε T' Heq.
  destruct T; simpl in Heq; try discriminate.
  - (* T = typ_var_f X0: subst either gives B or stays *)
    destruct (X0 == X); simpl in Heq.
    + (* X0 = X: result is B, which is mono → not etag *)
      eapply mono_not_etag; eauto.
    + discriminate.
  - (* T = typ_all_etag: contradicts Hne *)
    eapply (Hne ε0); reflexivity.
Qed.

(* subst_typ_not_plain dropped post-refactor: typ_all_plain no longer
   exists in typ. *)

(** [d_sub] respects monotype substitution. Closing this unblocks
    [d_consis_extends_d_sub __forall_r] via alpha-renaming the cofinite
    body's d_sub across X. *)
Lemma d_sub_subst_mono : forall Γ1 Γ2 X M Δ T A B,
    Γ1 ++ (X ~ dbind_tvar) ++ Γ2 ⊢[ M ; Δ ] T ⊑ A ->
    mono_typ B ->
    d_wf_typ Γ2 B ->
    Γ1 ++ Γ2 ⊢[ M ; Δ ] subst_typ_in_typ B X T ⊑ subst_typ_in_typ B X A.
Proof.
  intros Γ1 Γ2 X M Δ T A B Hsub HBmono HBwf.
  dependent induction Hsub.
  - (* __infer: LHS/RHS are [syn_color]-painted. The mono subst [B]
       pushes through to a [ctyp]-subst on the base; then it is a
       [d_consis] substitution. *)
    rewrite !mono_subst_syn_color by assumption.
    apply d_sub__infer.
    rewrite <- !mono_subst_syn_color by assumption.
    apply d_consis_subst_mono; auto.
  - (* __check: LHS [syn_color], RHS [inh_color]. *)
    rewrite mono_subst_syn_color by assumption.
    rewrite mono_subst_inh_color by assumption.
    apply d_sub__check.
    + (* guardedness transfers through the base [ctyp]-substitution:
         the original [guarded_typ (syn_color T0)] premise forces [T0]
         to be unit/var/arrow; subst preserves that, except a substituted
         var becomes the (guarded, mono) [B]. *)
      match goal with H : guarded_typ (syn_color ?T0) |- _ =>
        destruct T0; simpl in H; simpl;
        try constructor;
        try (inversion H; fail);
        (* typ_var_f X1 case *)
        match goal with X1 : ctypvar |- _ =>
          destruct (eq_var X1 X);
          [ rewrite (mono_typ_syn_color_erase HBmono);
            apply mono_typ_guarded; assumption
          | constructor ]
        end
      end.
    + rewrite <- mono_subst_syn_color by assumption.
      rewrite <- mono_subst_inh_color by assumption.
      apply d_consis_subst_mono; auto.
  - (* __forall_r *)
    apply d_sub__forall_r with
      (L := L `union` singleton X `union` dom (Γ1 ++ Γ2)).
    intros Y HY.
    rewrite subst_typ_in_typ_open_typ_wrt_typ_var; [|fsetdec | apply (d_wf_typ_lc HBwf)].
    rewrite_env (((Y ~ dbind_tvar) ++ Γ1) ++ Γ2).
    apply H0; auto.
  - (* __arg *)
    apply d_sub__arg.
    + apply d_consis_subst_mono; auto.
    + apply IHHsub; auto.
  - (* __forall_l_tagged *)
    simpl.
    eapply d_sub__forall_l_tagged with (Δ' := Δ') (ph := subst_typ_in_typ B X ph); auto.
    + eapply d_wf_ttyp_subst; eauto.
      apply mono_typ_d_wf_ttyp; auto.
    + rewrite <- subst_typ_in_typ_open_typ_wrt_typ; [| apply (d_wf_typ_lc HBwf)].
      apply IHHsub; auto.
Qed.

(** Context tvar-morphism for [d_sub]. *)
Lemma d_sub_tvar_morph : forall Γ Γ' M Δ T A,
    (forall X, binds X dbind_tvar Γ -> binds X dbind_tvar Γ') ->
    Γ ⊢[ M ; Δ ] T ⊑ A ->
    Γ' ⊢[ M ; Δ ] T ⊑ A.
Proof.
  intros Γ Γ' M Δ T A Hmorph H. generalize dependent Γ'.
  induction H; intros Γ' Hmorph.
  - apply d_sub__infer; auto. eapply d_consis_tvar_morph; eauto.
  - apply d_sub__check; auto. eapply d_consis_tvar_morph; eauto.
  - apply d_sub__forall_r with (L := L `union` dom Γ').
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY.
    destruct HbY as [Hb | Hb]; apply binds_app_iff; [left | right]; auto.
  - apply d_sub__arg.
    + eapply d_consis_tvar_morph; eauto.
    + apply IHd_sub; auto.
  - eapply d_sub__forall_l_tagged; eauto.
    eapply d_wf_ttyp_tvar_morph; eauto.
Qed.
