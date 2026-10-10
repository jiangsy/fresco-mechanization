(** Tvar-renaming closure lemmas: every declarative judgment ([is_*], [guarded_*],
    [d_consis], [d_wf_utyp], [d_sub]) is closed under a free type-variable
    renaming [α -> β].  The tag context [Ψ] is untouched.  Built
    bottom-up: shape predicates, then [d_consis] (as an instance of type
    substitution, [d_consis_subst_tvar]) / [d_wf_utyp] / [d_sub].
    Used by [prop_general_subsumption] for the CST [forall_r] cofinite cases. *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_basic.
Require Import src.fresco.prop_tag.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.decl.prop_wellformed.
Require Import src.fresco.decl.prop_weakening.

Set Implicit Arguments.

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

Lemma is_dtyp_rename_tvar : forall C α1 β1,
    is_dtyp C -> is_dtyp (subst_utyp_in_utyp (utyp_var_f β1) α1 C).
Proof.
  intros C α1 β1 H. induction H; simpl.
  - constructor.
  - match goal with |- context [ ?a == ?b ] => destruct (a == b) end; constructor.
  - constructor; assumption.
  - apply is_dtyp__all_tag with (L := L `union` singleton α1 `union` singleton β1).
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

(** Base fact for the [d_consis] substitution lemma: a tagged type [ph] is
    consistent (with NIL tags) with its bidirectional image [utyp_to_btyp ph]
    — every ε-tagged ∀ matches the syn-painted ∀ via [ForallSynTagged], which
    records no tag.  This is what makes the substitution [α ↦ ph] add no tags
    at variable occurrences. *)
Lemma d_consis_dtyp_refl : forall Γ C,
    {{ Γ ⊢ᵤ C }}d ->
    is_dtyp C ->
    {{ empty ⨟ Γ ⊢ C ∼ (utyp_to_btyp C) }}d.
Proof.
  intros Γ C Hwf. induction Hwf; intros Htt; simpl.
  - apply d_consis__unit. reflexivity.
  - apply d_consis__var; [ assumption | reflexivity ].
  - inversion Htt; subst.
    eapply d_consis__arrow; [ apply IHHwf1 | apply IHHwf2 | fsetdec ]; assumption.
  - inversion Htt.                          (* utyp_all_syn is not is_dtyp *)
  - inversion Htt; subst.
    apply d_consis__forall_syn_tagged with (L := L `union` L0).
    intros α Hα.
    change (btyp_var_f α) with (utyp_to_btyp (utyp_var_f α)).
    rewrite <- utyp_to_btyp_open.
    apply H0; [ fsetdec | ].
    match goal with
    | H : forall x, x `notin` _ -> is_dtyp _ |- _ => apply H; fsetdec
    end.
Qed.

(** The [d_consis] substitution lemma (the infrastructure the [forall_l]
    cases of both transitivity lemmas were blocked on).  Substituting a
    tvar [α0] by a tagged type [ph] on the unresolved side, and by its
    bidirectional image [utyp_to_btyp ph] on the bidirectional side,
    preserves consistency WITHOUT adding tags — the variable occurrences
    become [ph ∼ utyp_to_btyp ph], which is tag-free ([d_consis_dtyp_refl]).
    The [α0]-case uses the base fact; [d_consis_rename_tvar] below is the
    instance [ph := utyp_var_f β]. *)
Lemma d_consis_subst_tvar : forall Ψ Γ C B,
    {{ Ψ ⨟ Γ ⊢ C ∼ B }}d ->
    forall Γ1 Γ2 α0 C',
      Γ = Γ1 ++ (α0 ~ dbind_tvar) ++ Γ2 ->
      {{ (Γ1 ++ Γ2) ⊢ᵤ C' }}d ->
      is_dtyp C' ->
      {{ Ψ ⨟ (Γ1 ++ Γ2) ⊢ (subst_utyp_in_utyp C' α0 C)
                      ∼ (subst_btyp_in_btyp (utyp_to_btyp C') α0 B) }}d.
Proof.
  intros Ψ Γ C B H. induction H; intros Γ1 Γ2 α0 C' Heq Hwf Htt; subst; simpl.
  - apply d_consis__unit. assumption.
  - (* var: [α = α0] uses the base fact; [α <> α0] stays a variable. *)
    destruct_if.
    + eapply d_consis_equiv; [ | apply d_consis_dtyp_refl; assumption ]. fsetdec.
    + apply d_consis__var; [ analyze_binds H; auto | assumption ].
  - eapply d_consis__forall_inh_tagged with
      (L := L `union` dom (Γ1 ++ Γ2) `union` singleton α0).
    + intros α2 Hα2.
      erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var
        by (solve [ fsetdec | apply is_dtyp_lc; assumption ]).
      erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var
        by (solve [ fsetdec | apply lc_utyp_to_btyp; apply is_dtyp_lc; assumption ]).
      rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ Γ2).
      eapply (H0 α2);
        [ fsetdec | simpl; reflexivity
        | rewrite_env ((α2 ~ dbind_tvar) ++ (Γ1 ++ Γ2));
          apply d_wf_utyp_weakening_head; exact Hwf
        | assumption ].
    + assumption.
  - apply d_consis__forall_inh_untagged with
      (L := L `union` dom (Γ1 ++ Γ2) `union` singleton α0).
    intros α2 Hα2.
    erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var
      by (solve [ fsetdec | apply is_dtyp_lc; assumption ]).
    erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var
      by (solve [ fsetdec | apply lc_utyp_to_btyp; apply is_dtyp_lc; assumption ]).
    rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 α2);
      [ fsetdec | simpl; reflexivity
      | rewrite_env ((α2 ~ dbind_tvar) ++ (Γ1 ++ Γ2));
        apply d_wf_utyp_weakening_head; exact Hwf
      | assumption ].
  - apply d_consis__forall_syn_tagged with
      (L := L `union` dom (Γ1 ++ Γ2) `union` singleton α0).
    intros α2 Hα2.
    erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var
      by (solve [ fsetdec | apply is_dtyp_lc; assumption ]).
    erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var
      by (solve [ fsetdec | apply lc_utyp_to_btyp; apply is_dtyp_lc; assumption ]).
    rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 α2);
      [ fsetdec | simpl; reflexivity
      | rewrite_env ((α2 ~ dbind_tvar) ++ (Γ1 ++ Γ2));
        apply d_wf_utyp_weakening_head; exact Hwf
      | assumption ].
  - apply d_consis__forall_syn with
      (L := L `union` dom (Γ1 ++ Γ2) `union` singleton α0).
    intros α2 Hα2.
    erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var
      by (solve [ fsetdec | apply is_dtyp_lc; assumption ]).
    erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var
      by (solve [ fsetdec | apply lc_utyp_to_btyp; apply is_dtyp_lc; assumption ]).
    rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 α2);
      [ fsetdec | simpl; reflexivity
      | rewrite_env ((α2 ~ dbind_tvar) ++ (Γ1 ++ Γ2));
        apply d_wf_utyp_weakening_head; exact Hwf
      | assumption ].
  - eapply d_consis__arrow;
      [ eapply IHd_consis1; eauto | eapply IHd_consis2; eauto | assumption ].
Qed.

(** [d_consis] is closed under tvar renaming (the tag context is untouched):
    the instance of [d_consis_subst_tvar] at [utyp_var_f β], after inserting
    [β] next to [α0]. *)
Lemma d_consis_rename_tvar : forall Ψ Γ C B,
    {{ Ψ ⨟ Γ ⊢ C ∼ B }}d ->
    forall Γ1 Γ2 α0 β,
      Γ = Γ1 ++ (α0 ~ dbind_tvar) ++ Γ2 ->
      β `notin` dom (Γ1 ++ (α0 ~ dbind_tvar) ++ Γ2) ->
      {{ Ψ ⨟ (Γ1 ++ (β ~ dbind_tvar) ++ Γ2) ⊢
         (subst_utyp_in_utyp (utyp_var_f β) α0 C)
         ∼ (subst_btyp_in_btyp (btyp_var_f β) α0 B) }}d.
Proof.
  intros Ψ Γ C B H Γ1 Γ2 α0 β Heq _; subst.
  assert (Hw : {{ Ψ ⨟ (Γ1 ++ (α0 ~ dbind_tvar) ++ (β ~ dbind_tvar) ++ Γ2) ⊢ C ∼ B }}d)
    by (eapply d_consis_tvar_mono; [ exact H | intros γ Hb; analyze_binds Hb ]).
  pose proof (@d_consis_subst_tvar _ _ _ _ Hw Γ1 ((β ~ dbind_tvar) ++ Γ2) α0
                (utyp_var_f β) eq_refl) as Hs.
  cbn [utyp_to_btyp] in Hs. apply Hs; [ apply d_wf_utyp__var; auto | apply is_dtyp__var ].
Qed.

(** [d_wf_utyp] is closed under tvar renaming (pure well-scopedness). *)
Lemma d_wf_utyp_rename_tvar : forall Γ C,
    {{ Γ ⊢ᵤ C }}d ->
    forall Γ1 Γ2 α0 β,
      Γ = Γ1 ++ (α0 ~ dbind_tvar) ++ Γ2 ->
      β `notin` dom (Γ1 ++ (α0 ~ dbind_tvar) ++ Γ2) ->
      {{ (Γ1 ++ (β ~ dbind_tvar) ++ Γ2) ⊢ᵤ (subst_utyp_in_utyp (utyp_var_f β) α0 C) }}d.
Proof.
  intros Γ C H Γ1 Γ2 α0 β Heq _; subst.
  apply d_wf_utyp_of_lc_ftvar.
  - apply subst_utyp_in_utyp_lc_utyp;
      [ eapply d_wf_utyp_lc; eassumption | apply lc_utyp_var_f ].
  - intros γ Hγ. apply ftvar_in_utyp_subst_utyp_in_utyp_upper in Hγ. simpl in Hγ.
    apply union_1 in Hγ. destruct Hγ as [Hγ | Hγ].
    + apply singleton_1 in Hγ. subst. auto.
    + assert (Hne : γ <> α0).
      { intro Heq. subst. eapply remove_1; [ reflexivity | eassumption ]. }
      apply remove_3 in Hγ.
      pose proof (d_wf_utyp_ftvar H Hγ) as Hb. analyze_binds Hb.
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

(** [d_sub] is closed under tvar renaming (the tag context is untouched);
    closes the cofinite-uniform [forall_r] case of the transitivity lemmas. *)
Lemma d_sub_rename_tvar : forall m Ψ Γ C B,
    {{ Ψ ⨟ Γ ⊢[ m ] C ⩽ B }}d ->
    forall Γ1 Γ2 α0 β,
      Γ = Γ1 ++ (α0 ~ dbind_tvar) ++ Γ2 ->
      β `notin` dom (Γ1 ++ (α0 ~ dbind_tvar) ++ Γ2) ->
      {{ Ψ ⨟ (Γ1 ++ (β ~ dbind_tvar) ++ Γ2) ⊢[ m ]
         (subst_utyp_in_utyp (utyp_var_f β) α0 C)
         ⩽ (subst_btyp_in_btyp (btyp_var_f β) α0 B) }}d.
Proof.
  intros m Ψ Γ C B H. induction H; intros Γ1 Γ2 α0 β Heq Hfr; subst; simpl.
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
      change (utyp_all_tag ε (subst_utyp_in_utyp (utyp_var_f β) α0 C))
        with (subst_utyp_in_utyp (utyp_var_f β) α0 (utyp_all_tag ε C));
      rewrite ftag_in_utyp_subst_tagfree by reflexivity; assumption.
    + apply d_tags_subst_tvar. eassumption.
    + eapply d_wf_utyp_rename_tvar; [ eassumption | reflexivity | exact Hfr ].
    + apply is_dtyp_rename_tvar. assumption.
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
    + apply is_dtyp_rename_tvar. assumption.
    + rewrite <- subst_utyp_in_utyp_open_utyp_wrt_utyp by apply lc_utyp_var_f.
      eapply IHd_sub; [ reflexivity | exact Hfr ].
Qed.
