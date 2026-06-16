(** Frost — well-formedness lemmas for the current split syntax. *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.

Set Implicit Arguments.

(** * Declarative contexts. *)

Inductive d_wf_denv : list (atom * dbind) -> Prop :=
| d_wf_denv__nil : d_wf_denv nil
| d_wf_denv__tvar : forall Γ X,
    d_wf_denv Γ ->
    X `notin` dom Γ ->
    d_wf_denv ((X ~ dbind_tvar) ++ Γ)
| d_wf_denv__typ : forall Γ x A,
    d_wf_denv Γ ->
    x `notin` dom Γ ->
    d_wf_ptyp Γ A ->
    d_wf_denv ((x ~ dbind_typ A) ++ Γ)
| d_wf_denv__skl : forall Γ x P,
    d_wf_denv Γ ->
    x `notin` dom Γ ->
    d_wf_pskl nil Γ P ->
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
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
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
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    apply H0; auto.
  - inst_cofinites_for d_wf_utyp__all_etag; auto.
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    apply H0; auto.
Qed.

(** [d_wf_pskl] is monotone in the scope set [Ψ]: enlarging [Ψ] only
    relaxes the [var] rule (and the [∀] rule under its binder).  Used by
    [d_refine_preserves_wf] to bridge a premise whose cleared context
    yields a [Ψ ⊆] the one the conclusion needs. *)
Lemma d_wf_pskl_Psi_mono : forall Ψ Γ P,
    Ψ ⨟ Γ ⊢ₚₛ P ->
    forall Ψ', (forall X, List.In X Ψ -> List.In X Ψ') ->
    Ψ' ⨟ Γ ⊢ₚₛ P.
Proof.
  intros Ψ Γ P H. induction H; intros Ψ' Hmono.
  - constructor.
  - constructor. destruct H as [Hin | Hb]; [ left; auto | right; auto ].
  - constructor; auto.
  - inst_cofinites_for d_wf_pskl__all. intros X HX. apply H0; auto.
    intros Y HY. simpl in HY |- *. destruct HY as [HY | HY]; [ left; auto | right; auto ].
  - constructor.
  - apply d_wf_pskl__tophole; auto.
Qed.

Lemma d_wf_pskl_weakening : forall Γ1 Γ2 Γ3 Ψ P,
    Ψ ⨟ (Γ1 ++ Γ3) ⊢ₚₛ P ->
    Ψ ⨟ (Γ1 ++ Γ2 ++ Γ3) ⊢ₚₛ P.
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
    intros X HX. apply H0; auto.
  - constructor.
  - constructor; auto.
Qed.

Lemma d_wf_uskl_weakening : forall Γ1 Γ2 Γ3 Ψ R,
    Ψ ⨟ (Γ1 ++ Γ3) ⊢ᵤₛ R ->
    Ψ ⨟ (Γ1 ++ Γ2 ++ Γ3) ⊢ᵤₛ R.
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
    intros X HX. apply H0; auto.
  - inst_cofinites_for d_wf_uskl__all_etag.
    intros X HX. apply H0; auto.
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

Lemma d_tags_subst_tvar : forall Δ C X Y,
    d_tags Δ C ->
    d_tags Δ (subst_utyp_in_utyp (utyp_var_f Y) X C).
Proof.
  intros Δ C X Y H. induction H; simpl.
  - apply d_tags__unit; assumption.
  - match goal with |- context [ if ?d then _ else _ ] => destruct d end;
      apply d_tags__var; assumption.
  - eapply d_tags__arrow; [ eassumption | eassumption | assumption | assumption ].
  - inst_cofinites_for d_tags__all_etag Δ0 := Δ0; [ | assumption | assumption ].
    intros Z HZ.
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
    Δ [=] Δo -> Δ ⨟ Γ ⊨ C ≈ B -> Δo ⨟ Γ ⊨ C ≈ B.
Proof.
  intros Δ Δo Γ C B Heq H. revert Δo Heq. induction H; intros Δo Heq.
  - apply d_consis__unit. fsetdec.
  - apply d_consis__var; [ assumption | fsetdec ].
  - eapply d_consis__arrow; [ eassumption | eassumption | fsetdec ].
  - eapply d_consis__forall_inh_tagged; [ eassumption | fsetdec ].
  - apply d_consis__forall_inh_untagged with (L := L);
      intros X HX; eauto.
  - apply d_consis__forall_syn_tagged with (L := L);
      intros X HX; eauto.
  - apply d_consis__forall_syn with (L := L);
      intros X HX; eauto.
Qed.

Lemma d_sub_equiv : forall m Δ Δo Γ C B,
    Δ [=] Δo -> Δ ⨟ Γ ⊢[ m ] C ⊑ B -> Δo ⨟ Γ ⊢[ m ] C ⊑ B.
Proof.
  intros m Δ Δo Γ C B Heq H. revert Δo Heq. induction H; intros Δo Heq.
  - apply d_sub__infer; [ assumption | assumption | fsetdec ].
  - apply d_sub__check; [ assumption | assumption | | assumption ].
    eapply d_consis_equiv; [ exact Heq | eassumption ].
  - apply d_sub__forall_r with (L := L);
      intros X HX; eauto.
  - eapply d_sub__arg; [ eassumption | eassumption | fsetdec ].
  - (* forall_l_tagged: outer context pass-through, premise via IH *)
    eapply d_sub__forall_l_tagged with (Δ' := Δ');
      [ assumption | fsetdec | eassumption | assumption | assumption | ].
    match goal with
    | IH : forall _, _ [=] _ -> _ |- _ => eapply IH; fsetdec
    end.
  - eapply d_sub__forall_l_untagged with (Δ' := Δ');
      [ assumption | fsetdec | eassumption | assumption | assumption | ].
    match goal with
    | IH : forall _, _ [=] _ -> _ |- _ => eapply IH; fsetdec
    end.
Qed.

(** * Preservation hooks.

    These are the shape-correct statements the later typing/subtyping
    ports should consume.  Some are currently left as axioms while the
    proof layer is being moved off the old unified syntax; they are
    intentionally stated over the latest categories. *)


Lemma d_typing_pat_preserves_wf :
  (forall m Γ e B, d_typing m Γ e B -> d_wf_btyp Γ B) /\
  (forall m Γ e Q, d_pat m Γ e Q -> d_wf_pskl nil Γ Q).
Proof.
Admitted.
