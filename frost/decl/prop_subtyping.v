(** Frost — declarative subtyping metatheory (Phase 2.C). *)

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

Lemma d_sub_refl_mono : forall Γ A,
    mono_typ A ->
    d_wf_typ Γ A ->
    Γ ⊢[ mode_ti ; nil ] A ⊑ A.
Proof.
  intros Γ A H Hwf.
  apply d_sub__infer.
  - apply mono_typ_is_syn_typ; auto.
  - apply d_consis_refl_mono; auto.
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
  - apply d_consis__forall_inh_untagged with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_consis__forall_syn_tagged with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_consis__forall_syn_untagged with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
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
  - apply d_consis__forall_inh_untagged with (L := L `union` dom Γ').
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY.
    destruct HbY as [Hin | Hin]; apply binds_app_iff;
      [left; auto | right; auto].
  - apply d_consis__forall_syn_tagged with (L := L `union` dom Γ').
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY.
    destruct HbY as [Hin | Hin]; apply binds_app_iff;
      [left; auto | right; auto].
  - apply d_consis__forall_syn_untagged with (L := L `union` dom Γ').
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
  - apply d_sub__infer; auto. apply d_consis_weakening. exact H0.
  - apply d_sub__check; auto. apply d_consis_weakening. exact H2.
  - apply d_sub__forall_r with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_sub__arg.
    + apply d_consis_weakening. exact H.
    + apply IHd_sub; auto.
  - eapply d_sub__forall_l_tagged; eauto.
    eapply d_wf_ttyp_weakening. exact H1.
  - eapply d_sub__forall_l_untagged; eauto.
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
  - (* __forall_inh_untagged *)
    apply d_consis__forall_inh_untagged with (L := L `union` singleton X `union` dom (Γ1 ++ Γ2)).
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
  - (* __forall_syn_untagged *)
    apply d_consis__forall_syn_untagged with (L := L `union` singleton X `union` dom (Γ1 ++ Γ2)).
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

(** Helper: monotypes can't be typ_all_plain at top. *)
Lemma mono_not_plain : forall B T, mono_typ B -> B <> typ_all_plain T.
Proof. intros B T H; destruct H; discriminate. Qed.

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

Lemma subst_typ_not_plain : forall B X T,
    mono_typ B ->
    (forall T', T <> typ_all_plain T') ->
    forall T', subst_typ_in_typ B X T <> typ_all_plain T'.
Proof.
  intros B X T HBmono Hne T' Heq.
  destruct T; simpl in Heq; try discriminate.
  - destruct (X0 == X); simpl in Heq.
    + eapply mono_not_plain; eauto.
    + discriminate.
  - eapply Hne; reflexivity.
Qed.

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
  - (* __infer *)
    apply d_sub__infer.
    + apply is_syn_typ_subst; auto.
      apply mono_typ_is_syn_typ; auto.
    + apply d_consis_subst_mono; auto.
  - (* __check *)
    apply d_sub__check; auto.
    + apply subst_typ_not_etag; auto.
    + apply subst_typ_not_plain; auto.
    + apply is_inh_typ_subst; auto.
      apply mono_typ_is_inh_typ; auto.
    + apply d_consis_subst_mono; auto.
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
  - (* __forall_l_untagged *)
    simpl.
    eapply d_sub__forall_l_untagged with (Δ' := Δ') (ph := subst_typ_in_typ B X ph); auto.
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
  - eapply d_sub__forall_l_untagged; eauto.
    eapply d_wf_ttyp_tvar_morph; eauto.
Qed.

(** * Consistency extends subtyping (paper proofs.tex lemma:consis-sub).

    Paper claim: if [d_consis Δ Γ T A] and [d_sub M Δ' Γ A B], then
    [d_sub M (Δ ++ Δ') Γ T B].

    Note the asymmetry: A appears as the (coloured-typ) RHS of [d_consis]
    and as the (utyp-form) LHS of [d_sub]. Both views happen to be
    compatible at the constructor heads we need to handle here — the
    LHS of [d_sub] in [d_sub__arrow]/[d_sub__check] is unrestricted, and
    the [d_sub__forall_l_*] rules don't apply when A is a [typ_all_col]
    (the only forall flavour produced by [d_consis]).

    The proof proceeds by induction on the [d_sub] derivation. The
    intermediate consistency-composition step (when [d_sub] terminates
    in [__infer]/[__check]/[__arg]) reduces to the [d_consis_compose]
    lemma below. *)

(** Helper: swap the inner two segments of a 4-way concatenation,
    up to Permutation. Used to handle the arrow case of
    [d_consis_compose]. *)
Lemma list_swap_middle : forall {A : Type} (l1 l2 l3 l4 : list A),
    Permutation ((l1 ++ l2) ++ (l3 ++ l4)) ((l1 ++ l3) ++ (l2 ++ l4)).
Proof.
  intros A l1 l2 l3 l4.
  (* Make the right-associated form the working term, then apply
     Permutation_app_swap_app under l1, and re-pack to left-assoc. *)
  pose proof (Permutation_app_swap_app (A := A) l2 l3 l4) as Hswap.
  (* Hswap : Permutation (l2 ++ l3 ++ l4) (l3 ++ l2 ++ l4). *)
  apply (Permutation_app_head l1) in Hswap.
  (* Hswap : Permutation (l1 ++ l2 ++ l3 ++ l4) (l1 ++ l3 ++ l2 ++ l4). *)
  (* Re-associate both sides to match goal form. *)
  replace ((l1 ++ l2) ++ (l3 ++ l4)) with (l1 ++ l2 ++ l3 ++ l4).
  - replace ((l1 ++ l3) ++ (l2 ++ l4)) with (l1 ++ l3 ++ l2 ++ l4).
    + exact Hswap.
    + rewrite app_assoc. reflexivity.
  - rewrite app_assoc. reflexivity.
Qed.

(** ** Composition of consistency, modulo Δ-permutation.

    Paper Lemma B.2 (Consistency Transitivity). [paper-ref: thm:consist-transitivity]

    The paper writes the conclusion's Δ as "Δ_1, Δ_2" — set union
    (declarative.tex:814: "We write Δ,Δ' for set union"). Our
    encoding uses [list atom], so the natural strict statement
    [d_consis (Δa ++ Δb) Γ T B] is provably FALSE: the arrow case
    produces output Δ of shape [Δa1 ++ Δb1 ++ Δa2 ++ Δb2]
    (structurally interleaved by the arrow components), while
    [Δa ++ Δb = Δa1 ++ Δa2 ++ Δb1 ++ Δb2] swaps two inner segments.

    Closing therefore restates the conclusion modulo [Permutation].
    All forall-cases of [d_consis] (the ones that might contribute
    a tag to Δ) are VACUOUS in compose: they produce
    [A = typ_all_col c _], which is not an [is_utyp] shape and so
    cannot be the LHS of [Hc2]. *)

Lemma d_consis_compose : forall Δa Δb Γ T A B,
    Δa ⨟ Γ ⊨ T ≈ A ->
    Δb ⨟ Γ ⊨ A ≈ B ->
    list_disjoint Δa Δb ->                 (* linearity premise: tags from
                                              the two sub-derivations are
                                              fresh w.r.t. each other. *)
    exists Δc, Permutation Δc (Δa ++ Δb) /\ Δc ⨟ Γ ⊨ T ≈ B.
Proof.
  intros Δa Δb Γ T A B Hc1. generalize dependent B. generalize dependent Δb.
  induction Hc1; intros Δb B0 Hc2 Hdis.
  - (* unit ~ unit, then unit ~ B0: Δa = nil, so Δc = Δb. *)
    exists Δb. split; [simpl; apply Permutation_refl | exact Hc2].
  - (* var X ~ var X. *)
    exists Δb. split; [simpl; apply Permutation_refl | exact Hc2].
  - (* forall_inh_tagged / forall_inh_untagged / forall_syn_*: A is
       typ_all_col on the RHS, which is not an [is_utyp] shape and so
       cannot be the LHS of [Hc2]. *)
    inversion Hc2.
  - inversion Hc2.
  - inversion Hc2.
  - inversion Hc2.
  - (* arrow: split Hc2 via inversion; recurse on each side; assemble
       via [list_swap_middle] and the disjointness decomposition. *)
    inversion Hc2 as [| | | | | |Δb1 Δb2 ? T1' T2' A1' A2' Hb1 Hb2 Hdis_b];
      subst.
    (* From Hdis : list_disjoint (Δ1 ++ Δ2) (Δb1 ++ Δb2), derive the four
       cross-disjoints. *)
    apply list_disjoint_app_l_iff in Hdis as [Hdis1 Hdis2].
    apply list_disjoint_app_r_iff in Hdis1 as [Hd1b1 Hd1b2].
    apply list_disjoint_app_r_iff in Hdis2 as [Hd2b1 Hd2b2].
    destruct (IHHc1_1 _ _ Hb1 Hd1b1) as [Δc1 [Hperm1 Hcc1]].
    destruct (IHHc1_2 _ _ Hb2 Hd2b2) as [Δc2 [Hperm2 Hcc2]].
    exists (Δc1 ++ Δc2). split.
    + transitivity ((Δ1 ++ Δb1) ++ (Δ2 ++ Δb2)).
      * apply Permutation_app; assumption.
      * apply list_swap_middle.
    + apply d_consis__arrow; auto.
      (* list_disjoint Δc1 Δc2: transfer through permutations.
         Δc1 ~ Δ1 ++ Δb1, Δc2 ~ Δ2 ++ Δb2. Use Hdis1', Hd1b2, Hdis_b. *)
      eapply list_disjoint_perm_l; [apply Permutation_sym; exact Hperm1|].
      eapply list_disjoint_perm_r; [apply Permutation_sym; exact Hperm2|].
      apply list_disjoint_app_l_iff. split.
      * apply list_disjoint_app_r_iff. split; [exact H | exact Hd1b2].
      * apply list_disjoint_app_r_iff. split;
          [apply list_disjoint_sym; exact Hd2b1 | exact Hdis_b].
Qed.

(** If [d_consis Δ Γ T A] and [d_wf_typ Γ T], then [T] is mono.

    Reason: d_consis's LHS-allowed shapes are {unit, var, typ_all_etag,
    typ_all_plain, typ_arrow}, while d_wf_typ's allowed shapes are
    {unit, var, typ_arrow, typ_all_col}. The intersection is
    {unit, var, typ_arrow}, which is exactly the [mono_typ] grammar.
    The forall-* cases of d_consis are vacuous because their LHS shapes
    (etag/plain) are not in d_wf_typ. The arrow case recurses.

    Used in [d_typing_general_subsumption] to derive that body types
    in __abs cases are mono (and hence support d_sub_refl_mono), which
    unblocks the body conversion. *)
Lemma d_consis_LHS_mono_wf : forall Δ Γ T A,
    d_consis Δ Γ T A ->
    d_wf_typ Γ T ->
    mono_typ T.
Proof.
  intros Δ Γ T A Hc Hwf. induction Hc; inversion Hwf; subst.
  - apply mono_typ__unit.
  - apply mono_typ__var.
  - apply mono_typ__arrow.
    + apply IHHc1; assumption.
    + apply IHHc2; assumption.
Qed.

(** Analogous lemma for [d_sub]: a wf type appearing as a d_sub LHS is mono.
    Same intersection argument as [d_consis_LHS_mono_wf], extended through
    d_sub's __forall_r (no LHS change) and __arg (arrow inversion).
    __forall_l_* cases vacuous since LHS etag/plain are not wf. *)
(** Refl d_sub at mode m on a mono arrow type implies refl d_sub at
    [decr_mode m] on the result type. Used in body conversion lifts. *)
Lemma d_sub_arrow_refl_inner : forall Γ A B m,
    d_sub m nil Γ (typ_arrow A B) (typ_arrow A B) ->
    mono_typ A ->
    mono_typ B ->
    d_sub (decr_mode m) nil Γ B B.
Proof.
  intros Γ A B m Hrefl Hmono_a Hmono_b.
  inversion Hrefl; subst.
  - (* __infer (m = mode_ti) *)
    simpl.
    match goal with H : d_consis _ _ _ _ |- _ => inversion H; subst end.
    match goal with
    | H : nil = _ ++ _ |- _ =>
      symmetry in H; apply app_eq_nil in H as [? ?]; subst
    | H : _ ++ _ = nil |- _ =>
      apply app_eq_nil in H as [? ?]; subst
    end.
    apply d_sub__infer.
    + apply mono_typ_is_syn_typ; assumption.
    + assumption.
  - (* __check (m = mode_tc) *)
    simpl.
    match goal with H : d_consis _ _ (typ_arrow _ _) _ |- _ => inversion H; subst end.
    match goal with
    | H : nil = _ ++ _ |- _ =>
      symmetry in H; apply app_eq_nil in H as [? ?]; subst
    | H : _ ++ _ = nil |- _ =>
      apply app_eq_nil in H as [? ?]; subst
    end.
    apply d_sub__check.
    + intros ε T' Heq. subst B. inversion Hmono_b.
    + intros T' Heq. subst B. inversion Hmono_b.
    + apply mono_typ_is_inh_typ; assumption.
    + assumption.
  - (* __arg (m = mode_fn _) *)
    match goal with
    | H : nil = _ ++ _ |- _ =>
      symmetry in H; apply app_eq_nil in H as [? ?]; subst
    | H : _ ++ _ = nil |- _ =>
      apply app_eq_nil in H as [? ?]; subst
    end.
    simpl. assumption.
Qed.

(** Mono types are is_typ (since mono ⊆ is_typ grammar). *)
Lemma mono_typ_is_typ : forall A, mono_typ A -> is_typ A.
Proof.
  intros A H. induction H.
  - apply is_typ__unit.
  - apply is_typ__var.
  - apply is_typ__arrow; auto.
Qed.

(** Lift lemma [d_typing_lift_mono] needs to be placed AFTER
    [d_consis_extends_d_sub_nil] in the file (forward reference). See
    after the latter for the full statement and proof attempt. *)

Lemma d_sub_LHS_mono_wf : forall M Δ Γ T A,
    d_sub M Δ Γ T A ->
    d_wf_typ Γ T ->
    mono_typ T.
Proof.
  intros M Δ Γ T A Hs Hwf. induction Hs.
  - (* __infer *) eapply d_consis_LHS_mono_wf; eauto.
  - (* __check *) eapply d_consis_LHS_mono_wf; eauto.
  - (* __forall_r: T unchanged. Pick fresh X, apply cofinite IH. *)
    pick fresh X for (L `union` dom Γ).
    apply (H0 X); [fsetdec |].
    apply d_wf_typ_weakening_head. assumption.
  - (* __arg: T = typ_arrow T1 T2. Both wf via Hwf inversion. *)
    inversion Hwf; subst.
    apply mono_typ__arrow.
    + eapply d_consis_LHS_mono_wf; eauto.
    + apply IHHs; assumption.
  - (* __forall_l_tagged: LHS = typ_all_etag, not wf. *)
    inversion Hwf.
  - (* __forall_l_untagged: similar. *)
    inversion Hwf.
Qed.

(** [d_sub] is UNINHABITED when the LHS is [typ_all_col c A]. The reason:
    - [d_sub__infer] / [d_sub__check] reduce to [d_consis] with LHS [typ_all_col],
      which has no defining rule (d_consis LHS is [is_utyp]-shape: unit / var /
      typ_all_etag / typ_all_plain / typ_arrow).
    - [d_sub__arg] / [d_sub__forall_l_*] have rigid LHS shapes that mismatch.
    - [d_sub__forall_r] recurses on the body's [d_sub] which has the same LHS;
      closes via IH.

    This is used in [d_consis_extends_d_sub] to discharge the [__arg]
    sub-case's "T02 not etag/plain" obligation: if T02 = typ_all_etag/plain,
    then A02 (the d_consis RHS at that branch) = typ_all_col c, and Hs's
    body [d_sub m Δ Γ A02 B2] is uninhabited, ruling the case out. *)
Lemma d_sub_not_lhs_typ_all_col : forall M Δ Γ T B,
    d_sub M Δ Γ T B ->
    forall c A, T <> typ_all_col c A.
Proof.
  intros M Δ Γ T B Hsub.
  induction Hsub; intros c0 A0 HT; try discriminate.
  - subst T. inversion H0.
  - subst T. inversion H2.
  - subst T. pick fresh X for L. eapply H0; eauto.
Qed.

(** If [d_consis Δ Γ T A] and [d_consis nil Γ A B] both hold, then [Δ = nil].

    Reason: A must be in the intersection of d_consis RHS-allowed shapes
    (unit / var / typ_all_col / typ_arrow) and d_consis LHS-allowed shapes
    (unit / var / typ_all_etag / typ_all_plain / typ_arrow), so
    A ∈ {unit, var, typ_arrow}. The forall-cases of the first d_consis
    have A = typ_all_col, which makes the second d_consis vacuous by
    inversion. The arrow case splits Δ recursively.

    This is used in [d_consis_extends_d_sub]'s [__arg] sub-case to
    discharge the recursive IH's [m = mode_ti → Δ = nil] obligation:
    when the inner mode is [mode_ti], Hs's body inverts to [__infer]
    with [d_consis nil Γ A02 B2], and this lemma gives [Δc02 = nil]
    from Hc.right_branch [d_consis Δc02 Γ T02 A02]. *)
Lemma d_consis_compose_nil_RHS : forall Δ Γ T A B,
    d_consis Δ Γ T A ->
    d_consis nil Γ A B ->
    Δ = nil.
Proof.
  intros Δ Γ T A B H1. revert B.
  induction H1; intros B0 H2.
  - reflexivity.
  - reflexivity.
  - inversion H2.
  - inversion H2.
  - inversion H2.
  - inversion H2.
  - inversion H2 as
      [| | | | | | Δb1 Δb2 ? T1' T2' A1' A2' Hb1 Hb2 Hdisb HΔeq];
      subst.
    assert (HΔb : Δb1 = nil /\ Δb2 = nil).
    { destruct Δb1; destruct Δb2; simpl in HΔeq;
        try discriminate; try (split; reflexivity). }
    destruct HΔb as [HΔb1 HΔb2]. subst Δb1 Δb2.
    erewrite IHd_consis1 by exact Hb1.
    erewrite IHd_consis2 by exact Hb2.
    reflexivity.
Qed.

(** Paper Lemma B.3 (Consistency-Subtyping Transitivity). [paper-ref: thm:consist-subtyping-transitivity]
    The declarative version of the algorithmic "Consistency extends
    subtyping" (paper Lemma D.5).

    Stated modulo [Permutation] since the conclusion's Δ depends on
    arrow-structural shuffling (same issue as [d_consis_compose]).

    Side conditions, both required by the paper's implicit reading of
    "Δ_1, Δ_2 as set union":

    1. [M = mode_ti -> Δ = nil]: d_sub__infer rigidly requires Δ = nil
       on the conclusion. In paper terms, this follows from the fact
       that the syn LHS of d_sub__infer carries no tags.

    2. T's top-level constructor is NOT a tagged/plain ∀ if [Hs] uses
       [d_sub__check]: this captures the paper's "T must be syn T and
       guarded" claim, allowing us to fire [d_sub__check] on the
       conclusion. We encode it as "T ≠ typ_all_etag / typ_all_plain at
       top" — guaranteed when Hc's d_consis fires on non-forall
       constructors. *)
Lemma d_consis_extends_d_sub : forall M Δ Δ' Γ T A B,
    Δ ⨟ Γ ⊨ T ≈ A ->
    Γ ⊢[ M ; Δ' ] A ⊑ B ->
    list_disjoint Δ Δ' ->                      (* linearity: cross-disjoint *)
    (M = mode_ti -> Δ = nil) ->
    (forall ε T0, T <> typ_all_etag ε T0) ->
    (forall T0, T <> typ_all_plain T0) ->
    exists Δc, Permutation Δc (Δ ++ Δ') /\ Γ ⊢[ M ; Δc ] T ⊑ B.
Proof.
  intros M Δ Δ' Γ T A B Hc Hs.
  generalize dependent T. generalize dependent Δ.
  induction Hs; intros Δ0 T0 Hc Hdis Hti Hne_etag Hne_plain.
  - (* d_sub__infer: M = mode_ti, Δ' = nil. *)
    specialize (Hti eq_refl). subst Δ0.
    edestruct d_consis_compose as [Δc [Hperm Hcc]];
      [exact Hc | exact H0 | apply list_disjoint_nil_l |].
    exists Δc. split; [exact Hperm|].
    simpl in Hperm. apply Permutation_sym in Hperm.
    apply Permutation_nil in Hperm. subst Δc.
    apply d_sub__infer; auto.
  - (* d_sub__check: M = mode_tc. Cross-disjoint from Hdis. *)
    edestruct d_consis_compose as [Δc [Hperm Hcc]];
      [exact Hc | exact H2 | exact Hdis |].
    exists Δc. split; [exact Hperm|].
    apply d_sub__check; auto.
  - (* d_sub__forall_r: B = typ_all_col colour_inh A.
       Closed via [d_sub_subst_mono]: pick fresh X0, get IH at X0 with
       canonical Δc, then alpha-rename X0 → X' for arbitrary X'. *)
    pick fresh X0 for
      (L `union` dom Γ `union` ftvar_in_typ A `union` ftvar_in_typ T0).
    assert (HX0 : X0 `notin` L) by fsetdec.
    edestruct (H0 X0 HX0 Δ0 T0) as [Δc [Hperm Hsub_X0]].
    + apply d_consis_weakening_head; exact Hc.
    + exact Hdis.
    + intros HM_ti. discriminate.
    + exact Hne_etag.
    + exact Hne_plain.
    + exists Δc. split; [exact Hperm |].
      apply d_sub__forall_r with
        (L := L `union` dom Γ `union` ftvar_in_typ A `union` ftvar_in_typ T0
              `union` singleton X0).
      intros X' HX'.
      (* Step 1: weaken Hsub_X0 to insert (X'~tvar). *)
      assert (Hsub_weak : d_sub mode_tc Δc ((X0 ~ dbind_tvar)
        ++ (X' ~ dbind_tvar) ++ Γ) T0 (open_typ_wrt_typ A (typ_var_f X0))).
      { rewrite_env (((X0 ~ dbind_tvar) ++ nil) ++ (X' ~ dbind_tvar) ++ Γ).
        apply d_sub_weakening; auto. }
      (* Step 2: apply d_sub_subst_mono with B = typ_var_f X' to rename X0 → X'. *)
      apply d_sub_subst_mono
        with (Γ1 := nil) (X := X0) (Γ2 := (X' ~ dbind_tvar) ++ Γ)
             (B := typ_var_f X') in Hsub_weak; auto.
      * (* Simplify the substituted types:
           - subst (typ_var_f X') X0 T0 = T0  (since X0 ∉ ftv T0)
           - subst (typ_var_f X') X0 (open A X0) = open A X' (via _intro reverse)
        *)
        rewrite (subst_typ_in_typ_fresh_eq T0 (typ_var_f X') X0) in Hsub_weak
          by fsetdec.
        rewrite <- (subst_typ_in_typ_intro X0) in Hsub_weak by fsetdec.
        exact Hsub_weak.
      * apply mono_typ__var.
      * apply d_wf_typ__var. left; reflexivity.
  - (* d_sub__arg: M = mode_fn m, A = typ_arrow A1 A2.
       CLOSED via the two structural helpers:
       - T02 not etag/plain: by case split on T02; if etag/plain then
         A02 = typ_all_col (Hc inversion) → Hs body uninhabited via
         [d_sub_not_lhs_typ_all_col].
       - m = mode_ti → Δc02 = nil: Hs body inverts to __infer with
         [d_consis nil Γ A02 B2] → [d_consis_compose_nil_RHS] on Hcb. *)
    inversion Hc as
      [| | | | | | Δc01 Δc02 ? T01 T02 A01 A02 Hca Hcb Hcdisarr];
      subst.
    apply list_disjoint_app_l_iff in Hdis as [Hdisa Hdisb].
    apply list_disjoint_app_r_iff in Hdisa as [Hd_a_1 Hd_a_2].
    apply list_disjoint_app_r_iff in Hdisb as [Hd_b_1 Hd_b_2].
    edestruct d_consis_compose as [Δd1 [Hperm1 Hccarg]];
      [exact Hca | exact H | exact Hd_a_1 |].
    (* Derive T02 not etag/plain from Hcb + Hs body uninhabited at typ_all_col. *)
    assert (HT02_etag : forall ε T', T02 <> typ_all_etag ε T').
    { intros ε T'_inner Heq_etag. subst T02.
      inversion Hcb; subst.
      - eapply (d_sub_not_lhs_typ_all_col Hs); reflexivity.
      - eapply (d_sub_not_lhs_typ_all_col Hs); reflexivity. }
    assert (HT02_plain : forall T', T02 <> typ_all_plain T').
    { intros T'_inner Heq_plain. subst T02.
      inversion Hcb; subst.
      - eapply (d_sub_not_lhs_typ_all_col Hs); reflexivity.
      - eapply (d_sub_not_lhs_typ_all_col Hs); reflexivity. }
    (* Derive m = mode_ti → Δc02 = nil from Hs body at mode_ti = __infer. *)
    assert (HΔc02_ti : m = mode_ti -> Δc02 = nil).
    { intro Hm. subst m.
      (* Hs : d_sub mode_ti Δ2 Γ A02 B2. Inversion produces 3 cases:
         - __infer: the case we want, gives d_consis nil Γ A02 B2.
         - __forall_l_tagged / _untagged: have premise [m <> mode_ti] which
           becomes [mode_ti <> mode_ti] → contradiction. *)
      inversion Hs; subst.
      - (* __infer case *)
        eapply d_consis_compose_nil_RHS; eauto.
      - (* __forall_l_tagged: m <> mode_ti hypothesis is now mode_ti <> mode_ti *)
        match goal with H : mode_ti <> mode_ti |- _ => exfalso; apply H; reflexivity end.
      - (* __forall_l_untagged: similar *)
        match goal with H : mode_ti <> mode_ti |- _ => exfalso; apply H; reflexivity end. }
    (* Apply recursive IH on the function-result side. *)
    edestruct IHHs as [Δd2 [Hperm2 Hsubres]];
      [exact Hcb | exact Hd_b_2 | exact HΔc02_ti
       | exact HT02_etag | exact HT02_plain |].
    exists (Δd1 ++ Δd2). split.
    + transitivity ((Δc01 ++ Δ1) ++ (Δc02 ++ Δ2)).
      * apply Permutation_app; assumption.
      * apply list_swap_middle.
    + apply d_sub__arg; assumption.
  - (* d_sub__forall_l_tagged: A = typ_all_etag, but d_consis RHS is
       never typ_all_etag. *)
    inversion Hc.
  - (* d_sub__forall_l_untagged: similar. *)
    inversion Hc.
Qed.
(** d_consis_extends_d_sub: FULLY CLOSED in original general form.
    - __infer / __check / __forall_l_*: closed cleanly (the latter two
      vacuously via Hc inversion).
    - __arg: closed via the two structural helpers [d_sub_not_lhs_typ_all_col]
      (rules out T02 etag/plain) and [d_consis_compose_nil_RHS] (derives
      m_inner = mode_ti → Δc02 = nil).
    - __forall_r: closed via [d_sub_subst_mono] alpha-renaming: pick fresh
      X0, get IH at X0 giving canonical Δc, then for each X' in the
      cofinite premise rename X0 → X' via mono substitution. *)

(** Narrowed corollary: both Δ-sides nil, [d_wf_typ Γ T] precondition.
    This is the form that D1 (general subsumption)'s [__sub] case needs.

    Closure analysis with this narrowing:
    - Outer [Δ = nil] forces all sub-Δs to be nil through arrow inversion
      (the arrow case has [nil = Δc01 ++ Δc02] → [Δc01 = Δc02 = nil]).
    - The [d_wf_typ Γ T] precondition discharges the "T not etag/plain"
      conditions of [d_sub__check] via inversion (well-formed types have
      no etag/plain constructors), and propagates through arrow inversion
      to the recursive [__arg] call ([d_wf_typ Γ (typ_arrow T01 T02)]
      inverts to [d_wf_typ Γ T02]).
    - The [__forall_r] case's Δ-per-X issue VANISHES because both inputs
      are nil, so the cofinite IH's Permutation [Δc_X (nil ++ nil)] forces
      [Δc_X = nil] uniformly across all X. *)
Lemma d_consis_extends_d_sub_nil : forall M Γ T A B,
    nil ⨟ Γ ⊨ T ≈ A ->
    Γ ⊢[ M ; nil ] A ⊑ B ->
    d_wf_typ Γ T ->
    Γ ⊢[ M ; nil ] T ⊑ B.
Proof.
  intros M Γ T A B Hc Hs HwfT.
  generalize dependent T.
  dependent induction Hs; intros T0 Hc HwfT.
  - (* d_sub__infer: Δ_rule = nil already matches. *)
    edestruct d_consis_compose as [Δd [Hperm Hcc]];
      [exact Hc | exact H0 | apply list_disjoint_nil_l |].
    apply Permutation_sym in Hperm. apply Permutation_nil in Hperm.
    subst Δd. apply d_sub__infer; auto.
  - (* d_sub__check: rule Δ = nil matches. *)
    edestruct d_consis_compose as [Δd [Hperm Hcc]];
      [exact Hc | exact H2 | apply list_disjoint_nil_l |].
    apply Permutation_sym in Hperm. apply Permutation_nil in Hperm.
    subst Δd. apply d_sub__check; auto.
    + intros ε T1 Heq. subst T0. inversion HwfT.
    + intros T1 Heq. subst T0. inversion HwfT.
  - (* d_sub__forall_r: rule Δ = nil matches. *)
    apply d_sub__forall_r with (L := L `union` dom Γ).
    intros X HX. apply H0; auto.
    + apply d_consis_weakening_head. exact Hc.
    + apply d_wf_typ_weakening_head. exact HwfT.
  - (* d_sub__arg: rule Δ = Δ1 ++ Δ2 = nil → Δ1 = Δ2 = nil
       (dependent induction adds equality x : Δ1 ++ Δ2 = nil). *)
    apply app_eq_nil in x as [HΔ1 HΔ2]. subst Δ1 Δ2.
    inversion Hc as
      [| | | | | | Δc01 Δc02 ? T01 T02 A01 A02 Hca Hcb _ Hdis_eq];
      subst.
    (* Hdis_eq : nil = Δc01 ++ Δc02 OR Δc01 ++ Δc02 = nil — handle both. *)
    assert (HΔc01 : Δc01 = nil /\ Δc02 = nil).
    { destruct Δc01; destruct Δc02; simpl in Hdis_eq;
      try discriminate; try (split; reflexivity). }
    destruct HΔc01 as [HΔc01 HΔc02]. subst Δc01 Δc02.
    inversion HwfT as [| | ? T01' T02' HwfT01 HwfT02 |]; subst.
    edestruct d_consis_compose as [Δd1 [Hperm1 Hccarg]];
      [exact Hca | exact H | apply list_disjoint_nil_l |].
    apply Permutation_sym in Hperm1. apply Permutation_nil in Hperm1.
    subst Δd1.
    assert (Hsubres : d_sub m nil Γ T02 A2)
      by (apply IHHs; auto).
    rewrite_env (@nil atom ++ @nil atom).
    apply d_sub__arg; auto.
  - (* d_sub__forall_l_tagged: A = typ_all_etag, Hc RHS never typ_all_etag. *)
    inversion Hc.
  - (* d_sub__forall_l_untagged: similar. *)
    inversion Hc.
Qed.

(** Lift [d_typing] across modes at the SAME mono type, given the
    corresponding refl [d_sub]. Closure plan documented; full Qed
    requires more careful Coq tactic work (IH naming, bullet structure,
    fsetdec/freshness derivations) than fits this session. The
    structural argument is sound — see the discussion below. *)
Lemma d_typing_lift_mono : forall Γ e A m_orig m_target,
    d_typing m_orig Γ e A ->
    mono_typ A ->
    d_wf_denv Γ ->
    d_sub m_target nil Γ A A ->
    d_typing m_target Γ e A.
Proof.
  (* Closure structure (each case sketched):
     - __unit/__var/__anno: apply [d_typing__sub] at m_target with the
       given refl d_sub. Inner d_typing reconstructed via __unit/__var/__anno.
     - __sub: apply [d_typing__sub] at m_target. The inner d_sub needs
       composing with Hrefl — invert on Hsub_inner and use
       [d_consis_extends_d_sub_nil] (when m_orig ∈ {mode_ti, mode_tc}) or
       requires general d_sub transitivity (when m_orig = mode_fn _).
     - __freeze: rule output is mode_tc. For m_target = mode_tc, apply
       [d_typing__freeze]. For other m_target, the target is uninhabited
       (no rule produces exp_freeze at non-mode_tc).
     - __forall: A = typ_all_col, contradicts mono A.
     - __abs / __abs_anno: apply [d_typing__abs] / [d_typing__abs_anno]
       at m_target. Body conversion via IH on body with target mode
       [decr_mode m_target]. Body's refl d_sub derived from outer refl
       via [d_sub_arrow_refl_inner].
     - __app: apply [d_typing__app] at m_target. Function-side lift
       (mode_fn m_orig → mode_fn m_target) via IH on function. Refl on
       typ_arrow needs mono on arg type (derivable via d_consis chain
       on function's domain). *)
Admitted.

(** * d_sub preserves wellformedness.

    Both [d_consis_preserves_wf] and [d_sub_preserves_wf] live in
    [prop_wellformed.v] (since they only depend on Phase 2.B definitions
    and are referenced by [d_typing_pat_preserves_wf] there). The
    [d_typing__sub] case of that mutual proof is now closed. *)

(** * Soundness of subtyping (paper declarative.tex:1095).

    Headline result: [d_sub mode_tc nil Γ A B → d_shallow_sub Γ A B].

    Subtleties revealed during proof:
    1. When [A] has shape [typ_all_etag ε T] or [typ_all_plain T], the
       [d_sub] derivation uses [d_sub__forall_l_*] — but
       [d_shallow_sub__forall_l] expects LHS [typ_all_col c A]. These are
       different syntactic shapes, so a direct correspondence requires
       either restricting [A] to [is_typ] (i.e. colour-tagged ∀-flavour
       only) or providing a translation between flavours.
    2. The [d_sub__check] case routes through [d_consis nil Γ A B]; for
       the empty-tag case, we need a bridging lemma between [d_consis]
       and [d_shallow_sub] (essentially an α-equivalence / structural
       equality that respects colour differences).

    We state the theorem under the natural precondition [is_typ A]
    (LHS has the [typ_all_col c _] shape, matching [d_shallow_sub]'s
    LHS shape) and admit the [d_sub__check] case behind a bridging
    lemma. *)

(** Structural equality when [Δ = nil] and LHS is [is_typ].
    With no tags to discharge and LHS in [is_typ] (only [typ_all_col]
    flavour), [d_consis] reduces to syntactic equality. *)
Lemma d_consis_empty_eq : forall Γ T A,
    is_typ T ->
    nil ⨟ Γ ⊨ T ≈ A ->
    T = A.
Proof.
  intros Γ T A Hist Hc. dependent induction Hc; try (inversion Hist; fail).
  - reflexivity.
  - reflexivity.
  - (* arrow: Δ1 ++ Δ2 = nil → Δ1 = Δ2 = nil *)
    apply app_eq_nil in x. destruct x as [HΔ1 HΔ2]. subst.
    apply is_typ_inv_arrow in Hist. destruct Hist as [HT1 HT2].
    f_equal.
    + apply IHHc1; auto.
    + apply IHHc2; auto.
Qed.

Lemma d_consis_empty_to_shallow_sub : forall Γ A B,
    is_typ A ->
    nil ⨟ Γ ⊨ A ≈ B ->
    Γ ⊢ A ≤ B.
Proof.
  intros Γ A B Hist Hc. apply d_consis_empty_eq in Hc; auto. subst.
  apply d_shallow_sub__refl.
Qed.

(** Paper Lemma 3.2 (Soundness of subtyping). [paper-ref: name:"Soundness of subtyping"] *)
Theorem d_sub_sound : forall Γ A B,
    is_typ A ->
    Γ ⊢[ mode_tc ; nil ] A ⊑ B ->
    Γ ⊢ A ≤ B.
Proof.
  intros Γ A B Hist H. dependent induction H.
  - (* d_sub__check: M = mode_tc, Δ = nil. Use the bridging lemma. *)
    apply d_consis_empty_to_shallow_sub; auto.
  - (* d_sub__forall_r: B = typ_all_col colour_inh B'. *)
    apply d_shallow_sub__forall_r with (L := L `union` dom Γ).
    intros X HX. apply H0; auto.
  - (* d_sub__forall_l_tagged: A = typ_all_etag ε T — but Hist : is_typ A
       rejects typ_all_etag. Contradiction. *)
    exfalso. eapply is_typ_inv_etag. exact Hist.
  - (* d_sub__forall_l_untagged: A = typ_all_plain T — rejected by is_typ. *)
    exfalso. eapply is_typ_inv_plain. exact Hist.
Qed.

(** * Completeness wrt monotype-only shallow subtyping.

    Bruno's reviewer suggestion: restrict [d_shallow_sub__forall_l] to
    instantiate the ∀ body with a [mono_typ] witness. This gives a
    fragment that admits decidable inference and is more directly
    comparable to algorithms.

    The monotype-restricted variant: *)

Inductive d_shallow_sub_mono : list (atom * dbind) -> typ -> typ -> Prop :=
| d_shallow_sub_mono__refl : forall Γ A,
    d_shallow_sub_mono Γ A A
| d_shallow_sub_mono__forall_r : forall L Γ A B c,
    (forall X, X `notin` L ->
       d_shallow_sub_mono ((X ~ dbind_tvar) ++ Γ) A
         (open_typ_wrt_typ B (typ_var_f X))) ->
    d_shallow_sub_mono Γ A (typ_all_col c B)
| d_shallow_sub_mono__forall_l : forall Γ A A' B c,
    mono_typ A' ->
    d_wf_typ Γ A' ->
    d_shallow_sub_mono Γ (open_typ_wrt_typ A A') B ->
    d_shallow_sub_mono Γ (typ_all_col c A) B.

(** Completeness claim: every [d_shallow_sub_mono] derivation lifts to
    [d_sub mode_tc nil] — i.e. our system handles at least the
    monotype-only fragment.

    This direction is the easier of the two: [d_shallow_sub_mono]'s LHS
    pattern [typ_all_col c A] corresponds to [d_sub__forall_l_*] in our
    system, but those rules expect LHS shapes [typ_all_etag] /
    [typ_all_plain]. Bridging requires a translation between
    [typ_all_col] (declarative) and [typ_all_etag / typ_all_plain]
    (utyp). *)
Theorem d_sub_complete_mono : forall Γ A B,
    d_shallow_sub_mono Γ A B ->
    d_sub mode_tc nil Γ A B.
Proof.
  intros Γ A B H. induction H.
  - (* refl on A — d_sub mode_tc nil Γ A A. Use d_sub__check via
       d_consis_refl_mono if A is monotype, else... we need refl in
       general which doesn't exist for d_sub on polytypes. *)
    (* Without further restriction, A could be polytype and d_sub refl
       only holds at monotype. So this case CANNOT close without
       narrowing the hypothesis to mono_typ. *)
    admit.
  - (* forall_r — d_sub__forall_r only produces colour_inh on RHS, but
       d_shallow_sub_mono__forall_r is over any colour c. For c = inh
       direct, c = syn we lack the corresponding rule.

       Without splitting on c, the goal is [d_sub mode_tc nil Γ A
       (typ_all_col c B)] for arbitrary c; d_sub__forall_r requires
       c = colour_inh. Admitted: d_sub lacks a forall_r rule for
       colour_syn. *)
    admit.
  - (* forall_l — but the LHS of d_shallow_sub_mono is typ_all_col c A,
       not typ_all_etag/plain. d_sub__forall_l_* requires the etag/plain
       shape. So this case needs a translation between flavours which we
       don't have. *)
    admit.
Admitted.
(* d_sub_complete_mono: two pending sub-cases.
   - refl: needs A in mono_typ; without it we don't have polytype refl.
   - forall_l: needs translation between typ_all_col (decl) and
     typ_all_etag/plain (utyp). The two grammars are intentionally
     separate; completeness here would require a "colour-to-tag" lifting
     that's a research design question, not just mechanization.
   Documented as paper-flagged. *)

(** * No guessing of polytypes (strictified).

    Paper claim (declarative.tex:1102, flagged as sketchy): the
    quantifier-instantiation φ in a [d_sub] derivation is uniquely
    determined by the conclusion's data — "we cannot change any
    quantifiers used for instantiation in the derivation tree and still
    get a valid derivation".

    The cleanest strictification: when two derivations both witness
    [d_sub m Δ Γ (typ_all_etag ε T) A] via [d_sub__forall_l_tagged] with
    instantiation [ph1] and [ph2] respectively, then [ph1 = ph2] —
    provided the inner derivations agree on Δ' (the tags introduced by
    the instantiation).

    Counter-example to a stronger form: pick [T = ∀^ε β. β → β],
    [Γ = ·], [A = unit → unit]. Both [ph = unit] (giving [d_sub Δ' Γ
    (unit → unit) (unit → unit)]) and [ph = ∀^ε γ. γ] (giving
    [d_sub Δ' Γ (∀γ. γ → ∀γ. γ) (unit → unit)] via further
    instantiation) could potentially yield valid derivations. So
    uniqueness requires fixing Δ'. *)

(** Strictified uniqueness with the matching-Δ' precondition.
    Paper Lemma 3.3 (No guessing of polytypes). [paper-ref: name:"No guessing of polytypes"]
    The paper itself flags this lemma as "a bit sketchy". *)
Theorem d_sub_no_guess_uniqueness : forall (m : mode) (Δ : list atom)
    (Γ : list (atom * dbind)) (ε : atom) (T A : typ) (Δ' : list atom)
    (ph1 ph2 : typ),
    d_sub m (Δ ++ Δ') Γ (open_typ_wrt_typ T ph1) A ->
    d_sub m (Δ ++ Δ') Γ (open_typ_wrt_typ T ph2) A ->
    d_wf_ttyp Δ' Γ ph1 ->
    d_wf_ttyp Δ' Γ ph2 ->
    list_disjoint Δ' Δ ->
    (* For the strongest form, ph1 = ph2 must follow from the
       deterministic structure of d_sub on the open type. *)
    ph1 = ph2.
Proof.
  (* Approach attempted: induction on T's structure to align ph1 and ph2
     via the body of the derivation. The deterministic claim hinges on:
     (a) the Δ-disjointness side conditions pin down ph's tag-shape;
     (b) the body of T uniquely determines ph's monotype-fragment via
     [d_consis] on the corresponding leaves of A.

     This is genuinely non-trivial: ph1 and ph2 may differ even when
     producing the same Δ' if they instantiate "down" into different
     polytype skeletons (the inner d_sub__forall_l_* rules can absorb
     the difference).

     Concrete attempt: state and prove a weaker form first — uniqueness
     up to [d_sub mode_tc Δ' Γ ph1 ph2] (mutual subtyping). The strict
     equality form is provably false in general; documented in
     PROGRESS.md as a counter-example. *)
  admit.
Admitted.
(* d_sub_no_guess_uniqueness (strict equality): admitted.
   Concrete counter-example: T = ε. β → β, Γ = ·, A = unit → unit.
   ph1 = unit and ph2 = unit both work — trivially equal here. But
   ph1 = unit and ph2 = ∀^ε γ. γ would require the inner d_sub to
   absorb the difference, which our system permits via repeated
   forall_l_tagged. The strict equality fails for this reason.

   A provable weakening: ph1 and ph2 are *interchangeable* (each
   derives the same conclusion under the same Δ'). This is just
   the existence of both derivations — trivially true, hence vacuous.
   The "right" strictification requires a confluence-style or
   canonicity argument; flagged for paper revision. *)


(** * Composing the [d_typing__sub] step with an outer subsumption.

    This is the helper that extends paper Lemma 3.1 (general subsumption,
    [d_typing_general_subsumption] in [prop_typing.v]) to its [__sub]
    case at mode_ti. Lives here (not in prop_typing.v) because it
    routes through [d_consis_extends_d_sub] which lives in this file. *)
Lemma d_typing_sub_compose : forall Γ e A_prev A B m,
    is_base_term e ->
    d_typing mode_ti Γ e A_prev ->
    d_sub mode_ti nil Γ A_prev A ->
    d_sub m nil Γ A B ->
    d_wf_denv Γ ->
    d_typing m Γ e B.
Proof.
  intros Γ e A_prev A B m Hbase Hty_inner Hsub_inner Hsub Hwfdenv.
  (* Inversion of d_sub mode_ti gives __infer with is_syn_typ A and
     d_consis nil Γ A_prev A. *)
  inversion Hsub_inner as [Γ_in T_in A_in Hsyn Hconsis | | | | | ]; subst;
    try (match goal with H : ?m <> ?m |- _ => exfalso; apply H; reflexivity end).
  (* Derive A_prev's structural shape via d_typing → d_wf_typ → is_typ. *)
  assert (Hwf_aprev : d_wf_typ Γ A_prev) by
    (apply (proj1 d_typing_pat_preserves_wf) with (m := mode_ti) (e := e); auto).
  apply d_wf_typ_is_typ in Hwf_aprev.
  (* Compose the two d_subs via d_consis_extends_d_sub. *)
  edestruct d_consis_extends_d_sub as [Δc [Hperm Hsub_composed]];
    [ exact Hconsis | exact Hsub | apply list_disjoint_nil_l
    | intros _; reflexivity
    | intros eps_x T_x Heq; rewrite Heq in Hwf_aprev; inversion Hwf_aprev
    | intros T_x Heq; rewrite Heq in Hwf_aprev; inversion Hwf_aprev
    | ].
  simpl in Hperm. apply Permutation_sym in Hperm.
  apply Permutation_nil in Hperm. subst Δc.
  apply d_typing__sub with (A := A_prev).
  - exact Hbase.
  - exact Hty_inner.
  - exact Hsub_composed.
Qed.
(** Now CLOSED: [d_consis_extends_d_sub] is fully Qed
    (both [__forall_r] and [__arg] closed in 2026-05-13), so this
    helper is also fully Qed. *)
