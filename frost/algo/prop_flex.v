(** Soundness of the flexible-variable machinery (paper
    thm:sound-consistency, part 2): a [unifyvar] run is an identity
    information increase (dom-preserving) whose target equates the two
    subjects.  For monotypes, declarative consistency coincides with type
    equivalence under the context's definitions, so the declarative
    conclusion is stated with [a_tyequiv]; ≈/⊳-shaped corollaries are
    derived at their decorated-soundness use sites. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.ltac_utils.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_stability.

Set Implicit Arguments.

(* ===================================================================== *)
(*  Monotype / wf bookkeeping                                             *)
(* ===================================================================== *)

Lemma mono_ptyp_lc : forall A, mono_ptyp A -> lc_ptyp A.
Proof. intros A H; induction H; auto. Qed.

Lemma mono_ptyp_subst : forall A τ γ,
  mono_ptyp A -> mono_ptyp τ ->
  mono_ptyp (subst_ptyp_in_ptyp τ γ A).
Proof.
  intros * HA Hτ; induction HA; simpl; eauto using mono_ptyp.
  destruct (eq_var X γ); eauto using mono_ptyp.
Qed.

Lemma a_wf_ptyp_weaken : forall Θ Θ' A,
  (forall x b, binds x b Θ -> binds x b Θ') ->
  a_wf_ptyp Θ A ->
  a_wf_ptyp Θ' A.
Proof.
  intros * Hmon Hwf; revert Θ' Hmon; induction Hwf; intros Θ' Hmon;
    eauto using a_wf_ptyp.
  - apply a_wf_ptyp__var.
    destruct H as [Hb | [Hb | [τ Hb]]];
      [ left | right; left | right; right; exists τ ]; auto.
  - apply a_wf_ptyp__all with (L := L). intros X HX.
    apply H0; auto. intros x b Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? ?] | Hb']; subst;
      [ unfold binds; left; reflexivity
      | unfold binds; right; apply Hmon; auto ].
Qed.

Lemma a_tyequiv_weaken_cons : forall Θ (e : list (atom * abind)) A B,
  Θ ⊢ A ≡ᵗ B ->
  (e ++ Θ) ⊢ A ≡ᵗ B.
Proof.
  intros. eapply a_tyequiv_weaken; [ | eauto ].
  intros x b Hb. unfold binds; apply in_or_app; auto.
Qed.

(** Unfolding a definition inside a monotype: [A ≡ A[τ/γ̂]] when [γ̂:=τ]. *)
Lemma a_tyequiv_subst_def : forall Θ γ τ A,
  binds γ (abind_flex_mono_def τ) Θ ->
  mono_ptyp A ->
  lc_ptyp τ ->
  Θ ⊢ A ≡ᵗ (subst_ptyp_in_ptyp τ γ A).
Proof.
  intros * Hb Hm Hlc; induction Hm; simpl.
  - apply a_tyequiv__refl; auto.
  - destruct (eq_var X γ); subst.
    + apply a_tyequiv__flex_def; auto.
    + apply a_tyequiv__refl; auto.
  - apply a_tyequiv__arrow; auto.
Qed.

(* ===================================================================== *)
(*  Target weakening of information increase, and ⊴ cons congruences      *)
(* ===================================================================== *)

Lemma a_inc_target_weaken : forall Θ θ Θ' Ξ,
  Θ ≤[ θ ] Θ' ->
  a_suffix Ξ ->
  Θ ≤[ θ ] (Ξ ++ Θ').
Proof.
  intros * Hinc; revert Ξ; induction Hinc; intros Ξ0 HΞ0.
  - apply a_inc__empty. apply a_suffix_app; auto.
  - apply a_inc__flex; auto.
    eapply a_wf_ptyp_weaken; [ | eauto ].
    intros; unfold binds; apply in_or_app; auto.
  - apply a_inc__flex_def; auto.
    + eapply a_wf_ptyp_weaken; [ | eauto ].
      intros; unfold binds; apply in_or_app; auto.
    + apply a_tyequiv_weaken_cons; auto.
  - first [ rewrite <- app_assoc | rewrite app_assoc ].
    apply a_inc__var; auto using a_suffix_app.
  - first [ rewrite <- app_assoc | rewrite app_assoc ].
    apply a_inc__var_skl; auto using a_suffix_app.
  - first [ rewrite <- app_assoc | rewrite app_assoc ].
    apply a_inc__tvar; auto using a_suffix_app.
Qed.

(** ⊴ is preserved by pushing the SAME flexible declaration / definition /
    term-var / rigid entry on both sides. *)
Lemma a_isub_cons_flex : forall Θ Θ' γ,
  Θ ⊴ Θ' ->
  ((γ ~ abind_flex_mono) ++ Θ) ⊴ ((γ ~ abind_flex_mono) ++ Θ').
Proof.
  intros * [[θ [Hid Hinc]] Hd]. split.
  - exists ((γ, ptyp_var_f γ) :: θ). split.
    { constructor; auto. unfold is_id_entry; reflexivity. }
    apply a_inc__flex.
    + apply a_inc_target_weaken; auto.
      apply (a_suffix__cons γ (b := abind_flex_mono)); constructor.
    + apply a_wf_ptyp__var. right; left. unfold binds; left; reflexivity.
    + constructor.
  - intros α τ0 Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | ].
    simpl. unfold binds. right. apply Hd; auto.
Qed.

Lemma a_isub_cons_flex_def : forall Θ Θ' γ τ,
  Θ ⊴ Θ' ->
  lc_ptyp τ ->
  ((γ ~ abind_flex_mono_def τ) ++ Θ) ⊴ ((γ ~ abind_flex_mono_def τ) ++ Θ').
Proof.
  intros * [[θ [Hid Hinc]] Hd] Hlc. split.
  - exists ((γ, ptyp_var_f γ) :: θ). split.
    { constructor; auto. unfold is_id_entry; reflexivity. }
    apply a_inc__flex_def.
    + apply a_inc_target_weaken; auto.
      apply (a_suffix__cons γ (b := abind_flex_mono_def τ)); constructor.
    + apply a_wf_ptyp__var. right; right. exists τ.
      unfold binds; left; reflexivity.
    + constructor.
    + rewrite msubst_ptyp_id; auto.
      apply a_tyequiv__flex_def. unfold binds; left; reflexivity.
  - intros α τ0 Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb']; subst.
    + inversion Heq; subst. unfold binds; left; reflexivity.
    + unfold binds; right. apply Hd; auto.
Qed.

Lemma a_isub_cons_var_typ : forall Θ Θ' x A,
  Θ ⊴ Θ' ->
  ((x ~ abind_var_typ A) ++ Θ) ⊴ ((x ~ abind_var_typ A) ++ Θ').
Proof.
  intros * [[θ [Hid Hinc]] Hd]. split.
  - exists θ. split; auto.
    replace ((x ~ abind_var_typ A) ++ Θ')
      with (nil ++ (x ~ abind_var_typ (msubst_ptyp θ A)) ++ Θ')
      by (simpl; rewrite msubst_ptyp_id; auto).
    apply a_inc__var; auto. constructor.
  - intros α τ0 Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | ].
    simpl. unfold binds. right. apply Hd; auto.
Qed.

Lemma a_isub_cons_var_skl : forall Θ Θ' x P,
  Θ ⊴ Θ' ->
  ((x ~ abind_var_skl P) ++ Θ) ⊴ ((x ~ abind_var_skl P) ++ Θ').
Proof.
  intros * [[θ [Hid Hinc]] Hd]. split.
  - exists θ. split; auto.
    replace ((x ~ abind_var_skl P) ++ Θ')
      with (nil ++ (x ~ abind_var_skl (msubst_pskl θ P)) ++ Θ')
      by (simpl; rewrite msubst_pskl_id; auto).
    apply a_inc__var_skl; auto. constructor.
  - intros α τ0 Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | ].
    simpl. unfold binds. right. apply Hd; auto.
Qed.

(* ===================================================================== *)
(*  Soundness of variable unification (thm:sound-consistency part 2)      *)
(* ===================================================================== *)

Lemma a_unify_sound : forall Θ0 A B Θ1,
  a_unify Θ0 A B Θ1 ->
  a_wf_aenv Θ0 ->
  mono_ptyp A ->
  mono_ptyp B ->
  Θ0 ⊴ Θ1 /\ dom Θ1 [=] dom Θ0 /\ (Θ1 ⊢ A ≡ᵗ B).
Proof.
  intros * Hu; induction Hu; intros Hctx HmA HmB.
  - (* Flex-Flex-Id *)
    split; [ apply a_isub_refl | split; [ fsetdec | ] ].
    apply a_tyequiv__refl. constructor.
  - (* Flex-Flex-L : α̂ := β̂ *)
    split; [ | split; [ simpl; fsetdec | ] ].
    + split.
      * destruct (a_inc_refl_gen Θ0
          (Ξ0 := (α ~ abind_flex_mono_def (ptyp_var_f β))))
          as [θ0 [Hid0 Hinc0]].
        { apply (a_suffix__cons α (b := abind_flex_mono_def (ptyp_var_f β)));
            constructor. }
        exists ((α, ptyp_var_f α) :: θ0). split.
        { constructor; auto. unfold is_id_entry; reflexivity. }
        apply a_inc__flex; auto;
          try (apply a_wf_ptyp__var; right; right;
               exists (ptyp_var_f β); unfold binds; left; reflexivity);
          try constructor.
      * intros γ τ0 Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
          [ discriminate | ].
        simpl. unfold binds. right. auto.
    + apply a_tyequiv__flex_def. unfold binds; left; reflexivity.
  - (* Flex-Flex-R : β̂ := α̂ *)
    split; [ | split; [ simpl; fsetdec | ] ].
    + split.
      * destruct (a_inc_refl_gen Θ0
          (Ξ0 := (β ~ abind_flex_mono_def (ptyp_var_f α))))
          as [θ0 [Hid0 Hinc0]].
        { apply (a_suffix__cons β (b := abind_flex_mono_def (ptyp_var_f α)));
            constructor. }
        exists ((β, ptyp_var_f β) :: θ0). split.
        { constructor; auto. unfold is_id_entry; reflexivity. }
        apply a_inc__flex; auto;
          try (apply a_wf_ptyp__var; right; right;
               exists (ptyp_var_f α); unfold binds; left; reflexivity);
          try constructor.
      * intros γ τ0 Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
          [ discriminate | ].
        simpl. unfold binds. right. auto.
    + apply a_tyequiv__sym.
      apply a_tyequiv__flex_def. unfold binds; left; reflexivity.
  - (* Flex-Flex-Assign *)
    inversion Hctx; subst.
    match goal with
    | Hmτ : mono_ptyp τ |- _ =>
      destruct IHHu as [Hle [Hdom Heq1]]; auto using mono_ptyp_subst
    end.
    assert (Hlcτ : lc_ptyp τ) by (apply mono_ptyp_lc; assumption).
    assert (Hbγ : binds γ (abind_flex_mono_def τ)
                    ((γ ~ abind_flex_mono_def τ) ++ Θ1))
      by (unfold binds; left; reflexivity).
    split; [ | split ].
    + apply a_isub_cons_flex_def; auto.
    + simpl. fsetdec.
    + eapply a_tyequiv__trans.
      { eapply a_tyequiv_subst_def; eauto. }
      eapply a_tyequiv__trans.
      { apply a_tyequiv_weaken_cons. exact Heq1. }
      apply a_tyequiv__sym.
      eapply a_tyequiv_subst_def; eauto.
  - (* Flex-Flex-Skip (flexible γ̂, absent from the subjects) *)
    inversion Hctx; subst.
    destruct IHHu as [Hle [Hdom Heq1]]; auto.
    split; [ | split ].
    + apply a_isub_cons_flex; auto.
    + simpl. fsetdec.
    + apply a_tyequiv_weaken_cons; auto.
  - (* Flex-Flex-Skip' (rigid / term-var entry) *)
    destruct H as [Hb | [[Q Hb] | [Q Hb]]]; subst;
      inversion Hctx; subst;
      destruct IHHu as [Hle [Hdom Heq1]]; auto;
      (split; [ | split; [ simpl; fsetdec
                         | apply a_tyequiv_weaken_cons; auto ] ]).
    + apply a_isub_cons_tvar; auto.
    + apply a_isub_cons_var_typ; auto.
    + apply a_isub_cons_var_skl; auto.
Qed.

(* ===================================================================== *)
(*  Source-prefix machinery for assignvar (the [Θ0 | Ξ] split): flexible  *)
(*  declarations can be prepended to the SOURCE of an increase whenever   *)
(*  they are still visible in the target.                                 *)
(* ===================================================================== *)

Lemma a_wf_ptyp_lc : forall Θ A, a_wf_ptyp Θ A -> lc_ptyp A.
Proof.
  intros * H; induction H; auto.
Qed.

(** Declaration-only suffixes (the paper's "Ξ only contains declarations
    of flexible variables"). *)
Inductive a_decls : aenv -> Prop :=
| a_decls__nil : a_decls nil
| a_decls__cons : forall γ Ξ,
    a_decls Ξ ->
    a_decls ((γ ~ abind_flex_mono) ++ Ξ).

Lemma a_decls_suffix : forall Ξ, a_decls Ξ -> a_suffix Ξ.
Proof.
  intros Ξ H; induction H; [ constructor | ].
  apply (a_suffix__cons γ (b := abind_flex_mono)); auto; constructor.
Qed.

Lemma a_inc_prepend_flex_src : forall Θ θ Θ' γ,
  Θ ≤[ θ ] Θ' ->
  a_binds_tvar γ Θ' ->
  ((γ ~ abind_flex_mono) ++ Θ) ≤[ (γ, ptyp_var_f γ) :: θ ] Θ'.
Proof.
  intros * Hinc Hb.
  apply a_inc__flex; auto;
    try (apply a_wf_ptyp__var; auto);
    try constructor.
Qed.

Lemma a_isub_prepend_decls_src : forall Ξ Θ Θ',
  a_decls Ξ ->
  (forall γ, binds γ abind_flex_mono Ξ -> a_binds_tvar γ Θ') ->
  Θ ⊴ Θ' ->
  (Ξ ++ Θ) ⊴ Θ'.
Proof.
  intros Ξ; induction Ξ as [ | [γ b] Ξ' IH ]; intros Θ Θ' Hdecl Hvis Hle; auto.
  inversion Hdecl; subst.
  assert (Hle' : (Ξ' ++ Θ) ⊴ Θ').
  { apply IH; auto;
      try (intros γ0 Hb0; apply Hvis; unfold binds; right; auto). }
  destruct Hle' as [[θ [Hid Hinc]] Hd].
  split.
  - exists ((γ, ptyp_var_f γ) :: θ). split.
    { constructor; auto. unfold is_id_entry; reflexivity. }
    apply a_inc_prepend_flex_src; auto;
      try (apply Hvis; unfold binds; left; reflexivity).
  - intros α τ0 Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | auto ].
Qed.

(** Every declaration in the source of an identity increase is still
    tvar-ish in the target (specialization of the transport kit). *)
Lemma a_isub_binds_flex : forall Θ Θ' γ,
  Θ ⊴ Θ' ->
  binds γ abind_flex_mono Θ ->
  a_binds_tvar γ Θ'.
Proof.
  intros * [[θ [Hid Hinc]] _] Hb. eauto using a_inc_binds_flex.
Qed.

(** [guessMono] emits a declaration-only fresh suffix. *)
Lemma a_decls_app : forall Ξ1 Ξ2,
  a_decls Ξ1 -> a_decls Ξ2 -> a_decls (Ξ1 ++ Ξ2).
Proof.
  intros * H1 H2; induction H1; simpl; auto.
  apply (a_decls__cons γ); auto.
Qed.

Lemma a_guess_mono_decls : forall Θ P βs τ,
  a_guess_mono Θ P βs τ ->
  a_decls βs.
Proof.
  intros * H;
    induction H as [ Θ α | Θ P Ξ A Hg IH | Θ α | Θ
                   | Θ P Q Ξ1 Ξ2 A B Hg1 IH1 Hg2 IH2
                   | L Θ P Ξ A Hg IH ].
  - apply (a_decls__cons α). constructor.
  - auto.
  - constructor.
  - constructor.
  - apply a_decls_app; auto.
  - pick fresh X. eauto.
Qed.
