Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo.basic.prop_metasubst_composition.
Require Import src.fresco.algo.basic.prop_context_normalization.

Set Implicit Arguments.

Lemma a_inc_mid_strip_flex : forall Ξ β Θ0 κ Θ,
  a_decls Ξ ->
  κ ∷ (Ξ ++ (β ~ abind_flex_mono) ++ Θ0) ⊑ Θ ->
  exists κ1 τ κ2,
    κ = κ1 ++ (β, τ) :: κ2 /\
    dom κ1 [=] dom Ξ /\
    κ2 ∷ Θ0 ⊑ Θ /\
    κ1 ++ κ2 ∷ (Ξ ++ Θ0) ⊑ Θ.
Proof.
  induction Ξ as [ | [a b] Ξ' IH ]; intros β Θ0 κ Θ Hdec Hinc.
  -
    simpl in Hinc.
    inversion Hinc as [ | Θs κs Θt βs τ Hinc' Hwfτ Hmτ [Heqβ Heqκ] Heqt
                      | | | | ]; subst.
    exists (@nil (atom * ptyp)), τ, κs. simpl.
    split; [ reflexivity | ].
    split; [ clear; fsetdec | ].
    split; [ exact Hinc' | exact Hinc' ].
  -
    inversion Hdec as [ | α1 Ξ'' Hdec' [Heqγ HeqΞ] ]; subst.
    simpl in Hinc.
    inversion Hinc as [ | Θs κs Θt as' τ Hinc' Hwfτ Hmτ [Heqa Heqκ] Heqt
                      | | | | ]; subst.
    destruct (IH _ _ _ _ Hdec' Hinc')
      as [κ1 [τ2 [κ2 [Heqκ [Hdom [Hinc2 Hrec]]]]]].
    exists ((a, τ) :: κ1), τ2, κ2. simpl.
    split; [ rewrite Heqκ; reflexivity | ].
    split; [ clear - Hdom; simpl_env; fsetdec | ].
    split; [ exact Hinc2 | ].
    apply a_inc__flex; auto.
Qed.

Lemma a_assign_unify_consis_flex_preserve :
  (forall Θ0 Ξ α P Θ1,
     {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
     forall α1, a_flex_tvar (Ξ ++ Θ0) α1 -> a_flex_tvar Θ1 α1) /\
  (forall Θ0 α β Θ1,
     {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a ->
     forall α1, a_flex_tvar Θ0 α1 -> a_flex_tvar Θ1 α1) /\
  (forall Δ1 Δ2 Θ0 P0 P P' Θ1,
     {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ P' ⊣ Θ1 }}a ->
     forall α1, a_flex_tvar Θ0 α1 -> a_flex_tvar Θ1 α1).
Proof.
  apply a_assign_unify_consis_mutind;
    intros;
    try match goal with
    | H : _ = abind_tvar \/ (exists _, _ = abind_var_typ _) \/ (exists _, _ = abind_var_skl _) |- _ =>
        destruct H as [-> | [[? ->] | [? ->]]]
    end;
    match goal with |- a_flex_tvar _ ?x =>
      repeat match goal with
      | IH : forall y, a_flex_tvar _ y -> _ |- _ => specialize (IH x)
      end
    end;
    simpl_env in *;
    repeat rewrite a_flex_tvar_cons_tvar_any in *;
    repeat rewrite a_flex_tvar_cons_nonflex in * by (split; intros; discriminate);
    repeat rewrite a_flex_tvar_app_iff in *;
    repeat rewrite a_flex_tvar_one_flex in * by eauto;
    try tauto.
  all: match goal with
  | H : context [a_flex_tvar (?c ~ ?bd) ?x] |- _ =>
      assert (~ a_flex_tvar (c ~ bd) x)
        by (apply a_flex_tvar_one_nonflex; intros; discriminate); tauto
  end.

Qed.

Lemma a_wf_aenv_binds_var_typ_ftv : forall Θ x A,
  {{ ⊢ Θ }}a -> binds x (abind_var_typ A) Θ ->
  ftvar_in_ptyp A [<=] dom Θ.
Proof.
  intros Θ x A Hwf; induction Hwf; intros Hb; try solve [ inversion Hb ];
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq1 Heq2] | Hb'];
    try discriminate;
    try solve [ pose proof (IHHwf Hb') as Hs; simpl; clear - Hs; fsetdec ].

  injection Heq2 as Heq2. subst.
  pose proof (a_wf_ptyp_ftv_dom H0) as Hs. simpl. clear - Hs. fsetdec.
Qed.

Lemma a_wf_aenv_binds_var_skl_wf : forall Θ x P,
  {{ ⊢ Θ }}a -> binds x (abind_var_skl P) Θ ->
  {{ Θ ⨟ empty ⊢ₚₛ P }}a.
Proof.
  intros Θ x P Hwf; induction Hwf; intros Hb; try solve [ inversion Hb ];
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq1 Heq2] | Hb'];
    try discriminate;
    try solve [ eapply a_wf_pskl_weaken;
                  [ intros ? ? Hb2; apply binds_cons_3; exact Hb2
                  | exact (IHHwf Hb') ] ].

  injection Heq2 as Heq2. subst.
  eapply a_wf_pskl_weaken;
    [ intros ? ? Hb2; apply binds_cons_3; exact Hb2 | exact H0 ].
Qed.

Lemma a_wf_aenv_binds_var_skl_ftv : forall Θ x P,
  {{ ⊢ Θ }}a -> binds x (abind_var_skl P) Θ ->
  ftvar_in_pskl P [<=] dom Θ.
Proof.
  intros * Hwf Hb. apply a_scope_pskl_ftv_dom.
  eapply a_scope_pskl_of_wf, a_wf_aenv_binds_var_skl_wf; eauto.
Qed.

Lemma a_suffix_no_var_typ : forall Ξ x A,
  a_suffix Ξ -> binds x (abind_var_typ A) Ξ -> False.
Proof.
  intros Ξ x A Hsuf; induction Hsuf; intros Hb; [ inversion Hb | ].
  destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq1 Heq2] | Hb'];
    [ subst; inversion H | auto ].
Qed.

Lemma a_suffix_no_var_skl : forall Ξ x P,
  a_suffix Ξ -> binds x (abind_var_skl P) Ξ -> False.
Proof.
  intros Ξ x P Hsuf; induction Hsuf; intros Hb; [ inversion Hb | ].
  destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq1 Heq2] | Hb'];
    [ subst; inversion H | auto ].
Qed.
