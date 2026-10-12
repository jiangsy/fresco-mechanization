Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.algo_decl.def_subtyping.
Require Import src.fresco.algo_decl.def_typing.
Require Import src.fresco.algo_decl.prop_ctx_mono.
Require Import src.fresco.algo_decl.prop_stability.
Require Import src.fresco.algo.basic.prop_inc_strengthen.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo_decl.prop_refinement.
Require Import src.fresco.algo_decl.prop_precision.
Require Import src.fresco.algo.consistency.prop_completeness_consis.
Require Import src.fresco.algo.subtyping.prop_completeness_sub_precise.
Require Import src.fresco.algo.typing.prop_soundness_pat.

Set Implicit Arguments.

Open Scope fresco_ad_scope.

Reserved Notation "{{ Θ' ⪯ᶜᵗˣ Θ }}ad" (at level 0, Θ at level 74,
   format "'{{'  Θ'  ⪯ᶜᵗˣ  Θ  '}}ad'").

Inductive ad_ctx_precise : aenv -> aenv -> Prop :=
| ad_ctx_precise__nil :
    {{ nil ⪯ᶜᵗˣ nil }}ad
| ad_ctx_precise__copy : forall Θ' Θ x (b : abind),
    ~ abind_is_tm b ->
    {{ Θ' ⪯ᶜᵗˣ Θ }}ad ->
    {{ ((x ~ b) ++ Θ') ⪯ᶜᵗˣ ((x ~ b) ++ Θ) }}ad
| ad_ctx_precise__tm : forall Θ' Θ x (b' b : abind) (P' P : pskl),
    abind_to_pskl b' = Some P' ->
    abind_to_pskl b = Some P ->
    {{ Θ' ⨟ empty ⊢ₚᵣ P' ⊑ P }}ad ->
    {{ Θ' ⪯ᶜᵗˣ Θ }}ad ->
    {{ ((x ~ b') ++ Θ') ⪯ᶜᵗˣ ((x ~ b) ++ Θ) }}ad
where "{{ Θ' ⪯ᶜᵗˣ Θ }}ad" := (ad_ctx_precise Θ' Θ) : fresco_ad_scope.

Lemma ad_ctx_precise_dom : forall Θ' Θ,
  {{ Θ' ⪯ᶜᵗˣ Θ }}ad -> dom Θ' [=] dom Θ.
Proof.
  intros Θ' Θ H; induction H; simpl; fsetdec.
Qed.

Lemma ad_ctx_precise_tbinds_le : forall Θ' Θ,
  {{ Θ' ⪯ᶜᵗˣ Θ }}ad -> aenv_tbinds_le Θ Θ'.
Proof.
  intros Θ' Θ H; induction H; intros α b0 Hty Hb.
  - exact Hb.
  - destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> ->] | Hb'];
      [ unfold binds; simpl; left; reflexivity
      | apply binds_cons_3; apply IHad_ctx_precise; assumption ].
  - destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> ->] | Hb'].
    + exfalso. destruct b; simpl in *; solve [ contradiction | congruence ].
    + apply binds_cons_3; apply IHad_ctx_precise; assumption.
Qed.

Lemma ad_ctx_precise_binds_tm : forall Θ' Θ x (b : abind) (P : pskl),
  {{ Θ' ⪯ᶜᵗˣ Θ }}ad ->
  uniq Θ ->
  binds x b Θ ->
  abind_to_pskl b = Some P ->
  exists (b' : abind) (P' : pskl),
    binds x b' Θ' /\ abind_to_pskl b' = Some P' /\
    {{ Θ' ⨟ empty ⊢ₚᵣ P' ⊑ P }}ad.
Proof.
  intros Θ' Θ x b P H; induction H; intros Huq Hb HP.
  - inversion Hb.
  - destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> ->] | Hb'].
    +
      exfalso. apply H. destruct b0; simpl in *; try congruence; exact I.
    + inversion Huq; subst.
      destruct (IHad_ctx_precise ltac:(assumption) Hb' HP)
        as [b'' [P'' [Hb'' [HP'' Hprec]]]].
      exists b'', P''. split; [ apply binds_cons_3; exact Hb'' | ].
      split; [ exact HP'' | ].

      eapply ad_refine_syn_mono;
        [ exact Hprec
        | intros α b1 Hty Hb1; apply binds_cons_3; exact Hb1 ].
  - destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> ->] | Hb'].
    + rewrite H0 in HP. inversion HP; subst.
      exists b', P'. split; [ unfold binds; simpl; left; reflexivity | ].
      split; [ exact H | ].
      eapply ad_refine_syn_mono;
        [ exact H1
        | intros α b1 Hty Hb1; apply binds_cons_3; exact Hb1 ].
    + inversion Huq; subst.
      destruct (IHad_ctx_precise ltac:(assumption) Hb' HP)
        as [b'' [P'' [Hb'' [HP'' Hprec]]]].
      exists b'', P''. split; [ apply binds_cons_3; exact Hb'' | ].
      split; [ exact HP'' | ].
      eapply ad_refine_syn_mono;
        [ exact Hprec
        | intros α b1 Hty Hb1; apply binds_cons_3; exact Hb1 ].
Qed.

Theorem ad_ctx_precise_pat : forall M Θ e Q,
  {{ Θ ⊢ˢ[ M ] e ⦂ Q }}ad ->
  forall Θ',
  {{ Θ' ⪯ᶜᵗˣ Θ }}ad ->
  {{ ⊢ Θ }}a ->
  {{ ⊢ Θ' }}a ->
  {{ Θ' ⊢ˢ[ M ] e ⦂ Q }}ad.
Proof.
  intros M Θ e Q H; induction H; intros Θ' Hctx HwfΘ HwfΘ';
    pose proof (ad_ctx_precise_tbinds_le Hctx) as Htle.
  -
    apply ad_pat__unit;
      [ eapply a_wf_pskl_mono; eauto | eapply ad_pat_sub_mono; eauto ].
  -
    destruct (@ad_ctx_precise_binds_tm Θ' Θ x b P Hctx
                ltac:(apply a_wf_aenv_uniq; exact HwfΘ) H H0)
      as [b' [P' [Hb' [HP' Hprec]]]].
    assert (HwfQ' : {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a)
      by (eapply a_wf_pskl_mono; eauto).

    assert (HwfP : {{ Θ ⨟ empty ⊢ₚₛ P }}a).
    { destruct b; simpl in H0; try discriminate; inversion H0; subst.
      - apply a_wf_ptyp_to_wf_pskl.
        eapply a_wf_aenv_binds_var_typ_wf; eassumption.
      - eapply a_wf_aenv_binds_var_skl_wf; eassumption. }
    assert (HwfP' : {{ Θ' ⨟ empty ⊢ₚₛ P }}a)
      by (eapply a_wf_pskl_mono; eauto).
    eapply ad_pat__var with (b := b');
      [ exact Hb' | exact HP' | exact HwfQ' | ].
    rewrite pskl_to_uskl_via_bskl_syn.
    eapply ad_precise_extends_pat_sub with (Δ := empty) (P := P);
      [ exact Hprec
      | rewrite <- pskl_to_uskl_via_bskl_syn;
        eapply ad_pat_sub_mono; eauto
      | exact HwfΘ'
      | exact HwfP'
      | exact HwfQ'
      | intros Hd; discriminate ].
  -
    apply ad_pat__anno;
      [ eapply a_wf_pskl_mono; eauto | eapply ad_pat_sub_mono; eauto ].
  -
    apply ad_pat__freeze; auto.
  -
    assert (HwfP' : {{ Θ' ⨟ empty ⊢ₚₛ P }}a)
      by (eapply a_wf_pskl_mono; eauto).
    apply ad_pat__abs with (L := L `union` dom Θ');
      [ assumption | exact HwfP' | assumption | ].
    intros x Hx.
    apply H3;
      [ clear - Hx; fsetdec
      | apply ad_ctx_precise__tm with (P' := P) (P := P);
          [ reflexivity | reflexivity | apply ad_precise_refl; exact HwfP'
          | exact Hctx ]
      | apply a_wf_aenv__var;
          [ pose proof (ad_ctx_precise_dom Hctx) as Hd;
            clear - Hx Hd; fsetdec
          | exact H0
          | exact HwfΘ ]
      | apply a_wf_aenv__var;
          [ clear - Hx; fsetdec
          | exact HwfP'
          | exact HwfΘ' ] ].
  -
    assert (HwfA' : a_wf_ptyp Θ' A)
      by (eapply a_wf_ptyp_mono; eauto).
    apply ad_pat__abs_anno with (L := L `union` dom Θ') (B := B);
      [ assumption | exact HwfA' | assumption | assumption | ].
    intros x Hx.
    apply H4;
      [ clear - Hx; fsetdec
      | apply ad_ctx_precise__tm
          with (P' := ptyp_to_pskl A) (P := ptyp_to_pskl A);
          [ reflexivity | reflexivity
          | apply ad_precise_refl; apply a_wf_ptyp_to_wf_pskl; exact HwfA'
          | exact Hctx ]
      | apply a_wf_aenv__var_typ;
          [ pose proof (ad_ctx_precise_dom Hctx) as Hd;
            clear - Hx Hd; fsetdec
          | exact H0
          | exact HwfΘ ]
      | apply a_wf_aenv__var_typ;
          [ clear - Hx; fsetdec | exact HwfA' | exact HwfΘ' ] ].
  -
    eapply ad_pat__app;
      [ auto | eapply ad_refine_syn_mono; eauto | auto ].
  -
    apply ad_pat__abs_check with (L := L `union` dom Θ').
    intros x Hx.
    apply H0;
      [ clear - Hx; fsetdec
      | apply ad_ctx_precise__tm with (P' := pskl_ghost) (P := pskl_ghost);
          [ reflexivity | reflexivity
          | apply ad_precise_refl; apply a_wf_pskl__ghost | exact Hctx ]
      | apply a_wf_aenv__var;
          [ pose proof (ad_ctx_precise_dom Hctx) as Hd;
            clear - Hx Hd; fsetdec
          | apply a_wf_pskl__ghost | exact HwfΘ ]
      | apply a_wf_aenv__var;
          [ clear - Hx; fsetdec | apply a_wf_pskl__ghost | exact HwfΘ' ] ].
  -
    assert (HwfA' : a_wf_ptyp Θ' A)
      by (eapply a_wf_ptyp_mono; eauto).
    apply ad_pat__abs_anno_check with (L := L `union` dom Θ') (P := P);
      [ exact HwfA' | ].
    intros x Hx.
    apply H1;
      [ clear - Hx; fsetdec
      | apply ad_ctx_precise__tm
          with (P' := ptyp_to_pskl A) (P := ptyp_to_pskl A);
          [ reflexivity | reflexivity
          | apply ad_precise_refl; apply a_wf_ptyp_to_wf_pskl; exact HwfA'
          | exact Hctx ]
      | apply a_wf_aenv__var_typ;
          [ pose proof (ad_ctx_precise_dom Hctx) as Hd;
            clear - Hx Hd; fsetdec
          | exact H
          | exact HwfΘ ]
      | apply a_wf_aenv__var_typ;
          [ clear - Hx; fsetdec | exact HwfA' | exact HwfΘ' ] ].
Qed.
