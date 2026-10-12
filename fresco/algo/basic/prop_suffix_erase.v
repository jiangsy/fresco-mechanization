Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
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
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.algo_decl.def_subtyping.
Require Import src.fresco.algo_decl.def_typing.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo_decl.prop_ctx_mono.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo.consistency.prop_consis_monotype_equiv.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo_decl.prop_refinement.
Require Import src.fresco.prop_tag.
Require Import src.fresco.algo_decl.prop_subtyping.
Require Import src.fresco.algo.subtyping.prop_soundness_subtag.
Require Import src.fresco.algo.typing.prop_soundness_pat.
Require Import src.fresco.decl.prop_basic.

Set Implicit Arguments.

Definition subst_abind (τ : ptyp) (α : atom) (bd : abind) : abind :=
  match bd with
  | abind_tvar            => abind_tvar
  | abind_var_typ A       => abind_var_typ (subst_ptyp_in_ptyp τ α A)
  | abind_var_skl P       => abind_var_skl
                               (subst_pskl_in_pskl (ptyp_to_pskl τ) α P)
  | abind_flex_mono       => abind_flex_mono
  | abind_flex_mono_def A => abind_flex_mono_def (subst_ptyp_in_ptyp τ α A)
  end.

Fixpoint subst_aenv (τ : ptyp) (α : atom) (Θ : aenv) : aenv :=
  match Θ with
  | nil           => nil
  | (x, bd) :: Θ' => (x, subst_abind τ α bd) :: subst_aenv τ α Θ'
  end.

Lemma binds_subst_aenv : forall τ α x bd Θ,
  binds x bd Θ -> binds x (subst_abind τ α bd) (subst_aenv τ α Θ).
Proof.
  intros τ α x bd Θ; induction Θ as [ | [y bd'] Θ' IH ]; intros Hb.
  - inversion Hb.
  - simpl. unfold binds in *; simpl in *.
    destruct Hb as [Heq | Hb].
    + inversion Heq; subst. left; reflexivity.
    + right. apply IH. exact Hb.
Qed.

Definition solves_flex (τ : ptyp) (α : atom) (b : abind) (Θ0 : aenv) : Prop :=
  mono_ptyp τ /\ a_wf_ptyp Θ0 τ /\ α `notin` ftvar_in_ptyp τ /\
  (b = abind_flex_mono \/ b = abind_flex_mono_def τ).

Lemma solves_flex_mono : forall τ α b Θ0, solves_flex τ α b Θ0 -> mono_ptyp τ.
Proof. intros τ α b Θ0 [Hm _]. exact Hm. Qed.

Lemma solves_flex_lc : forall τ α b Θ0, solves_flex τ α b Θ0 -> lc_ptyp τ.
Proof. intros. apply mono_ptyp_lc. eapply solves_flex_mono; eassumption. Qed.

Lemma solves_flex_wf : forall τ α b Θ0, solves_flex τ α b Θ0 -> a_wf_ptyp Θ0 τ.
Proof. intros τ α b Θ0 [_ [Hw _]]. exact Hw. Qed.

Lemma solves_flex_fresh : forall τ α b Θ0, solves_flex τ α b Θ0 -> α `notin` ftvar_in_ptyp τ.
Proof. intros τ α b Θ0 [_ [_ [Hf _]]]. exact Hf. Qed.

Lemma solves_flex_def_eq : forall τs α0 b Θa Θ0 τ,
  solves_flex τs α0 b Θ0 ->
  uniq (Θa ++ (α0 ~ b) ++ Θ0) ->
  binds α0 (abind_flex_mono_def τ) (Θa ++ (α0 ~ b) ++ Θ0) ->
  τ = τs.
Proof.
  intros * Hs Hu Hbd.
  assert (Hb : abind_flex_mono_def τ = b) by (eapply binds_mid_eq; eassumption).
  destruct Hs as [_ [_ [_ [Heqb | Heqb]]]];
    rewrite Heqb in Hb; [ discriminate | inversion Hb; reflexivity ].
Qed.

Lemma solves_flex_open_subst_uskl : forall {τs α0 b Θ0 X β},
  solves_flex τs α0 b Θ0 -> α0 <> β ->
  open_uskl_wrt_uskl (subst_uskl_in_uskl (ptyp_to_uskl_syn τs) α0 X) (uskl_var_f β)
  = subst_uskl_in_uskl (ptyp_to_uskl_syn τs) α0 (open_uskl_wrt_uskl X (uskl_var_f β)).
Proof.
  intros * Hs Hβ. apply subst_uskl_in_uskl_open_uskl_wrt_uskl_var; [ exact Hβ | ].
  apply mono_ptyp_to_uskl_syn_lc; eapply solves_flex_mono; eassumption.
Qed.

Lemma solves_flex_open_subst_bskl : forall {τs α0 b Θ0 X β},
  solves_flex τs α0 b Θ0 -> α0 <> β ->
  open_bskl_wrt_bskl (subst_bskl_in_bskl (ptyp_to_bskl_syn τs) α0 X) (bskl_var_f β)
  = subst_bskl_in_bskl (ptyp_to_bskl_syn τs) α0 (open_bskl_wrt_bskl X (bskl_var_f β)).
Proof.
  intros * Hs Hβ. apply subst_bskl_in_bskl_open_bskl_wrt_bskl_var; [ exact Hβ | ].
  apply mono_ptyp_to_bskl_syn_lc; eapply solves_flex_mono; eassumption.
Qed.

Lemma solves_flex_open_subst_pskl : forall {τs α0 b Θ0 X β},
  solves_flex τs α0 b Θ0 -> α0 <> β ->
  open_pskl_wrt_pskl (subst_pskl_in_pskl (ptyp_to_pskl τs) α0 X) (pskl_var_f β)
  = subst_pskl_in_pskl (ptyp_to_pskl τs) α0 (open_pskl_wrt_pskl X (pskl_var_f β)).
Proof.
  intros * Hs Hβ. apply subst_pskl_in_pskl_open_pskl_wrt_pskl_var; [ exact Hβ | ].
  apply ptyp_to_pskl_lc; eapply solves_flex_lc; eassumption.
Qed.

Lemma binds_subst_strip_mid : forall τ α (b : abind) Θa Θ0 x bd,
  binds x bd (Θa ++ (α ~ b) ++ Θ0) ->
  x <> α ->
  binds x (subst_abind τ α bd) (subst_aenv τ α (Θa ++ Θ0)).
Proof.
  intros τ α b Θa Θ0 x bd Hb Hne.
  apply binds_subst_aenv.
  apply binds_app_1 in Hb as [Hb | Hb]; [ apply binds_app_2; exact Hb | ].
  apply binds_app_1 in Hb as [Hb | Hb]; [ | apply binds_app_3; exact Hb ].
  destruct Hb as [Heq | []]. inversion Heq; subst. contradiction.
Qed.

Lemma binds_def_subst_strip_mid : forall τs α0 (b : abind) Θa Θ0 α τ,
  binds α (abind_flex_mono_def τ) (Θa ++ (α0 ~ b) ++ Θ0) ->
  α <> α0 ->
  binds α (abind_flex_mono_def (subst_ptyp_in_ptyp τs α0 τ))
    (subst_aenv τs α0 (Θa ++ Θ0)).
Proof.
  intros * Hb Hne.
  change (abind_flex_mono_def (subst_ptyp_in_ptyp τs α0 τ))
    with (subst_abind τs α0 (abind_flex_mono_def τ)).
  eapply binds_subst_strip_mid; eassumption.
Qed.

Lemma a_binds_tvar_subst_mid : forall τ α (b : abind) Θa Θ0 β,
  a_binds_tvar β (Θa ++ (α ~ b) ++ Θ0) ->
  β <> α ->
  a_binds_tvar β (subst_aenv τ α (Θa ++ Θ0)).
Proof.
  intros τ α b Θa Θ0 β H Hne.
  destruct H as [Hb | [Hb | [τ0 Hb]]];
    pose proof (binds_subst_strip_mid τ _ _ _ _ Hb Hne) as Hb'; simpl in Hb'.
  - left; exact Hb'.
  - right; left; exact Hb'.
  - right; right; eexists; exact Hb'.
Qed.

Lemma a_binds_tvar_subst_tail : forall τ α Θa Θ0 β,
  a_binds_tvar β Θ0 -> a_binds_tvar β (subst_aenv τ α (Θa ++ Θ0)).
Proof.
  intros τ α Θa Θ0 β H.
  destruct H as [Hb | [Hb | [τ0 Hb]]].
  - left. change abind_tvar with (subst_abind τ α abind_tvar).
    apply binds_subst_aenv. apply binds_app_3. exact Hb.
  - right; left.
    change abind_flex_mono with (subst_abind τ α abind_flex_mono).
    apply binds_subst_aenv. apply binds_app_3. exact Hb.
  - right; right. exists (subst_ptyp_in_ptyp τ α τ0).
    change (abind_flex_mono_def (subst_ptyp_in_ptyp τ α τ0))
      with (subst_abind τ α (abind_flex_mono_def τ0)).
    apply binds_subst_aenv. apply binds_app_3. exact Hb.
Qed.

Lemma a_wf_ptyp_tbinds_mono : forall Θ A,
  a_wf_ptyp Θ A ->
  forall Θ', (forall β, a_binds_tvar β Θ -> a_binds_tvar β Θ') ->
  a_wf_ptyp Θ' A.
Proof.
  intros Θ A H; induction H; intros Θ' Hmon.
  - apply a_wf_ptyp__unit.
  - apply a_wf_ptyp__var; auto.
  - apply a_wf_ptyp__arrow; auto.
  - apply a_wf_ptyp__all with (L := L). intros β Hβ. apply H0; [ exact Hβ | ].
    intros γ Hγ. destruct (γ == β) as [-> | Hne].
    + unfold a_binds_tvar. left. unfold binds; simpl; left; reflexivity.
    + apply a_binds_tvar_weaken_cons. apply Hmon.
      unfold a_binds_tvar in Hγ |- *.
      destruct Hγ as [Hb | [Hb | [τ0 Hb]]];
        [ left | right; left | right; right; exists τ0 ];
        (unfold binds in Hb; simpl in Hb;
         destruct Hb as [He | Hb];
         [ inversion He; subst; contradiction | exact Hb ]).
Qed.

Lemma a_wf_ptyp_subst_tail : forall τ α Θa Θ0,
  a_wf_ptyp Θ0 τ -> a_wf_ptyp (subst_aenv τ α (Θa ++ Θ0)) τ.
Proof.
  intros. eapply a_wf_ptyp_tbinds_mono; [ eassumption | ].
  intros β Hβ. eapply a_binds_tvar_subst_tail; eassumption.
Qed.

Lemma a_wf_ptyp_subst_mid : forall Θ A,
  a_wf_ptyp Θ A ->
  forall τ α0 (b : abind) Θa Θ0,
  Θ = Θa ++ (α0 ~ b) ++ Θ0 ->
  solves_flex τ α0 b Θ0 ->
  a_wf_ptyp (subst_aenv τ α0 (Θa ++ Θ0)) (subst_ptyp_in_ptyp τ α0 A).
Proof.

  intros Θ A H; induction H; intros τ α0 b Θa Θ0 Heq Hs; subst; simpl.
  - apply a_wf_ptyp__unit.
  - destruct_if as [Heqα | Hne].
    + subst. apply a_wf_ptyp_subst_tail. eapply solves_flex_wf; eassumption.
    + apply a_wf_ptyp__var. eapply a_binds_tvar_subst_mid; eassumption.
  - apply a_wf_ptyp__arrow; eauto.
  - apply a_wf_ptyp__all with (L := L `union` singleton α0). intros β Hβ.
    rewrite subst_ptyp_in_ptyp_open_ptyp_wrt_ptyp_var;
      [ | clear - Hβ; fsetdec | eapply solves_flex_lc; eassumption ].
    apply (H0 β ltac:(clear - Hβ; solve_notin_auto) τ α0 b ((β ~ abind_tvar) ++ Θa) Θ0);
      [ reflexivity | exact Hs ].
Qed.

Lemma subst_aenv_minus : forall τ α Θ Δ,
  subst_aenv τ α (aenv_minus Θ Δ) = aenv_minus (subst_aenv τ α Θ) Δ.
Proof.
  intros τ α Θ Δ; induction Θ as [ | [y bd] Θ IH ]; [ reflexivity | ].
  unfold aenv_minus in *; simpl.
  destruct (AtomSetImpl.mem y Δ); simpl; [ exact IH | f_equal; exact IH ].
Qed.

Lemma a_wf_ptyp_mono_aenv_minus : forall Θ Δ τ,
  mono_ptyp τ -> a_wf_ptyp Θ τ ->
  Δ ∩ ftvar_in_ptyp τ [=] empty ->
  a_wf_ptyp (aenv_minus Θ Δ) τ.
Proof.
  intros Θ Δ τ Hm; induction Hm; intros Hw Hd; inversion Hw; subst; simpl in Hd.
  - apply a_wf_ptyp__unit.
  - apply a_wf_ptyp__var. apply a_binds_tvar_aenv_minus.
    split; [ assumption | ].
    intros Hin. assert (Hx : α `in` Δ ∩ singleton α)
      by (clear - Hin; fsetdec).
    rewrite Hd in Hx. clear - Hx; fsetdec.
  - apply a_wf_ptyp__arrow;
      [ apply IHHm1 | apply IHHm2 ]; try assumption; clear - Hd; fsetdec.
Qed.

Lemma a_wf_pskl_subst_mid : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  forall τ α0 (b : abind) Θa Θ0,
  Θ = Θa ++ (α0 ~ b) ++ Θ0 ->
  solves_flex τ α0 b Θ0 ->
  α0 `notin` Δ ->
  Δ ∩ ftvar_in_ptyp τ [=] empty ->
  {{ (subst_aenv τ α0 (Θa ++ Θ0)) ⨟ Δ
    ⊢ₚₛ (subst_pskl_in_pskl (ptyp_to_pskl τ) α0 P) }}a.
Proof.
  intros Θ Δ P H; induction H; intros τ α0 b Θa Θ0 Heq Hs Hα0 Hd; subst; simpl.
  - apply a_wf_pskl__unit.
  - destruct_if as [Heqα | Hne].
    + subst. apply a_wf_pskl_mono_ptyp;
        [ eapply solves_flex_mono; eassumption | apply a_wf_ptyp_subst_tail;
                             eapply solves_flex_wf; eassumption ].
    + apply a_wf_pskl__var. eapply a_binds_tvar_subst_mid; eassumption.
  - apply a_wf_pskl__arrow; eauto.
  - apply a_wf_pskl__all
      with (L := L `union` singleton α0 `union` ftvar_in_ptyp τ). intros β Hβ.
    rewrite (solves_flex_open_subst_pskl Hs) by (clear - Hβ; fsetdec).
    change ((β ~ abind_tvar) ++ subst_aenv τ α0 (Θa ++ Θ0))
      with (subst_aenv τ α0 (((β ~ abind_tvar) ++ Θa) ++ Θ0)).
    apply (H0 β ltac:(clear - Hβ; solve_notin_auto) τ α0 b
             ((β ~ abind_tvar) ++ Θa) Θ0);
      [ reflexivity | exact Hs | clear - Hα0 Hβ; fsetdec
      | clear - Hd Hβ; fsetdec ].
  - apply a_wf_pskl__ghost.
  - apply a_wf_pskl__univ_ghost.
    + apply guarded_pskl_subst;
        [ exact H
        | apply mono_ptyp_to_pskl_guarded; eapply solves_flex_mono; eassumption
        | apply ptyp_to_pskl_lc; eapply solves_flex_lc; eassumption ].
    + rewrite <- subst_aenv_minus, aenv_minus_app.
      destruct Hs as [Hm [Hw [Hfr Hb]]].
      apply (IHa_wf_pskl τ α0 b (aenv_minus Θa Δ) (aenv_minus Θ0 Δ));
        [ rewrite aenv_minus_app; f_equal;
          apply aenv_minus_cons_notin; exact Hα0
        | repeat split; [ exact Hm | | exact Hfr | exact Hb ];
          apply a_wf_ptyp_mono_aenv_minus; assumption
        | clear; fsetdec | clear; fsetdec ].
Qed.

Lemma a_tyequiv_subst_mid : forall Θ A A',
  {{ Θ ⊢ A ≡ᵗ A' }}a ->
  forall τs α0 (b : abind) Θa Θ0,
  Θ = Θa ++ (α0 ~ b) ++ Θ0 ->
  solves_flex τs α0 b Θ0 ->
  uniq (Θa ++ (α0 ~ b) ++ Θ0) ->
  {{ (subst_aenv τs α0 (Θa ++ Θ0))
    ⊢ (subst_ptyp_in_ptyp τs α0 A) ≡ᵗ (subst_ptyp_in_ptyp τs α0 A') }}a.
Proof.

  intros Θ A A' H; induction H; intros τs α0 b Θa Θ0 Heq Hs Hu; subst.
  -
    apply a_tyequiv__refl. apply subst_ptyp_in_ptyp_lc_ptyp;
      [ exact H | eapply solves_flex_lc; eassumption ].
  -  apply a_tyequiv__sym; eauto.
  -  eapply a_tyequiv__trans; eauto.
  -
    simpl. destruct_if as [Heqα | Hne].
    +
      subst α.
      assert (Hb : abind_flex_mono_def τ = b)
        by (eapply binds_mid_eq; eassumption).
      destruct Hs as [Hm [Hw [Hfrτ [Heqb | Heqb]]]];
        [ rewrite Heqb in Hb; discriminate | ].
      rewrite Heqb in Hb. inversion Hb; subst τ.
      rewrite subst_ptyp_in_ptyp_fresh_eq by exact Hfrτ.
      apply a_tyequiv__refl. apply mono_ptyp_lc; exact Hm.
    + apply a_tyequiv__flex_def with (α := α).
      eapply binds_def_subst_strip_mid; eassumption.
  -  simpl. apply a_tyequiv__arrow; eauto.
  -
    simpl. apply a_tyequiv__all
      with (L := L `union` singleton α0 `union` dom Θa `union` dom Θ0).
    intros β Hβ.
    repeat rewrite subst_ptyp_in_ptyp_open_ptyp_wrt_ptyp_var;
      try solve [ clear - Hβ; fsetdec | eapply solves_flex_lc; eassumption ].
    apply (H0 β ltac:(clear - Hβ; solve_notin_auto) τs α0 b Θa Θ0);
      [ reflexivity | exact Hs | exact Hu ].
Qed.

Ltac push_uniq Hu Hβ :=
  simpl_env; apply uniq_push;
    [ exact Hu | repeat rewrite dom_app; simpl; clear - Hβ; fsetdec ].

Lemma ad_refine_syn_subst_mid : forall Θ Δ Qs Qt,
  {{ Θ ⨟ Δ ⊢ᵣ Qs ⊳ Qt }}ad ->
  forall τs α0 (b : abind) Θa Θ0,
  Θ = Θa ++ (α0 ~ b) ++ Θ0 ->
  solves_flex τs α0 b Θ0 ->
  uniq (Θa ++ (α0 ~ b) ++ Θ0) ->
  α0 `notin` Δ ->
  Δ ∩ ftvar_in_ptyp τs [=] empty ->
  {{ (subst_aenv τs α0 (Θa ++ Θ0)) ⨟ Δ
    ⊢ᵣ (subst_bskl_in_bskl (ptyp_to_bskl_syn τs) α0 Qs)
      ⊳ (subst_bskl_in_bskl (ptyp_to_bskl_syn τs) α0 Qt) }}ad.
Proof.
  intros Θ Δ Qs Qt H; induction H;
    intros τs α0 b Θa Θ0 Heq Hs Hu Hα0 Hd; subst; simpl.
  -  apply ad_refine_syn__unit.
  -
    destruct_if as [Heqα | Hne].
    + subst α. apply ad_refine_syn_mono_refl.
      eapply solves_flex_mono; eassumption.
    + apply ad_refine_syn__var.
  -  apply ad_refine_syn_arrow_intro; eauto.
  -
    apply ad_refine_syn_all_intro
      with (L := L `union` singleton α0 `union` ftvar_in_ptyp τs
                 `union` dom Θa `union` dom Θ0). intros β Hβ.
    repeat rewrite (solves_flex_open_subst_bskl Hs) by (clear - Hβ; fsetdec).
    apply (H1 β ltac:(clear - Hβ; solve_notin_auto) τs α0 b
             ((β ~ abind_tvar) ++ Θa) Θ0);
      [ reflexivity | exact Hs | push_uniq Hu Hβ | clear - Hα0 Hβ; fsetdec
      | clear - Hd Hβ; fsetdec ].
  -
    unfold ptyp_to_bskl_syn at 1. rewrite <- pskl_to_bskl_syn_subst.
    apply ad_refine_syn__ghost.
    pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P (ptyp_to_pskl τs) α0)
      as Hup.
    rewrite ftvar_ptyp_to_pskl in Hup. clear - H Hd Hup; fsetdec.
  -  apply ad_refine_syn_univ_ghost_remove_intro; eauto.
  -
    apply ad_refine_syn_univ_ghost_fill_intro
      with (L := L `union` singleton α0 `union` dom Θa `union` dom Θ0).
    intros β Hβ.
    rewrite (solves_flex_open_subst_bskl Hs) by (clear - Hβ; fsetdec).
    apply (H1 β ltac:(clear - Hβ; solve_notin_auto) τs α0 b ((β ~ abind_tvar) ++ Θa) Θ0);
      [ reflexivity | exact Hs | push_uniq Hu Hβ | exact Hα0 | exact Hd ].
  -
    apply ad_refine_syn_univ_ghost_keep_intro; eauto.
  -
    destruct_if as [Heqα | Hne].
    +
      subst α.
      assert (Hττ : τ = τs) by (eapply solves_flex_def_eq; eassumption).
      subst τ.
      match goal with
      | IH : forall _ _ _ _ _, _ = _ -> _ |- _ =>
          pose proof (IH τs α0 b Θa Θ0 eq_refl Hs Hu Hα0 Hd) as IHx
      end.
      rewrite (subst_bskl_in_bskl_fresh_eq (ptyp_to_bskl_syn τs)) in IHx;
        [ exact IHx | ].
      rewrite ftvar_ptyp_to_bskl_syn. eapply solves_flex_fresh; eassumption.
    + apply ad_refine_syn__flex_l
        with (α := α) (τ := subst_ptyp_in_ptyp τs α0 τ).
      * eapply binds_def_subst_strip_mid; eassumption.
      * rewrite ptyp_to_bskl_syn_subst. eauto.
  -
    destruct_if as [Heqα | Hne].
    + subst α.
      assert (Hττ : τ = τs) by (eapply solves_flex_def_eq; eassumption).
      subst τ.
      match goal with
      | IH : forall _ _ _ _ _, _ = _ -> _ |- _ =>
          pose proof (IH τs α0 b Θa Θ0 eq_refl Hs Hu Hα0 Hd) as IHx
      end.
      rewrite (subst_bskl_in_bskl_fresh_eq (ptyp_to_bskl_syn τs)) in IHx;
        [ exact IHx | ].
      rewrite ftvar_ptyp_to_bskl_syn. eapply solves_flex_fresh; eassumption.
    + apply ad_refine_syn__flex_r
        with (α := α) (τ := subst_ptyp_in_ptyp τs α0 τ).
      * eapply binds_def_subst_strip_mid; eassumption.
      * rewrite ptyp_to_bskl_syn_subst. eauto.
Qed.

Lemma ad_refine_pskl_subst_mid : forall Θ Δ P Q,
  {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ Q }}ad ->
  forall τs α0 (b : abind) Θa Θ0,
  Θ = Θa ++ (α0 ~ b) ++ Θ0 ->
  solves_flex τs α0 b Θ0 ->
  uniq (Θa ++ (α0 ~ b) ++ Θ0) ->
  α0 `notin` Δ ->
  Δ ∩ ftvar_in_ptyp τs [=] empty ->
  {{ (subst_aenv τs α0 (Θa ++ Θ0)) ⨟ Δ
    ⊢ᵣₚ (subst_pskl_in_pskl (ptyp_to_pskl τs) α0 P)
      ⊳ (subst_pskl_in_pskl (ptyp_to_pskl τs) α0 Q) }}ad.
Proof.
  intros Θ Δ P Q H; induction H;
    intros τs α0 b Θa Θ0 Heq Hs Hu Hα0 Hd; subst; simpl.
  -  apply ad_refine_pskl__unit.
  -
    destruct_if as [Heqα | Hne].
    + subst α. apply ad_refine_pskl_refl.
      apply a_wf_pskl_mono_ptyp;
        [ eapply solves_flex_mono; eassumption
        | apply a_wf_ptyp_subst_tail; eapply solves_flex_wf; eassumption ].
    + apply ad_refine_pskl__var.
  -  apply ad_refine_pskl__arrow; eauto.
  -
    apply ad_refine_pskl__all
      with (L := L `union` singleton α0 `union` ftvar_in_ptyp τs
                 `union` dom Θa `union` dom Θ0). intros β Hβ.
    repeat rewrite (solves_flex_open_subst_pskl Hs) by (clear - Hβ; fsetdec).
    apply (H0 β ltac:(clear - Hβ; solve_notin_auto) τs α0 b
             ((β ~ abind_tvar) ++ Θa) Θ0);
      [ reflexivity | exact Hs | push_uniq Hu Hβ | clear - Hα0 Hβ; fsetdec
      | clear - Hd Hβ; fsetdec ].
  -
    apply ad_refine_pskl__ghost.
    pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P' (ptyp_to_pskl τs) α0)
      as Hup.
    rewrite ftvar_ptyp_to_pskl in Hup. clear - H Hd Hup; fsetdec.
  -  apply ad_refine_pskl__univ_ghost_remove; eauto.
  -
    apply ad_refine_pskl__univ_ghost_fill
      with (L := L `union` singleton α0 `union` dom Θa `union` dom Θ0).
    intros β Hβ.
    rewrite (solves_flex_open_subst_pskl Hs) by (clear - Hβ; fsetdec).
    apply (H0 β ltac:(clear - Hβ; solve_notin_auto) τs α0 b ((β ~ abind_tvar) ++ Θa) Θ0);
      [ reflexivity | exact Hs | push_uniq Hu Hβ | exact Hα0 | exact Hd ].
  -
    apply ad_refine_pskl__univ_ghost_keep; eauto.
  -
    destruct_if as [Heqα | Hne].
    +
      subst α.
      assert (Hττ : τ = τs) by (eapply solves_flex_def_eq; eassumption).
      subst τ.
      match goal with
      | IH : forall _ _ _ _ _, _ = _ -> _ |- _ =>
          pose proof (IH τs α0 b Θa Θ0 eq_refl Hs Hu Hα0 Hd) as IHx
      end.
      rewrite (subst_pskl_in_pskl_fresh_eq (ptyp_to_pskl τs)) in IHx;
        [ exact IHx | ].
      rewrite ftvar_ptyp_to_pskl. eapply solves_flex_fresh; eassumption.
    + apply ad_refine_pskl__flex_l
        with (α := α) (τ := subst_ptyp_in_ptyp τs α0 τ).
      * eapply binds_def_subst_strip_mid; eassumption.
      * rewrite ptyp_to_pskl_subst. eauto.
  -
    destruct_if as [Heqα | Hne].
    + subst α.
      assert (Hττ : τ = τs) by (eapply solves_flex_def_eq; eassumption).
      subst τ.
      match goal with
      | IH : forall _ _ _ _ _, _ = _ -> _ |- _ =>
          pose proof (IH τs α0 b Θa Θ0 eq_refl Hs Hu Hα0 Hd) as IHx
      end.
      rewrite (subst_pskl_in_pskl_fresh_eq (ptyp_to_pskl τs)) in IHx;
        [ exact IHx | ].
      rewrite ftvar_ptyp_to_pskl. eapply solves_flex_fresh; eassumption.
    + apply ad_refine_pskl__flex_r
        with (α := α) (τ := subst_ptyp_in_ptyp τs α0 τ).
      * eapply binds_def_subst_strip_mid; eassumption.
      * rewrite ptyp_to_pskl_subst. eauto.
Qed.

Lemma ad_pat_consis_mono_refl_vis : forall Ψ Θ τ,
  Ψ [=] empty ->
  mono_ptyp τ ->
  a_wf_ptyp Θ τ ->
  {{ Ψ ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn τ) ∼ (ptyp_to_bskl_syn τ) }}ad.
Proof.
  intros Ψ Θ τ HΨ Hm Hw.
  eapply ad_pat_consis_psi_cong;
    [ apply consis_mono_refl;
      [ exact Hm | intros β Hβ; eapply a_wf_ptyp_ftv_tvarish; eassumption ]
    | clear - HΨ; fsetdec ].
Qed.

Lemma ad_pat_consis_subst_mid : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  forall τs α0 (b : abind) Θa Θ0,
  Θ = Θa ++ (α0 ~ b) ++ Θ0 ->
  solves_flex τs α0 b Θ0 ->
  uniq (Θa ++ (α0 ~ b) ++ Θ0) ->
  {{ Ψ ⨟ (subst_aenv τs α0 (Θa ++ Θ0))
    ⊢ˢ (subst_uskl_in_uskl (ptyp_to_uskl_syn τs) α0 R)
      ∼ (subst_bskl_in_bskl (ptyp_to_bskl_syn τs) α0 Q) }}ad.
Proof.
  intros Ψ Θ R Q H; induction H;
    intros τs α0 b Θa Θ0 Heq Hs Hu; subst; simpl.
  -  apply ad_pat_consis__unit; assumption.
  -
    destruct_if as [Heqα | Hne].
    + subst α. apply ad_pat_consis_mono_refl_vis;
        [ assumption | eapply solves_flex_mono; eassumption
        | apply a_wf_ptyp_subst_tail; eapply solves_flex_wf; eassumption ].
    + apply ad_pat_consis__var;
        [ assumption | eapply a_binds_tvar_subst_mid; eassumption ].
  -
    eapply ad_pat_consis__arrow; eauto.
  -
    eapply ad_pat_consis__forall_inh_tagged
      with (L := L `union` singleton α0 `union` dom Θa `union` dom Θ0);
      [ | eassumption ].
    intros β Hβ.
    rewrite (solves_flex_open_subst_uskl Hs) by (clear - Hβ; fsetdec).
    rewrite (solves_flex_open_subst_bskl Hs) by (clear - Hβ; fsetdec).
    apply (H0 β ltac:(clear - Hβ; solve_notin_auto) τs α0 b ((β ~ abind_tvar) ++ Θa) Θ0);
      [ reflexivity | exact Hs | push_uniq Hu Hβ ].
  -
    eapply ad_pat_consis__forall_inh_untagged
      with (L := L `union` singleton α0 `union` dom Θa `union` dom Θ0).
    intros β Hβ.
    rewrite (solves_flex_open_subst_uskl Hs) by (clear - Hβ; fsetdec).
    rewrite (solves_flex_open_subst_bskl Hs) by (clear - Hβ; fsetdec).
    apply (H0 β ltac:(clear - Hβ; solve_notin_auto) τs α0 b ((β ~ abind_tvar) ++ Θa) Θ0);
      [ reflexivity | exact Hs | push_uniq Hu Hβ ].
  -
    eapply ad_pat_consis__forall_syn_tagged
      with (L := L `union` singleton α0 `union` dom Θa `union` dom Θ0).
    intros β Hβ.
    rewrite (solves_flex_open_subst_uskl Hs) by (clear - Hβ; fsetdec).
    rewrite (solves_flex_open_subst_bskl Hs) by (clear - Hβ; fsetdec).
    apply (H0 β ltac:(clear - Hβ; solve_notin_auto) τs α0 b ((β ~ abind_tvar) ++ Θa) Θ0);
      [ reflexivity | exact Hs | push_uniq Hu Hβ ].
  -
    eapply ad_pat_consis__forall_syn
      with (L := L `union` singleton α0 `union` dom Θa `union` dom Θ0).
    intros β Hβ.
    rewrite (solves_flex_open_subst_uskl Hs) by (clear - Hβ; fsetdec).
    rewrite (solves_flex_open_subst_bskl Hs) by (clear - Hβ; fsetdec).
    apply (H0 β ltac:(clear - Hβ; solve_notin_auto) τs α0 b ((β ~ abind_tvar) ++ Θa) Θ0);
      [ reflexivity | exact Hs | push_uniq Hu Hβ ].
  -  apply ad_pat_consis__ghostg; assumption.
  -  apply ad_pat_consis__dot_univ_ghost; eauto.
  -
    assert (Hm : mono_ptyp τs) by (eapply solves_flex_mono; eassumption).
    rewrite (pskl_to_bskl_inh_subst_mono P α0 Hm).
    apply ad_pat_consis__ghost; assumption.
  -  apply ad_pat_consis__univ_ghost; eauto.
  -
    eapply ad_pat_consis__univ_ghost_inh
      with (L := L `union` singleton α0 `union` dom Θa `union` dom Θ0).
    intros β Hβ.
    rewrite (solves_flex_open_subst_bskl Hs) by (clear - Hβ; fsetdec).
    apply (H0 β ltac:(clear - Hβ; solve_notin_auto) τs α0 b ((β ~ abind_tvar) ++ Θa) Θ0);
      [ reflexivity | exact Hs | push_uniq Hu Hβ ].
  -  apply ad_pat_consis__univ_ghost_drop; eauto.
  -
    destruct_if as [Heqα | Hne].
    +
      subst α.
      assert (Hττ : τ = τs) by (eapply solves_flex_def_eq; eassumption).
      subst τ.
      match goal with
      | IH : forall _ _ _ _ _, _ = _ -> _ |- _ =>
          pose proof (IH τs α0 b Θa Θ0 eq_refl Hs Hu) as IHx
      end.
      rewrite (subst_uskl_in_uskl_fresh_eq (ptyp_to_uskl_syn τs)) in IHx;
        [ exact IHx | ].
      rewrite ftvar_ptyp_to_uskl_syn. eapply solves_flex_fresh; eassumption.
    + apply ad_pat_consis__flex_l with (τ := subst_ptyp_in_ptyp τs α0 τ).
      * eapply binds_def_subst_strip_mid; eassumption.
      * rewrite ptyp_to_uskl_syn_subst. eauto.
  -
    destruct_if as [Heqα | Hne].
    + subst α.
      assert (Hττ : τ = τs) by (eapply solves_flex_def_eq; eassumption).
      subst τ.
      match goal with
      | IH : forall _ _ _ _ _, _ = _ -> _ |- _ =>
          pose proof (IH τs α0 b Θa Θ0 eq_refl Hs Hu) as IHx
      end.
      rewrite (subst_bskl_in_bskl_fresh_eq (ptyp_to_bskl_syn τs)) in IHx;
        [ exact IHx | ].
      rewrite ftvar_ptyp_to_bskl_syn. eapply solves_flex_fresh; eassumption.
    + apply ad_pat_consis__flex_r with (τ := subst_ptyp_in_ptyp τs α0 τ).
      * eapply binds_def_subst_strip_mid; eassumption.
      * rewrite ptyp_to_bskl_syn_subst. eauto.
Qed.

Lemma subst_aenv_fresh_eq : forall τ α Θ,
  α `notin` ftvar_in_aenv Θ -> subst_aenv τ α Θ = Θ.
Proof.
  intros τ α Θ; induction Θ as [ | [x bd] Θ' IH ]; intros Hfr;
    [ reflexivity | ].
  simpl in Hfr |- *. rewrite IH by (clear - Hfr; fsetdec).
  f_equal. f_equal. destruct bd; simpl; try reflexivity.
  - rewrite subst_ptyp_in_ptyp_fresh_eq; [ reflexivity | clear - Hfr; fsetdec ].
  - rewrite subst_pskl_in_pskl_fresh_eq; [ reflexivity | clear - Hfr; fsetdec ].
  - rewrite subst_ptyp_in_ptyp_fresh_eq; [ reflexivity | clear - Hfr; fsetdec ].
Qed.

Lemma solves_flex_of_wf_head : forall α b Θ,
  a_suffix_binding b ->
  {{ ⊢ ((α ~ b) ++ Θ) }}a ->
  exists τ, solves_flex τ α b Θ.
Proof.
  intros α b Θ Hb Hwf; inversion Hb; subst.
  - exists ptyp_unit. repeat split;
      [ apply mono_ptyp__unit | apply a_wf_ptyp__unit | simpl; fsetdec
      | left; reflexivity ].
  - inversion Hwf as [ | | ? τ0 ? Hfrα Hwfτ Hm Hwf' | | | ]; subst.
    exists A. repeat split; [ exact Hm | exact Hwfτ | | right; reflexivity ].
    intro Hin. pose proof (a_wf_ptyp_ftv_tvarish Hwfτ Hin) as Ht.
    destruct Ht as [Hbb | [Hbb | [τ1 Hbb]]]; apply binds_In in Hbb;
      clear - Hbb Hfrα; fsetdec.
Qed.

Lemma ad_refine_syn_strip_suffix : forall Ξ Θ Δ Qs Qt,
  a_suffix Ξ ->
  {{ ⊢ (Ξ ++ Θ) }}a ->
  (forall α, α `in` dom Ξ ->
     α `notin` (ftvar_in_bskl Qs `union` ftvar_in_bskl Qt `union` Δ)) ->
  {{ (Ξ ++ Θ) ⨟ Δ ⊢ᵣ Qs ⊳ Qt }}ad ->
  {{ Θ ⨟ Δ ⊢ᵣ Qs ⊳ Qt }}ad.
Proof.
  induction Ξ as [ | [β b] Ξ' IH ]; intros * Hsuf Hwf Hfv H; [ exact H | ].
  inversion Hsuf as [ | ? ? ? Hsuf' Hbind ]; subst.
  assert (Hβ : β `notin` (ftvar_in_bskl Qs `union` ftvar_in_bskl Qt `union` Δ))
    by (apply Hfv; simpl; fsetdec).
  simpl_env in Hwf.
  assert (Hwf' : {{ ⊢ (Ξ' ++ Θ) }}a)
    by (inversion Hwf; subst; assumption).
  assert (Hβd : β `notin` dom (Ξ' ++ Θ))
    by (inversion Hwf; subst; assumption).
  assert (Hd : ftvar_in_aenv (Ξ' ++ Θ) [<=] dom (Ξ' ++ Θ))
    by (apply a_wf_aenv_ftv_dom; exact Hwf').
  assert (Hx : {{ (Ξ' ++ Θ) ⨟ Δ ⊢ᵣ Qs ⊳ Qt }}ad).
  { eapply ad_refine_syn_defs_avoid with (S := singleton β);
      [ exact H | | clear - Hβ; fsetdec | clear - Hβ; fsetdec ].
    intros γ τ Hb Hγ. simpl_env in Hb.
    apply binds_app_1 in Hb as [Hb | Hb];
      [ apply binds_one_iff in Hb as [He _]; subst γ;
        clear - Hγ; exfalso; fsetdec | ].
    split; [ exact Hb | ].
    pose proof (ftvar_in_aenv_binds_def _ _ _ Hb) as Hτ.
    clear - Hτ Hd Hβd; fsetdec. }
  apply IH; auto.
  intros α Hα. apply Hfv. simpl. clear - Hα; fsetdec.
Qed.

Lemma ad_consis_join_subst_mid : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ᵣ Q }}ad ->
  forall τs α0 (b : abind) Θa Θ0,
  Θ = Θa ++ (α0 ~ b) ++ Θ0 ->
  solves_flex τs α0 b Θ0 ->
  uniq (Θa ++ (α0 ~ b) ++ Θ0) ->
  {{ Ψ ⨟ (subst_aenv τs α0 (Θa ++ Θ0))
    ⊢ˢ (subst_uskl_in_uskl (ptyp_to_uskl_syn τs) α0 R)
      ∼ᵣ (subst_bskl_in_bskl (ptyp_to_bskl_syn τs) α0 Q) }}ad.
Proof.
  intros Ψ Θ R Q [Hc Hr] τs α0 b Θa Θ0 Heq Hs Hu. split.
  - eapply ad_pat_consis_subst_mid;
      [ exact Hc | exact Heq | exact Hs | exact Hu ].
  - rewrite uskl_to_pskl_subst_mono, bskl_to_pskl_subst_mono.
    eapply ad_refine_pskl_subst_mid;
      [ exact Hr | exact Heq | exact Hs | exact Hu | clear; fsetdec
      | clear; fsetdec ].
Qed.

Lemma ad_pat_sub_subst_mid : forall NM M Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ[ NM | M ] R ⩽ Q }}ad ->
  forall τs α0 (b : abind) Θa Θ0,
  Θ = Θa ++ (α0 ~ b) ++ Θ0 ->
  solves_flex τs α0 b Θ0 ->
  uniq (Θa ++ (α0 ~ b) ++ Θ0) ->
  {{ Ψ ⨟ (subst_aenv τs α0 (Θa ++ Θ0))
    ⊢ˢ[ NM | M ] (subst_uskl_in_uskl (ptyp_to_uskl_syn τs) α0 R)
                ⩽ (subst_bskl_in_bskl (ptyp_to_bskl_syn τs) α0 Q) }}ad.
Proof.
  intros NM M Ψ Θ R Q H; induction H;
    intros τs α0 b Θa Θ0 Heq Hs Hu; subst; simpl;
    (assert (Hm : mono_ptyp τs) by (eapply solves_flex_mono; eassumption)).
  -
    apply ad_pat_sub__infer;
      [ assumption
      | eapply ad_consis_join_subst_mid; [ eassumption | reflexivity | .. ];
        eassumption
      | apply is_sskl_subst_mono; assumption ].
  -
    rewrite pskl_to_bskl_inh_subst_mono; [ | assumption ].
    apply ad_pat_sub__check;
      [ apply guarded_uskl_subst_mono; assumption
      | apply guarded_pskl_subst;
          [ assumption | apply mono_ptyp_to_pskl_guarded; assumption
          | apply ptyp_to_pskl_lc; apply mono_ptyp_lc; assumption ]
      | rewrite <- pskl_to_bskl_inh_subst_mono; [ | assumption ];
        eapply ad_consis_join_subst_mid; [ eassumption | reflexivity | .. ];
        eassumption ].
  -
    apply ad_pat_sub__forall_r
      with (L := L `union` singleton α0 `union` dom Θa `union` dom Θ0).
    intros β Hβ.
    rewrite (solves_flex_open_subst_bskl Hs) by (clear - Hβ; fsetdec).
    apply (H0 β ltac:(clear - Hβ; solve_notin_auto) τs α0 b ((β ~ abind_tvar) ++ Θa) Θ0);
      [ reflexivity | exact Hs | push_uniq Hu Hβ ].
  -
    apply ad_pat_sub__univ_ghost_r;
      [ assumption
      | apply guarded_uskl_subst_mono; assumption
      | apply guarded_bskl_subst_mono; assumption
      | apply is_sskl_subst_mono; assumption
      | eapply ad_consis_join_subst_mid; [ eassumption | reflexivity | .. ];
        eassumption ].
  -
    eapply ad_pat_sub__arrow;
      [ eapply ad_consis_join_subst_mid; [ eassumption | reflexivity | .. ];
        eassumption
      | eauto | assumption ].
  -
    match goal with
    | IH : forall _ _ _ _ _, _ = _ -> _ |- _ =>
        pose proof (IH τs α0 b Θa Θ0 eq_refl Hs Hu) as IHx
    end.
    rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl in IHx;
      [ | apply mono_ptyp_to_uskl_syn_lc; assumption ].
    eapply ad_pat_sub__forall_l_tagged;
      [ assumption | eassumption
      |
        assert (Hsu : ftag_in_uskl (subst_uskl_in_uskl (ptyp_to_uskl_syn τs) α0 R)
                      [=] ftag_in_uskl R)
          by (apply ftag_in_uskl_subst_tagfree; apply ftag_ptyp_to_uskl_syn);
        simpl in H1 |- *; rewrite Hsu; exact H1
      | apply a_tags_sort_subst_mono; eassumption
      | rewrite uskl_to_pskl_subst_mono;
        eapply a_wf_pskl_subst_mid;
          [ eassumption | reflexivity | exact Hs | clear; fsetdec | clear; fsetdec ]
      | exact IHx ].
  -
    match goal with
    | IH : forall _ _ _ _ _, _ = _ -> _ |- _ =>
        pose proof (IH τs α0 b Θa Θ0 eq_refl Hs Hu) as IHx
    end.
    rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl in IHx;
      [ | apply mono_ptyp_to_uskl_syn_lc; assumption ].
    eapply ad_pat_sub__forall_l_untagged;
      [ assumption | eassumption
      |
        assert (Hsu : ftag_in_uskl (subst_uskl_in_uskl (ptyp_to_uskl_syn τs) α0 R)
                      [=] ftag_in_uskl R)
          by (apply ftag_in_uskl_subst_tagfree; apply ftag_ptyp_to_uskl_syn);
        simpl in H1 |- *; rewrite Hsu; exact H1
      | apply a_tags_sort_subst_mono; eassumption
      | rewrite uskl_to_pskl_subst_mono;
        eapply a_wf_pskl_subst_mid;
          [ eassumption | reflexivity | exact Hs | clear; fsetdec | clear; fsetdec ]
      | exact IHx ].
  -
    rewrite pskl_to_bskl_inh_subst_mono; [ | assumption ].
    apply ad_pat_sub__ghost;
      [ assumption
      | rewrite <- pskl_to_bskl_inh_subst_mono; [ | assumption ];
        apply mod_comp_sk_subst_mono; assumption ].
  -
    apply ad_pat_sub__ghostg; [ assumption | ].
    change bskl_ghost
      with (subst_bskl_in_bskl (ptyp_to_bskl_syn τs) α0 bskl_ghost).
    apply mod_comp_sk_subst_mono; assumption.
  -  apply ad_pat_sub__univ_ghost_l; [ assumption | eauto ].
  -  apply ad_pat_sub__univ_ghost_lg; [ assumption | eauto ].
  -
    destruct_if as [Heqα | Hne].
    + subst α.
      assert (Hττ : τ = τs) by (eapply solves_flex_def_eq; eassumption).
      subst τ.
      match goal with
      | IH : forall _ _ _ _ _, _ = _ -> _ |- _ =>
          pose proof (IH τs α0 b Θa Θ0 eq_refl Hs Hu) as IHx
      end.
      rewrite (subst_uskl_in_uskl_fresh_eq (ptyp_to_uskl_syn τs)) in IHx;
        [ exact IHx | ].
      rewrite ftvar_ptyp_to_uskl_syn. eapply solves_flex_fresh; eassumption.
    + apply ad_pat_sub__flex_mono with (τ := subst_ptyp_in_ptyp τs α0 τ).
      * eapply binds_def_subst_strip_mid; eassumption.
      * rewrite ptyp_to_uskl_syn_subst. eauto.
Qed.

Lemma abind_to_pskl_subst : forall τs α0 b P,
  abind_to_pskl b = Some P ->
  abind_to_pskl (subst_abind τs α0 b)
  = Some (subst_pskl_in_pskl (ptyp_to_pskl τs) α0 P).
Proof.
  intros τs α0 b P H; destruct b; simpl in H |- *; try discriminate;
    inversion H; subst;
    [ f_equal; apply ptyp_to_pskl_subst | reflexivity ].
Qed.

Lemma binds_tm_neq_flex : forall x b Θa α0 b0 Θ0 P,
  binds x b (Θa ++ (α0 ~ b0) ++ Θ0) ->
  abind_to_pskl b = Some P ->
  uniq (Θa ++ (α0 ~ b0) ++ Θ0) ->
  a_suffix_binding b0 ->
  x <> α0.
Proof.
  intros x b Θa α0 b0 Θ0 P Hb Hsome Hu Hsuf Heq; subst x.
  assert (Hbb : b = b0) by (eapply binds_mid_eq; eassumption).
  subst b. inversion Hsuf; subst; simpl in Hsome; discriminate.
Qed.

Lemma solves_flex_binding : forall τs α0 b Θ0,
  solves_flex τs α0 b Θ0 -> a_suffix_binding b.
Proof.
  intros τs α0 b Θ0 [_ [_ [_ [Heq | Heq]]]]; subst;
    [ apply a_suffix_binding__flex_mono
    | apply a_suffix_binding__flex_mono_def ].
Qed.

Lemma subst_pskl_to_bskl_syn_eq : forall τ α P,
  subst_bskl_in_bskl (ptyp_to_bskl_syn τ) α (pskl_to_bskl_syn P)
  = pskl_to_bskl_syn (subst_pskl_in_pskl (ptyp_to_pskl τ) α P).
Proof. intros. rewrite pskl_to_bskl_syn_subst. reflexivity. Qed.

Lemma subst_btyp_to_bskl_eq : forall τ α B,
  subst_bskl_in_bskl (ptyp_to_bskl_syn τ) α (btyp_to_bskl B)
  = btyp_to_bskl (subst_btyp_in_btyp (ptyp_to_btyp_syn τ) α B).
Proof.
  intros. rewrite btyp_to_bskl_subst, btyp_to_bskl_ptyp_to_btyp_syn.
  reflexivity.
Qed.

Lemma ad_pat_subst_mid : forall M Θ e Q,
  {{ Θ ⊢ˢ[ M ] e ⦂ Q }}ad ->
  forall τs α0 (b0 : abind) Θa Θ0,
  Θ = Θa ++ (α0 ~ b0) ++ Θ0 ->
  solves_flex τs α0 b0 Θ0 ->
  uniq (Θa ++ (α0 ~ b0) ++ Θ0) ->
  {{ (subst_aenv τs α0 (Θa ++ Θ0))
    ⊢ˢ[ M ] (subst_ptyp_in_exp τs α0 e)
         ⦂ (subst_bskl_in_bskl (ptyp_to_bskl_syn τs) α0 Q) }}ad.
Proof.
  intros M Θ e Q H; induction H;
    intros τs α0 b0 Θa Θ0 Heq Hs Hu; subst; simpl;
    (assert (Hm : mono_ptyp τs) by (eapply solves_flex_mono; eassumption));
    (assert (Hlcτ : lc_ptyp τs) by (apply mono_ptyp_lc; exact Hm)).
  -
    apply ad_pat__unit.
    + rewrite bskl_to_pskl_subst_mono.
      eapply a_wf_pskl_subst_mid;
        [ exact H | reflexivity | exact Hs | clear; fsetdec | clear; fsetdec ].
    + pose proof (@ad_pat_sub_subst_mid _ _ _ _ _ _ H0 τs α0 b0 Θa Θ0
                    eq_refl Hs Hu) as Hx.
      simpl in Hx. exact Hx.
  -
    assert (Hne : x <> α0)
      by (eapply binds_tm_neq_flex;
          [ eassumption | eassumption | eassumption
          | eapply solves_flex_binding; eassumption ]).
    eapply ad_pat__var;
      [ eapply binds_subst_strip_mid; eassumption
      | apply abind_to_pskl_subst; eassumption
      | rewrite bskl_to_pskl_subst_mono;
        eapply a_wf_pskl_subst_mid;
          [ exact H1 | reflexivity | exact Hs | clear; fsetdec | clear; fsetdec ]
      | ].
    pose proof (@ad_pat_sub_subst_mid _ _ _ _ _ _ H2 τs α0 b0 Θa Θ0
                  eq_refl Hs Hu) as Hx.
    rewrite !pskl_to_uskl_via_bskl_syn in Hx |- *.
    rewrite pskl_to_uskl_subst. exact Hx.
  -
    eapply ad_pat__anno;
      [ rewrite bskl_to_pskl_subst_mono;
        eapply a_wf_pskl_subst_mid;
          [ exact H | reflexivity | exact Hs | clear; fsetdec | clear; fsetdec ]
      | ].
    pose proof (@ad_pat_sub_subst_mid _ _ _ _ _ _ H0 τs α0 b0 Θa Θ0
                  eq_refl Hs Hu) as Hx.
    rewrite !pskl_to_uskl_via_bskl_syn in Hx |- *.
    rewrite ptyp_to_pskl_subst, pskl_to_uskl_subst. exact Hx.
  -
    rewrite subst_pskl_to_bskl_syn_eq.
    apply ad_pat__freeze.
    pose proof (IHad_pat τs α0 b0 Θa Θ0 eq_refl Hs Hu) as IHx.
    rewrite subst_pskl_to_bskl_syn_eq in IHx. exact IHx.
  -
    rewrite (pskl_to_bskl_inh_subst_mono P α0 Hm).
    apply ad_pat__abs
      with (L := L `union` singleton α0 `union` dom Θa `union` dom Θ0);
      [ assumption
      | eapply a_wf_pskl_subst_mid;
          [ eassumption | reflexivity | exact Hs | clear; fsetdec | clear; fsetdec ]
      | rewrite <- (pskl_to_bskl_inh_subst_mono P α0 Hm);
        change (bskl_arrow (subst_bskl_in_bskl (ptyp_to_bskl_syn τs) α0
                              (pskl_to_bskl_inh P))
                           (subst_bskl_in_bskl (ptyp_to_bskl_syn τs) α0 Q))
          with (subst_bskl_in_bskl (ptyp_to_bskl_syn τs) α0
                  (bskl_arrow (pskl_to_bskl_inh P) Q));
        apply mod_comp_sk_subst_mono; assumption
      | ].
    intros x Hx.
    rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var.
    apply (H3 x ltac:(clear - Hx; solve_notin_auto) τs α0 b0
             ((x ~ abind_var_skl P) ++ Θa) Θ0);
      [ reflexivity | exact Hs | push_uniq Hu Hx ].
  -
    rewrite subst_btyp_to_bskl_eq.
    apply ad_pat__abs_anno
      with (L := L `union` singleton α0 `union` dom Θa `union` dom Θ0)
           (B := subst_btyp_in_btyp (ptyp_to_btyp_syn τs) α0 B);
      [ assumption
      | eapply a_wf_ptyp_subst_mid;
          [ eassumption | reflexivity | exact Hs ]
      |
        rewrite btyp_to_ptyp_subst, btyp_to_ptyp_ptyp_to_btyp_syn;
        reflexivity
      | rewrite <- subst_btyp_to_bskl_eq;
        change (bskl_arrow (subst_bskl_in_bskl (ptyp_to_bskl_syn τs) α0
                              (btyp_to_bskl B))
                           (subst_bskl_in_bskl (ptyp_to_bskl_syn τs) α0 Q))
          with (subst_bskl_in_bskl (ptyp_to_bskl_syn τs) α0
                  (bskl_arrow (btyp_to_bskl B) Q));
        apply mod_comp_sk_subst_mono; assumption
      | ].
    intros x Hx.
    rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var.
    match goal with
    | IH : forall y, y `notin` _ -> forall _ _ _ _ _, _ = _ -> _ |- _ =>
        apply (IH x ltac:(clear - Hx; solve_notin_auto) τs α0 b0
                 ((x ~ abind_var_typ (btyp_to_ptyp B)) ++ Θa) Θ0)
    end;
      [ reflexivity | exact Hs | push_uniq Hu Hx ].
  -
    eapply ad_pat__app with (P := subst_pskl_in_pskl (ptyp_to_pskl τs) α0 P).
    + pose proof (IHad_pat1 τs α0 b0 Θa Θ0 eq_refl Hs Hu) as IHx.
      rewrite subst_pskl_to_bskl_syn_eq in IHx. exact IHx.
    + rewrite <- (pskl_to_bskl_inh_subst_mono P α0 Hm).
      eapply ad_refine_syn_subst_mid;
        [ eassumption | reflexivity | exact Hs | exact Hu | clear; fsetdec
        | clear; fsetdec ].
    + pose proof (IHad_pat2 τs α0 b0 Θa Θ0 eq_refl Hs Hu) as IHy.
      simpl in IHy. exact IHy.
  -
    rewrite subst_pskl_to_bskl_syn_eq.
    apply ad_pat__abs_check
      with (L := L `union` singleton α0 `union` dom Θa `union` dom Θ0)
           (P := subst_pskl_in_pskl (ptyp_to_pskl τs) α0 P).
    intros x Hx.
    rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var.
    rewrite <- subst_pskl_to_bskl_syn_eq.
    apply (H0 x ltac:(clear - Hx; solve_notin_auto) τs α0 b0
             ((x ~ abind_var_skl pskl_ghost) ++ Θa) Θ0);
      [ reflexivity | exact Hs | push_uniq Hu Hx ].
  -
    rewrite subst_pskl_to_bskl_syn_eq, subst_btyp_to_bskl_eq,
      <- ptyp_to_btyp_syn_subst.
    apply ad_pat__abs_anno_check
      with (L := L `union` singleton α0 `union` dom Θa `union` dom Θ0)
           (P := subst_pskl_in_pskl (ptyp_to_pskl τs) α0 P);
      [ eapply a_wf_ptyp_subst_mid;
          [ eassumption | reflexivity | exact Hs ]
      | ].
    intros x Hx.
    rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var.
    rewrite <- subst_pskl_to_bskl_syn_eq.
    apply (H1 x ltac:(clear - Hx; solve_notin_auto) τs α0 b0
             ((x ~ abind_var_typ A) ++ Θa) Θ0);
      [ reflexivity | exact Hs | push_uniq Hu Hx ].
Qed.

Lemma subst_btyp_to_ptyp_eq : forall τ α B,
  subst_ptyp_in_ptyp τ α (btyp_to_ptyp B)
  = btyp_to_ptyp (subst_btyp_in_btyp (ptyp_to_btyp_syn τ) α B).
Proof.
  intros. rewrite btyp_to_ptyp_subst, btyp_to_ptyp_ptyp_to_btyp_syn.
  reflexivity.
Qed.

Lemma ad_sd_typing_subst_mid : forall M Θ e B,
  {{ Θ ⊢ˢᵈ[ M ] e ⦂ B }}ad ->
  forall τs α0 (b0 : abind) Θa Θ0,
  Θ = Θa ++ (α0 ~ b0) ++ Θ0 ->
  solves_flex τs α0 b0 Θ0 ->
  uniq (Θa ++ (α0 ~ b0) ++ Θ0) ->
  {{ (subst_aenv τs α0 (Θa ++ Θ0))
    ⊢ˢᵈ[ M ] (subst_ptyp_in_exp τs α0 e)
          ⦂ (subst_btyp_in_btyp (ptyp_to_btyp_syn τs) α0 B) }}ad.
Proof.
  intros M Θ e B H; induction H;
    intros τs α0 b0 Θa Θ0 Heq Hs Hu; subst; simpl;
    (assert (Hm : mono_ptyp τs) by (eapply solves_flex_mono; eassumption));
    (assert (Hlcτ : lc_ptyp τs) by (apply mono_ptyp_lc; exact Hm)).
  -
    apply ad_sd_typing__unit.
    pose proof (@ad_pat_sub_subst_mid _ _ _ _ _ _ H τs α0 b0 Θa Θ0
                  eq_refl Hs Hu) as Hx.
    simpl in Hx. rewrite subst_btyp_to_bskl_eq in Hx. exact Hx.
  -
    assert (Hne : x <> α0)
      by (eapply binds_tm_neq_flex with (P := ptyp_to_pskl A);
          [ eassumption | reflexivity | eassumption
          | eapply solves_flex_binding; eassumption ]).
    apply ad_sd_typing__var with (A := subst_ptyp_in_ptyp τs α0 A);
      [ change (abind_var_typ (subst_ptyp_in_ptyp τs α0 A))
          with (subst_abind τs α0 (abind_var_typ A));
        eapply binds_subst_strip_mid; eassumption | ].
    pose proof (@ad_pat_sub_subst_mid _ _ _ _ _ _ H0 τs α0 b0 Θa Θ0
                  eq_refl Hs Hu) as Hx.
    rewrite subst_btyp_to_bskl_eq, <- ptyp_to_uskl_syn_subst in Hx.
    exact Hx.
  -
    eapply ad_sd_typing__anno.
    + eapply a_wf_ptyp_subst_mid; [ exact H | reflexivity | exact Hs ].
    + pose proof (IHad_sd_typing τs α0 b0 Θa Θ0 eq_refl Hs Hu) as IHx.
      rewrite <- ptyp_to_btyp_inh_subst_mono in IHx; [ | assumption ].
      exact IHx.
    + pose proof (@ad_pat_sub_subst_mid _ _ _ _ _ _ H1 τs α0 b0 Θa Θ0
                    eq_refl Hs Hu) as Hx.
      rewrite subst_btyp_to_bskl_eq, <- ptyp_to_uskl_syn_subst in Hx.
      exact Hx.
  -
    rewrite <- ptyp_to_btyp_inh_subst_mono; [ | assumption ].
    eapply ad_sd_typing__freeze.
    + pose proof (IHad_sd_typing τs α0 b0 Θa Θ0 eq_refl Hs Hu) as IHx.
      rewrite <- ptyp_to_btyp_syn_subst in IHx. exact IHx.
    + eapply a_tyequiv_subst_mid;
        [ eassumption | reflexivity | exact Hs | exact Hu ].
  -
    apply ad_sd_typing__abs_check_step
      with (L := L `union` singleton α0 `union` dom Θa `union` dom Θ0).
    intros β Hβ.
    rewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var;
      [ | clear - Hβ; fsetdec
        | apply is_styp_lc; apply mono_ptyp_to_btyp_syn_is_styp; assumption ].
    apply (H0 β ltac:(clear - Hβ; solve_notin_auto) τs α0 b0
             ((β ~ abind_tvar) ++ Θa) Θ0);
      [ reflexivity | exact Hs | push_uniq Hu Hβ ].
  -
    rewrite <- ptyp_to_btyp_inh_subst_mono; [ | assumption ].
    apply ad_sd_typing__abs_check_base
      with (L := L `union` singleton α0 `union` dom Θa `union` dom Θ0);
      [ eapply a_wf_ptyp_subst_mid; [ eassumption | reflexivity | exact Hs ]
      | apply is_ityp_subst_mono; assumption
      | ].
    intros x Hx.
    rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var.
    apply (H2 x ltac:(clear - Hx; solve_notin_auto) τs α0 b0
             ((x ~ abind_var_typ A) ++ Θa) Θ0);
      [ reflexivity | exact Hs | push_uniq Hu Hx ].
  -
    apply ad_sd_typing__abs_anno_check_step
      with (L := L `union` singleton α0 `union` dom Θa `union` dom Θ0).
    intros β Hβ.
    rewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var;
      [ | clear - Hβ; fsetdec
        | apply is_styp_lc; apply mono_ptyp_to_btyp_syn_is_styp; assumption ].
    apply (H0 β ltac:(clear - Hβ; solve_notin_auto) τs α0 b0
             ((β ~ abind_tvar) ++ Θa) Θ0);
      [ reflexivity | exact Hs | push_uniq Hu Hβ ].
  -
    rewrite <- ptyp_to_btyp_inh_subst_mono; [ | assumption ].
    apply ad_sd_typing__abs_anno_check_base
      with (L := L `union` singleton α0 `union` dom Θa `union` dom Θ0)
           (A' := subst_ptyp_in_ptyp τs α0 A');
      [ eapply a_wf_ptyp_subst_mid; [ eassumption | reflexivity | exact Hs ]
      | eapply a_tyequiv_subst_mid;
          [ eassumption | reflexivity | exact Hs | exact Hu ]
      | apply is_ityp_subst_mono; assumption
      | ].
    intros x Hx.
    rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var.
    apply (H3 x ltac:(clear - Hx; solve_notin_auto) τs α0 b0
             ((x ~ abind_var_typ A) ++ Θa) Θ0);
      [ reflexivity | exact Hs | push_uniq Hu Hx ].
  -
    rewrite <- ptyp_to_btyp_inh_subst_mono; [ | assumption ].
    apply ad_sd_typing__abs
      with (L := L `union` singleton α0 `union` dom Θa `union` dom Θ0);
      [ assumption
      | eapply a_wf_ptyp_subst_mid; [ eassumption | reflexivity | exact Hs ]
      | rewrite ptyp_to_btyp_inh_subst_mono; [ | assumption ];
        change (btyp_arrow (subst_btyp_in_btyp (ptyp_to_btyp_syn τs) α0
                              (ptyp_to_btyp_inh A))
                           (subst_btyp_in_btyp (ptyp_to_btyp_syn τs) α0 B))
          with (subst_btyp_in_btyp (ptyp_to_btyp_syn τs) α0
                  (btyp_arrow (ptyp_to_btyp_inh A) B));
        apply mod_comp_ty_subst_mono; assumption
      | ].
    intros x Hx.
    rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var.
    apply (H3 x ltac:(clear - Hx; solve_notin_auto) τs α0 b0
             ((x ~ abind_var_typ A) ++ Θa) Θ0);
      [ reflexivity | exact Hs | push_uniq Hu Hx ].
  -
    eapply ad_sd_typing__abs_anno
      with (L := L `union` singleton α0 `union` dom Θa `union` dom Θ0)
           (A' := subst_ptyp_in_ptyp τs α0 (btyp_to_ptyp B1));
      [ assumption
      | eapply a_wf_ptyp_subst_mid; [ eassumption | reflexivity | exact Hs ]
      | eapply a_tyequiv_subst_mid;
          [ eassumption | reflexivity | exact Hs | exact Hu ]
      | rewrite btyp_to_ptyp_subst, btyp_to_ptyp_ptyp_to_btyp_syn;
        reflexivity
      | change (btyp_arrow (subst_btyp_in_btyp (ptyp_to_btyp_syn τs) α0 B1)
                           (subst_btyp_in_btyp (ptyp_to_btyp_syn τs) α0 B2))
          with (subst_btyp_in_btyp (ptyp_to_btyp_syn τs) α0
                  (btyp_arrow B1 B2));
        apply mod_comp_ty_subst_mono; assumption
      | ].
    intros x Hx.
    rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var.
    match goal with
    | IH : forall y, y `notin` _ -> forall _ _ _ _ _, _ = _ -> _ |- _ =>
        apply (IH x ltac:(clear - Hx; solve_notin_auto) τs α0 b0
                 ((x ~ abind_var_typ A) ++ Θa) Θ0)
    end;
      [ reflexivity | exact Hs | push_uniq Hu Hx ].
  -
    eapply ad_sd_typing__app
      with (P := subst_pskl_in_pskl (ptyp_to_pskl τs) α0 P)
           (A2 := subst_ptyp_in_ptyp τs α0 A2)
           (B1 := subst_btyp_in_btyp (ptyp_to_btyp_syn τs) α0 B1).
    + pose proof (@ad_pat_subst_mid _ _ _ _ H τs α0 b0 Θa Θ0
                    eq_refl Hs Hu) as Hx.
      rewrite subst_pskl_to_bskl_syn_eq in Hx. exact Hx.
    + rewrite <- (pskl_to_bskl_inh_subst_mono P α0 Hm).
      rewrite <- subst_btyp_to_bskl_eq.
      eapply ad_refine_syn_subst_mid;
        [ eassumption | reflexivity | exact Hs | exact Hu | clear; fsetdec
        | clear; fsetdec ].
    + pose proof (IHad_sd_typing1 τs α0 b0 Θa Θ0 eq_refl Hs Hu) as IHx.
      simpl in IHx. exact IHx.
    +
      rewrite <- subst_btyp_to_ptyp_eq.
      eapply a_tyequiv_subst_mid;
        [ eassumption | reflexivity | exact Hs | exact Hu ].
    + pose proof (IHad_sd_typing2 τs α0 b0 Θa Θ0 eq_refl Hs Hu) as IHy.
      rewrite <- ptyp_to_btyp_inh_subst_mono in IHy; [ | assumption ].
      exact IHy.
Qed.

Lemma ad_sd_typing_strip_suffix : forall Ξ Θ M e B,
  a_suffix Ξ ->
  {{ ⊢ (Ξ ++ Θ) }}a ->
  (forall α, α `in` dom Ξ ->
     α `notin` (ftvar_in_btyp B `union` ftvar_in_exp e)) ->
  {{ (Ξ ++ Θ) ⊢ˢᵈ[ M ] e ⦂ B }}ad ->
  {{ Θ ⊢ˢᵈ[ M ] e ⦂ B }}ad.
Proof.
  induction Ξ as [ | [β b] Ξ' IH ]; intros * Hsuf Hwf Hfv H; [ exact H | ].
  inversion Hsuf as [ | ? ? ? Hsuf' Hbind ]; subst.
  assert (Hβ : β `notin` (ftvar_in_btyp B `union` ftvar_in_exp e))
    by (apply Hfv; simpl; fsetdec).
  simpl_env in Hwf.
  destruct (solves_flex_of_wf_head Hbind Hwf) as [τs Hs].
  assert (Hwf' : {{ ⊢ (Ξ' ++ Θ) }}a) by (inversion Hwf; subst; assumption).
  pose proof (@ad_sd_typing_subst_mid _ _ _ _ H τs β b nil (Ξ' ++ Θ)
                ltac:(simpl_env; reflexivity) Hs
                ltac:(simpl_env; apply a_wf_aenv_uniq; exact Hwf)) as Hx.
  simpl_env in Hx.
  assert (Hβd : β `notin` dom (Ξ' ++ Θ))
    by (inversion Hwf; subst; assumption).
  assert (Hd : ftvar_in_aenv (Ξ' ++ Θ) [<=] dom (Ξ' ++ Θ))
    by (apply a_wf_aenv_ftv_dom; exact Hwf').
  rewrite subst_aenv_fresh_eq in Hx by (clear - Hβd Hd; fsetdec).
  rewrite subst_ptyp_in_exp_fresh_eq in Hx by (clear - Hβ; fsetdec).
  rewrite subst_btyp_in_btyp_fresh_eq in Hx by (clear - Hβ; fsetdec).
  apply IH; auto.
  intros α Hα. apply Hfv. simpl. clear - Hα; fsetdec.
Qed.
