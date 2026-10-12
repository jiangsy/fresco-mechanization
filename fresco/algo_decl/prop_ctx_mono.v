Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.algo_decl.def_subtyping.
Require Import src.fresco.algo_decl.def_typing.

Set Implicit Arguments.

Definition aenv_binds_le (Θ Θ' : aenv) : Prop :=
  forall x b, binds x b Θ -> binds x b Θ'.

Lemma aenv_binds_le_cons : forall Θ Θ' x (b : abind),
  aenv_binds_le Θ Θ' -> aenv_binds_le ((x ~ b) ++ Θ) ((x ~ b) ++ Θ').
Proof.
  intros Θ Θ' x b Hle y c Hy.
  apply binds_app_1 in Hy as [Hy | Hy]; [ apply binds_app_2 | ]; auto.
Qed.

Lemma aenv_binds_le_weaken_l : forall Ξ Θ, aenv_binds_le Θ (Ξ ++ Θ).
Proof. intros Ξ Θ x b H; auto. Qed.

Lemma aenv_binds_le_perm3 : forall (Θa Θb Θc : aenv),
  aenv_binds_le (Θa ++ Θb ++ Θc) (Θb ++ Θa ++ Θc).
Proof.
  intros Θa Θb Θc x b H.
  apply binds_app_1 in H as [H | H].
  - apply binds_app_3; apply binds_app_2; exact H.
  - apply binds_app_1 in H as [H | H].
    + apply binds_app_2; exact H.
    + apply binds_app_3; apply binds_app_3; exact H.
Qed.

Definition abind_is_ty (b : abind) : Prop :=
  match b with
  | abind_tvar | abind_flex_mono | abind_flex_mono_def _ => True
  | abind_var_typ _ | abind_var_skl _ => False
  end.

Definition aenv_tbinds_le (Θ Θ' : aenv) : Prop :=
  forall α b, abind_is_ty b -> binds α b Θ -> binds α b Θ'.

Lemma aenv_tbinds_le_of_binds_le : forall Θ Θ',
  aenv_binds_le Θ Θ' -> aenv_tbinds_le Θ Θ'.
Proof. intros Θ Θ' Hle α b _ H; auto. Qed.

Lemma aenv_tbinds_le_cons : forall Θ Θ' x (b : abind),
  aenv_tbinds_le Θ Θ' -> aenv_tbinds_le ((x ~ b) ++ Θ) ((x ~ b) ++ Θ').
Proof.
  intros Θ Θ' x b Hle y c Hc Hy.
  apply binds_app_1 in Hy as [Hy | Hy]; [ apply binds_app_2 | ]; auto.
Qed.

Lemma aenv_tbinds_le_strip_tm : forall Θ1 x (b : abind) Θ2,
  ~ abind_is_ty b ->
  aenv_tbinds_le (Θ1 ++ (x ~ b) ++ Θ2) (Θ1 ++ Θ2).
Proof.
  intros Θ1 x b Θ2 Htm y c Hc Hy.
  apply binds_app_1 in Hy as [Hy | Hy]; [ apply binds_app_2; exact Hy | ].
  apply binds_app_1 in Hy as [Hy | Hy]; [ | apply binds_app_3; exact Hy ].
  apply binds_one_1 in Hy as Heq. destruct Hy as [Hpair | []].
  inversion Hpair; subst. contradiction.
Qed.

Lemma aenv_tbinds_le_flex_def : forall Θ Θ' α τ,
  aenv_tbinds_le Θ Θ' ->
  binds α (abind_flex_mono_def τ) Θ ->
  binds α (abind_flex_mono_def τ) Θ'.
Proof. intros Θ Θ' α τ Hle H; apply Hle; [ exact I | exact H ]. Qed.

Lemma a_binds_tvar_mono : forall Θ Θ' α,
  aenv_tbinds_le Θ Θ' -> a_binds_tvar α Θ -> a_binds_tvar α Θ'.
Proof.
  intros Θ Θ' α Hle [H | [H | [τ H]]];
    [ left | right; left | right; right; exists τ ];
    apply Hle; solve [ exact I | exact H ].
Qed.

Lemma a_wf_ptyp_mono : forall Θ A,
  a_wf_ptyp Θ A ->
  forall Θ', aenv_tbinds_le Θ Θ' -> a_wf_ptyp Θ' A.
Proof.
  intros Θ A H; induction H; intros Θ' Hle;
    eauto 4 using a_wf_ptyp, a_binds_tvar_mono, aenv_tbinds_le_cons.
Qed.

Lemma a_wf_pskl_mono : forall Θ Δ P,
  a_wf_pskl Θ Δ P ->
  forall Θ', aenv_tbinds_le Θ Θ' -> a_wf_pskl Θ' Δ P.
Proof.
  intros Θ Δ P H Θ' Hle. apply (a_wf_pskl_tvar_mono H).
  intros α. apply a_binds_tvar_mono. exact Hle.
Qed.

Lemma a_tyequiv_ctx_mono : forall Θ A B,
  {{ Θ ⊢ A ≡ᵗ B }}a ->
  forall Θ', aenv_tbinds_le Θ Θ' -> {{ Θ' ⊢ A ≡ᵗ B }}a.
Proof.
  intros * Heq Θ' Hle. eapply a_tyequiv_transport; [ | exact Heq ].
  intros; apply a_tyequiv__flex_def; eapply aenv_tbinds_le_flex_def; eauto.
Qed.

Lemma a_binds_tvar_mono_cons_tvar : forall α Θ Θ',
  (forall β, a_binds_tvar β Θ -> a_binds_tvar β Θ') ->
  forall β, a_binds_tvar β ((α ~ abind_tvar) ++ Θ) ->
    a_binds_tvar β ((α ~ abind_tvar) ++ Θ').
Proof.
  intros * Hm β Hb. apply a_binds_tvar_cons_tvar.
  destruct (a_binds_tvar_cons_tvar_inv Hb); auto.
Qed.

Lemma flex_defs_cons_tvar : forall α (Θ Θ' : aenv),
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     binds β (abind_flex_mono_def τ) Θ') ->
  forall β τ, binds β (abind_flex_mono_def τ) ((α ~ abind_tvar) ++ Θ) ->
    binds β (abind_flex_mono_def τ) ((α ~ abind_tvar) ++ Θ').
Proof.
  intros * Hm β τ Hb.
  destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
    [ discriminate | ].
  unfold binds; right; apply Hm; exact Hb'.
Qed.

Lemma ad_pat_consis_transport : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  forall Θ', (forall α, a_binds_tvar α Θ -> a_binds_tvar α Θ') ->
  (forall α τ, binds α (abind_flex_mono_def τ) Θ ->
     binds α (abind_flex_mono_def τ) Θ') ->
  {{ Ψ ⨟ Θ' ⊢ˢ R ∼ Q }}ad.
Proof.
  intros * H; induction H; intros Θ' Htv Hdef;
    eauto 6 using ad_pat_consis, a_binds_tvar_mono_cons_tvar, flex_defs_cons_tvar.
Qed.

Lemma ad_pat_consis_mono : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  forall Θ', aenv_tbinds_le Θ Θ' -> {{ Ψ ⨟ Θ' ⊢ˢ R ∼ Q }}ad.
Proof.
  intros * H Θ' Hle. eapply ad_pat_consis_transport; [ exact H | | ];
    intros; eauto using a_binds_tvar_mono, aenv_tbinds_le_flex_def.
Qed.

Lemma ad_refine_syn_defs_mono : forall Θ Δ Q Q',
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad ->
  forall Θ', (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
                binds β (abind_flex_mono_def τ) Θ') ->
  {{ Θ' ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad.
Proof.
  intros * H; induction H; intros Θ' Hm;
    eauto 6 using ad_refine_syn, flex_defs_cons_tvar.
Qed.

Lemma ad_refine_pskl_defs_mono : forall Θ Δ P P',
  {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ P' }}ad ->
  forall Θ', (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
                binds β (abind_flex_mono_def τ) Θ') ->
  {{ Θ' ⨟ Δ ⊢ᵣₚ P ⊳ P' }}ad.
Proof.
  intros * H; induction H; intros Θ' Hm;
    eauto 6 using ad_refine_pskl, flex_defs_cons_tvar.
Qed.

Lemma ad_refine_syn_mono : forall Θ Δ Q Q',
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad ->
  forall Θ', aenv_tbinds_le Θ Θ' -> {{ Θ' ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad.
Proof.
  intros * H Θ' Hle. eapply ad_refine_syn_defs_mono;
    [ exact H | intros; eapply aenv_tbinds_le_flex_def; eauto ].
Qed.

Lemma ad_refine_pskl_mono : forall Θ Δ P P',
  {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ P' }}ad ->
  forall Θ', aenv_tbinds_le Θ Θ' -> {{ Θ' ⨟ Δ ⊢ᵣₚ P ⊳ P' }}ad.
Proof.
  intros * H Θ' Hle. eapply ad_refine_pskl_defs_mono;
    [ exact H | intros; eapply aenv_tbinds_le_flex_def; eauto ].
Qed.

Lemma ad_consis_join_mono : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ᵣ Q }}ad ->
  forall Θ', aenv_tbinds_le Θ Θ' -> {{ Ψ ⨟ Θ' ⊢ˢ R ∼ᵣ Q }}ad.
Proof.
  intros Ψ Θ R Q [Hc Hr] Θ' Hle. split;
    eauto 3 using ad_pat_consis_mono, ad_refine_pskl_mono.
Qed.

Lemma ad_pat_sub_mono : forall NM M Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ[ NM | M ] R ⩽ Q }}ad ->
  forall Θ', aenv_tbinds_le Θ Θ' -> {{ Ψ ⨟ Θ' ⊢ˢ[ NM | M ] R ⩽ Q }}ad.
Proof.
  intros NM M Ψ Θ R Q H; induction H; intros Θ' Hle;
    eauto 4 using ad_pat_sub, ad_consis_join_mono, a_wf_pskl_mono,
      aenv_tbinds_le_cons, aenv_tbinds_le_flex_def.
Qed.

Lemma ad_pat_mono : forall M Θ e Q,
  {{ Θ ⊢ˢ[ M ] e ⦂ Q }}ad ->
  forall Θ', aenv_binds_le Θ Θ' -> {{ Θ' ⊢ˢ[ M ] e ⦂ Q }}ad.
Proof.
  intros M Θ e Q H; induction H; intros Θ' Hle;
    pose proof (aenv_tbinds_le_of_binds_le Hle) as Htle;
    pose proof Hle as Hbinds; unfold aenv_binds_le in Hbinds;
    eauto 5 using ad_pat, aenv_binds_le_cons, a_wf_pskl_mono,
      a_wf_ptyp_mono, ad_pat_sub_mono, ad_refine_syn_mono.
Qed.

Lemma ad_sd_typing_mono : forall M Θ e B,
  {{ Θ ⊢ˢᵈ[ M ] e ⦂ B }}ad ->
  forall Θ', aenv_binds_le Θ Θ' -> {{ Θ' ⊢ˢᵈ[ M ] e ⦂ B }}ad.
Proof.
  intros M Θ e B H; induction H; intros Θ' Hle;
    pose proof (aenv_tbinds_le_of_binds_le Hle) as Htle;
    pose proof Hle as Hbinds; unfold aenv_binds_le in Hbinds;
    eauto 6 using ad_sd_typing, aenv_binds_le_cons, a_wf_ptyp_mono,
      ad_pat_sub_mono, a_tyequiv_ctx_mono, ad_pat_mono, ad_refine_syn_mono.
  eapply ad_sd_typing__app;
    eauto 3 using ad_pat_mono, ad_refine_syn_mono, a_tyequiv_ctx_mono.
Qed.

Corollary ad_sd_typing_suffix_moving : forall M Θ1 Θ2 Ξ e B,
  {{ (Ξ ++ Θ2 ++ Θ1) ⊢ˢᵈ[ M ] e ⦂ B }}ad ->
  {{ (Θ2 ++ Ξ ++ Θ1) ⊢ˢᵈ[ M ] e ⦂ B }}ad.
Proof.
  intros M Θ1 Θ2 Ξ e B H.
  eapply ad_sd_typing_mono; [ exact H | apply aenv_binds_le_perm3 ].
Qed.

Corollary ad_pat_suffix_moving : forall M Θ1 Θ2 Ξ e Q,
  {{ (Ξ ++ Θ2 ++ Θ1) ⊢ˢ[ M ] e ⦂ Q }}ad ->
  {{ (Θ2 ++ Ξ ++ Θ1) ⊢ˢ[ M ] e ⦂ Q }}ad.
Proof.
  intros M Θ1 Θ2 Ξ e Q H.
  eapply ad_pat_mono; [ exact H | apply aenv_binds_le_perm3 ].
Qed.

Corollary ad_refine_syn_strip_tm_typ : forall Ξ x A Θ Δ Q Q',
  {{ (Ξ ++ (x ~ abind_var_typ A) ++ Θ) ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad ->
  {{ (Ξ ++ Θ) ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad.
Proof.
  intros * H. eapply ad_refine_syn_mono;
    [ exact H | apply aenv_tbinds_le_strip_tm; intros [] ].
Qed.

Corollary ad_refine_syn_strip_tm_skl : forall Ξ x P0 Θ Δ Q Q',
  {{ (Ξ ++ (x ~ abind_var_skl P0) ++ Θ) ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad ->
  {{ (Ξ ++ Θ) ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad.
Proof.
  intros * H. eapply ad_refine_syn_mono;
    [ exact H | apply aenv_tbinds_le_strip_tm; intros [] ].
Qed.

Lemma ad_pat_sub_fuel_le : forall n NM M Ψ Θ R Q,
  ad_pat_sub_fuel n NM M Ψ Θ R Q ->
  forall m, n <= m -> ad_pat_sub_fuel m NM M Ψ Θ R Q.
Proof.
  intros n NM M Ψ Θ R Q H; induction H; intros m Hle;
    try solve [eauto 3 using ad_pat_sub_fuel].
  all: destruct m as [|m']; [ lia | ];
    eauto 4 using ad_pat_sub_fuel, le_S_n.
Qed.

Lemma ad_pat_sub_of_fuel : forall n NM M Ψ Θ R Q,
  ad_pat_sub_fuel n NM M Ψ Θ R Q ->
  {{ Ψ ⨟ Θ ⊢ˢ[ NM | M ] R ⩽ Q }}ad.
Proof.
  intros n NM M Ψ Θ R Q H; induction H; eauto 3 using ad_pat_sub.
Qed.

Lemma ad_pat_consis_weaken : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  forall Θ',
  (forall x b, binds x b Θ -> binds x b Θ') ->
  {{ Ψ ⨟ Θ' ⊢ˢ R ∼ Q }}ad.
Proof.
  intros * H Θ' Hmon.
  eapply ad_pat_consis_mono; [ exact H | ].
  apply aenv_tbinds_le_of_binds_le. exact Hmon.
Qed.

Lemma ad_pat_consis_weaken_cons : forall Ψ Θ (e : list (atom * abind)) R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  {{ Ψ ⨟ (e ++ Θ) ⊢ˢ R ∼ Q }}ad.
Proof.
  intros. eapply ad_pat_consis_weaken; eauto;
    try (intros x b Hb; unfold binds; apply in_or_app; auto).
Qed.

Lemma ad_partial_precise_psi_cong : forall Θ Δ Ψ P ψ,
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  forall Ψc, Ψ [=] Ψc ->
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψc ] ψ }}ad.
Proof.
  intros Θ Δ Ψ P ψ H; induction H; intros Ψc Heq;
    econstructor; eauto; fsetdec.
Qed.

Lemma ad_partial_precise_weaken : forall Θ Δ Ψ P ψ,
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  forall Θ',
  (forall x b, binds x b Θ -> binds x b Θ') ->
  {{ Θ' ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad.
Proof.
  intros Θ Δ Ψ P ψ H; induction H; intros Θ' Hmon.
  - apply ad_ppre__unit; auto.
  - apply ad_ppre__var; auto.
  - eapply ad_ppre__arrow; eauto.
  - eapply ad_ppre__forall with (L := L); eauto.
    intros α Hα. apply H0; auto.
    intros x b Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? ?] | Hb']; subst;
      [ unfold binds; left; reflexivity
      | unfold binds; right; apply Hmon; auto ].
  - apply ad_ppre__ghost; auto.
  - apply ad_ppre__univ_ghost_remove; auto.
  - eapply ad_ppre__univ_ghost_fill with (L := L).
    intros α Hα. apply H0; auto.
    intros x b Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? ?] | Hb']; subst;
      [ unfold binds; left; reflexivity
      | unfold binds; right; apply Hmon; auto ].
  - apply ad_ppre__univ_ghost_keep; auto.
  - eapply ad_ppre__flex_l; eauto.
  - eapply ad_ppre__flex_r; eauto.
Qed.

Lemma ad_partial_precise_weaken_tvar : forall α Θ Δ Ψ P ψ,
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  {{ ((α ~ abind_tvar) ++ Θ) ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad.
Proof.
  intros α Θ Δ Ψ P ψ H. eapply ad_partial_precise_weaken; [ exact H | ].
  intros x b Hb. unfold binds; right; exact Hb.
Qed.
