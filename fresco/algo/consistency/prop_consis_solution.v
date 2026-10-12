Require Import src.fresco.prop_atom_sets.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.
Require Import src.fresco.notations.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_ln.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo_decl.prop_stability.
Require Import src.fresco.algo_decl.prop_refinement.
Require Import src.fresco.algo.basic.prop_metasubst_composition.
Require Import src.fresco.algo.basic.prop_context_normalization.
Require Import src.fresco.algo.basic.prop_metasubst.
Require Import src.fresco.algo_decl.prop_precision.
Require Import src.fresco.algo.consistency.prop_consis_monotype_equiv.
Require Import src.fresco.algo.consistency.prop_soundness_consis.
Require Import src.fresco.algo.basic.prop_inc_strengthen.
Require Import src.fresco.algo.consistency.prop_precision_recovery.
Require Import src.fresco.algo.consistency.prop_consis_rename.

Set Implicit Arguments.

Section Lex.
  Context {A B : Type} (RA : A -> A -> Prop) (RB : B -> B -> Prop).

  Definition lex (x y : A * B) : Prop :=
    RA (fst x) (fst y) \/ (fst x = fst y /\ RB (snd x) (snd y)).

  Lemma lex_wf : well_founded RA -> well_founded RB -> well_founded lex.
  Proof.
    intros wfA wfB [a b]. revert b.
    generalize (wfA a); intros Ha.
    induction Ha as [a Ha IHa]. intros b.
    generalize (wfB b); intros Hb.
    induction Hb as [b Hb IHb].
    constructor. intros [a' b'] Hlex.
    destruct Hlex as [Hlt | [Heq Hlt]]; simpl in *.
    - apply IHa. exact Hlt.
    - subst a'. apply IHb. exact Hlt.
  Qed.
End Lex.

Definition mu_ty : Type := nat * (nat * (nat * nat)).

Definition mu_lt : mu_ty -> mu_ty -> Prop :=
  lex lt (lex lt (lex lt lt)).

Lemma mu_lt_wf : well_founded mu_lt.
Proof.
  unfold mu_lt.
  apply lex_wf; [ exact lt_wf | ].
  apply lex_wf; [ exact lt_wf | ].
  apply lex_wf; exact lt_wf.
Qed.

Definition Vpskl (Θ : aenv) (κ : metasubst) (P : pskl) : nat :=
  size_pskl (⇓ˢ[Θ] (msubst_pskl κ P)).

Definition Vptyp (Θ : aenv) (κ : metasubst) (A : ptyp) : nat :=
  size_ptyp (⇓ᵗ[Θ] (msubst_ptyp κ A)).

Definition Vvar (Θ : aenv) (κ : metasubst) (α : atom) : nat :=
  size_ptyp (⇓ᵗ[Θ] (msubst_lookup κ α)).

Definition V_consis (Θ : aenv) (κ : metasubst) (P0 P : pskl) : nat :=
  Vpskl Θ κ P + Vpskl Θ κ P0.
Definition V_unify (Θ : aenv) (κ : metasubst) (α β : atom) : nat :=
  Vvar Θ κ α + Vvar Θ κ β.
Definition V_assign (Θ : aenv) (κ : metasubst) (α : atom) (P : pskl) : nat :=
  Vpskl Θ κ P + Vvar Θ κ α.

Lemma Vpskl_arrow : forall Θ κ P1 P2,
  Vpskl Θ κ (pskl_arrow P1 P2) = 1 + Vpskl Θ κ P1 + Vpskl Θ κ P2.
Proof. reflexivity. Qed.

Lemma Vpskl_all_syn : forall Θ κ P,
  Vpskl Θ κ (pskl_all_syn P) = 1 + Vpskl Θ κ P.
Proof. reflexivity. Qed.

Lemma Vpskl_univ_ghost : forall Θ κ P,
  Vpskl Θ κ (pskl_univ_ghost P) = 1 + Vpskl Θ κ P.
Proof. reflexivity. Qed.

Lemma Vpskl_pos : forall Θ κ P, 1 <= Vpskl Θ κ P.
Proof. intros. unfold Vpskl. apply size_pskl_min. Qed.

Lemma Vpskl_arrow_lt1 : forall Θ κ P1 P2,
  Vpskl Θ κ P1 < Vpskl Θ κ (pskl_arrow P1 P2).
Proof. intros. rewrite Vpskl_arrow. pose proof (Vpskl_pos Θ κ P2). lia. Qed.

Lemma Vpskl_arrow_lt2 : forall Θ κ P1 P2,
  Vpskl Θ κ P2 < Vpskl Θ κ (pskl_arrow P1 P2).
Proof. intros. rewrite Vpskl_arrow. pose proof (Vpskl_pos Θ κ P1). lia. Qed.

Lemma Vpskl_all_syn_lt : forall Θ κ P,
  Vpskl Θ κ P < Vpskl Θ κ (pskl_all_syn P).
Proof. intros. rewrite Vpskl_all_syn. lia. Qed.

Lemma Vpskl_univ_ghost_lt : forall Θ κ P,
  Vpskl Θ κ P < Vpskl Θ κ (pskl_univ_ghost P).
Proof. intros. rewrite Vpskl_univ_ghost. lia. Qed.

Lemma Vpskl_var : forall Θ κ α,
  Vpskl Θ κ (pskl_var_f α) = Vvar Θ κ α.
Proof.
  intros. unfold Vpskl, Vvar. cbn [msubst_pskl].
  rewrite msubst_pskl_embed_ptyp. apply size_pskl_ptyp_to_pskl.
Qed.

Lemma V_flexL : forall Θ κ α P0,
  V_consis Θ κ P0 (pskl_var_f α) = V_assign Θ κ α P0.
Proof. intros. unfold V_consis, V_assign. rewrite Vpskl_var. lia. Qed.

Lemma V_flexR : forall Θ κ α P,
  V_consis Θ κ (pskl_var_f α) P = V_assign Θ κ α P.
Proof. intros. unfold V_consis, V_assign. rewrite Vpskl_var. lia. Qed.

Lemma V_flex : forall Θ κ α β,
  V_consis Θ κ (pskl_var_f β) (pskl_var_f α) = V_unify Θ κ α β.
Proof. intros. unfold V_consis, V_unify. rewrite !Vpskl_var. lia. Qed.

Lemma Vpskl_inc_equiv : forall Θ0 κ1 κ2 Θ P,
  a_inc_equiv Θ0 κ1 κ2 Θ ->
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a -> a_scope_pskl Θ0 P ->
  Vpskl Θ κ1 P = Vpskl Θ κ2 P.
Proof.
  intros. unfold Vpskl. eapply a_inc_equiv_downarrow_pskl_size; eauto.
Qed.

Lemma Vpskl_backedge : forall Θ κ0 α1 τ τ' P,
  {{ ⊢ Θ }}a ->
  {{ Θ ⊢ τ' ≡ᵗ (msubst_ptyp κ0 τ) }}a ->
  Vpskl Θ κ0 (subst_pskl_in_pskl (ptyp_to_pskl τ) α1 P)
  = Vpskl Θ ((α1, τ') :: κ0) P.
Proof.
  intros. unfold Vpskl. eapply downarrow_subst_pskl_size; eauto.
Qed.

Lemma Vvar_backedge : forall Θ κ0 α1 τ τ' α,
  {{ ⊢ Θ }}a ->
  {{ Θ ⊢ τ' ≡ᵗ (msubst_ptyp κ0 τ) }}a ->
  Vptyp Θ κ0 (subst_ptyp_in_ptyp τ α1 (ptyp_var_f α))
  = Vptyp Θ ((α1, τ') :: κ0) (ptyp_var_f α).
Proof.
  intros. unfold Vptyp. eapply downarrow_subst_ptyp_size; eauto.
Qed.

Lemma msubst_pskl_ftv_keep : forall κ P α',
  α' `notin` dom κ ->
  α' `in` ftvar_in_pskl P ->
  α' `in` ftvar_in_pskl (msubst_pskl κ P).
Proof.
  intros κ P α' Hnd;
    induction P as [ | n | x | P1 IH1 P2 IH2 | Pb IHb | | Pt IHt ];
    simpl; intros Hin; try solve [ fsetdec ].

  assert (Heq : α' = x) by (clear - Hin; fsetdec). subst x.
  rewrite (msubst_lookup_notin κ Hnd). simpl. fsetdec.
Qed.

Lemma Vpskl_open : forall Θ κ P α,
  {{ ⊢ Θ }}a ->
  msubst_lc κ ->
  α `notin` dom κ ->
  α `notin` dom Θ ->
  Vpskl Θ κ (open_pskl_wrt_pskl P (pskl_var_f α)) = Vpskl Θ κ P.
Proof.
  intros Θ κ P α Hwf Hlcκ Hακ HαΘ. unfold Vpskl.
  assert (HαΘ' : α `notin` dom (aenv_msubst Θ))
    by (pose proof (dom_aenv_msubst Θ); clear - HαΘ H; fsetdec).
  rewrite msubst_pskl_open_lc by assumption.
  rewrite (msubst_pskl_open_lc (κ := aenv_msubst Θ));
    [ apply size_pskl_open_pskl_wrt_pskl_var
    | apply aenv_msubst_lc; exact Hwf
    | exact HαΘ' ].
Qed.

Lemma rigid_survives_solution : forall Θ1 κ Θ β P,
  κ ∷ Θ1 ⊑ Θ ->
  {{ ⊢ Θ1 }}a ->
  binds β abind_tvar Θ1 ->
  β `in` ftvar_in_pskl P ->
  β `in` ftvar_in_pskl (msubst_pskl κ P).
Proof.
  intros Θ1 κ Θ β P Hinc Hwf Hb Hin.
  apply msubst_pskl_ftv_keep; [ | exact Hin ].
  eapply a_inc_tvar_notin_dom; eauto.
Qed.

Lemma join_pskl_downarrow_mono_scoped : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  {{ ⊢ Θ }}a ->
  forall P0 A D,
    R = pskl_to_uskl P0 ->
    Q = ptyp_to_bskl_syn A -> mono_ptyp A ->
    (forall α τ, binds α (abind_flex_mono_def τ) Θ -> α `in` D -> ftvar_in_ptyp τ [<=] D) ->
    ftvar_in_ptyp A [<=] D ->
    ftvar_in_pskl (⇓ˢ[ Θ ] P0) [<=] D.
Proof.
  intros Ψ Θ R Q Hc Hwf; induction Hc;
    intros P0 C0 D HeqS HeqC HmC0 Hcl HCD;
    unfold ptyp_to_bskl_syn in *.
  -
    destruct P0; simpl in HeqS; try discriminate.
    simpl. clear; fsetdec.
  -
    destruct P0; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    destruct C0; simpl in HeqC; try discriminate.
    inversion HeqC; subst.
    simpl. rewrite ftvar_ptyp_to_pskl.
    match goal with
    | |- context[msubst_lookup ?r ?α] =>
        replace (msubst_lookup r α) with (⇓ᵗ[ Θ ] (ptyp_var_f α)) by reflexivity
    end.
    apply downarrow_ftv_closed;
      [ exact Hwf | simpl; clear - HCD; simpl in HCD; fsetdec | exact Hcl ].
  -
    destruct P0 as [ | n | α | S01 S02 | S0a | | S0b ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    destruct C0 as [ | | | C1 C2 | ]; simpl in HeqC; try discriminate.
    inversion HeqC; subst.
    inversion HmC0 as [ | | ? ? HmC1 HmC2 ]; subst.
    simpl. intros α2 Hα2.
    apply union_1 in Hα2. destruct Hα2 as [HZl | HZr].
    + apply (IHHc1 Hwf S01 C1 D eq_refl eq_refl HmC1 Hcl
               ltac:(clear - HCD; simpl in HCD; solve_notin_auto) α2 HZl).
    + apply (IHHc2 Hwf S02 C2 D eq_refl eq_refl HmC2 Hcl
               ltac:(clear - HCD; simpl in HCD; solve_notin_auto) α2 HZr).
  -  destruct HmC0; simpl in HeqC; discriminate.
  -  destruct HmC0; simpl in HeqC; discriminate.
  -  destruct HmC0; simpl in HeqC; discriminate.
  -  destruct HmC0; simpl in HeqC; discriminate.
  -  destruct HmC0; simpl in HeqC; discriminate.
  -  destruct HmC0; simpl in HeqC; discriminate.
  -
    destruct P0; simpl in HeqS; try discriminate.
    simpl. clear; fsetdec.
  -  destruct HmC0; simpl in HeqC; discriminate.
  -  destruct HmC0; simpl in HeqC; discriminate.
  -
    destruct P0 as [ | | | | | | S0t ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    simpl. apply (IHHc Hwf S0t C0 D eq_refl eq_refl HmC0 Hcl HCD).
  -
    destruct P0 as [ | | αv | | | | ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    simpl.
    assert (Hlk : msubst_lookup (aenv_msubst Θ) αv = ⇓ᵗ[ Θ ] τ)
      by (apply aenv_msubst_lookup_def; assumption).
    rewrite Hlk.
    rewrite <- msubst_pskl_embed_ptyp.
    apply (IHHc Hwf (ptyp_to_pskl τ) C0 D
             (eq_sym (pskl_to_uskl_ptyp τ)) eq_refl HmC0 Hcl HCD).
  -
    destruct C0; simpl in HeqC; try discriminate.
    inversion HeqC; subst.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    assert (Hτcl : ftvar_in_ptyp τ [<=] D).
    { eapply Hcl; [ exact H | ].
      clear - HCD; simpl in HCD; fsetdec. }
    apply (IHHc Hwf P0 τ D eq_refl eq_refl Hmτ Hcl Hτcl).
Qed.

Lemma a_wf_pskl_strengthen : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  forall Θ', uniq Θ ->
  (forall x b, binds x b Θ' -> binds x b Θ) ->
  (forall α, α `in` ftvar_in_pskl P -> α `in` dom Θ') ->
  {{ Θ' ⨟ Δ ⊢ₚₛ P }}a.
Proof.
  intros Θ Δ P H Θ' Hu Hsub Hsc.
  eapply a_wf_pskl_tvar_mono_ftv; [ exact H | ].
  intros α Hα Htv.
  pose proof (Hsc α Hα) as Hd.
  eapply a_binds_tvar_strengthen; eauto.
Qed.

Lemma a_wf_pskl_univ_ghost_body : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ (pskl_univ_ghost P) }}a ->
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a.
Proof.
  intros Θ Δ P H. inversion H; subst.
  match goal with Hb : {{ aenv_minus _ _ ⨟ _ ⊢ₚₛ P }}a |- _ => rename Hb into Hbody end.
  eapply a_wf_pskl_delta_mono.
  - eapply a_wf_pskl_tvar_mono; [ exact Hbody | ].
    intros γ Hγ. apply a_binds_tvar_aenv_minus in Hγ. exact (proj1 Hγ).
  - intros γ Hγ HγΔ. exfalso.
    pose proof (a_wf_pskl_ftv_binds Hbody Hγ) as Hb.
    apply a_binds_tvar_aenv_minus in Hb. exact (proj2 Hb HγΔ).
Qed.

Lemma a_wf_pskl_var_non_flex_tvar : forall Θ Δ β,
  {{ Θ ⨟ Δ ⊢ₚₛ (pskl_var_f β) }}a ->
  a_non_flex Θ (pskl_var_f β) ->
  binds β abind_tvar Θ.
Proof.
  intros Θ Δ β Hwf [_ Hnfl].
  inversion Hwf as [ | Θw Δw δw Hbt | | | | ]; subst.
  destruct Hbt as [Hb | [Hb | [τ0 Hb]]];
    [ exact Hb
    | exfalso; apply Hnfl; apply a_flex__var; exact Hb
    | exfalso; apply Hnfl; eapply a_flex__var_def; exact Hb ].
Qed.

Ltac str_forall H0 Hu Hwf' Hsub HscS HscQ Rr Qq α Hα openU openB :=
  apply H0;
  [ clear - Hα; fsetdec
  | simpl_env; apply uniq_push; [ exact Hu | clear - Hα; fsetdec ]
  | apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf' ]
  | apply binds_sub_cons with (e := (α ~ abind_tvar)); exact Hsub
  | intros β Hβ;
    pose proof (openU Rr (uskl_var_f α)) as HupU; simpl in HupU;
    destruct (β == α) as [-> | Hne]; [ simpl; clear; fsetdec | ];
    simpl; apply add_2; apply HscS; clear - Hβ HupU Hne; fsetdec
  | intros β Hβ;
    pose proof (openB Qq (bskl_var_f α)) as HupB; simpl in HupB;
    destruct (β == α) as [-> | Hne]; [ simpl; clear; fsetdec | ];
    simpl; apply add_2; apply HscQ; clear - Hβ HupB Hne; fsetdec ].

Lemma ad_pat_consis_strengthen : forall Ψ Θ R' Q,
  {{ Ψ ⨟ Θ ⊢ˢ R' ∼ Q }}ad ->
  forall Θ', uniq Θ -> {{ ⊢ Θ' }}a ->
  (forall x b, binds x b Θ' -> binds x b Θ) ->
  (forall α0, α0 `in` ftvar_in_uskl R' -> α0 `in` dom Θ') ->
  (forall α0, α0 `in` ftvar_in_bskl Q -> α0 `in` dom Θ') ->
  {{ Ψ ⨟ Θ' ⊢ˢ R' ∼ Q }}ad.
Proof.
  intros Ψ Θ R' Q H; induction H;
    intros Θ' Hu Hwf' Hsub HscS HscQ; simpl in *.
  - apply ad_pat_consis__unit; auto.
  - apply ad_pat_consis__var; [ assumption | ].
    eapply a_binds_tvar_strengthen;
      [ eassumption | exact Hu | exact Hsub | apply HscS; fsetdec ].
  - eapply ad_pat_consis__arrow; [ | | exact H1 ].
    + apply IHad_pat_consis1; auto; intros α0 Hα0;
        solve [ apply HscS; fsetdec | apply HscQ; fsetdec ].
    + apply IHad_pat_consis2; auto; intros α0 Hα0;
        solve [ apply HscS; fsetdec | apply HscQ; fsetdec ].
  - eapply ad_pat_consis__forall_inh_tagged
      with (L := L `union` dom Θ `union` dom Θ'); [ | exact H1 ].
    intros α0 Hα0.
    str_forall H0 Hu Hwf' Hsub HscS HscQ R Q α0 Hα0
      ftvar_in_uskl_open_uskl_wrt_uskl_upper ftvar_in_bskl_open_bskl_wrt_bskl_upper.
  - eapply ad_pat_consis__forall_inh_untagged
      with (L := L `union` dom Θ `union` dom Θ').
    intros α0 Hα0.
    str_forall H0 Hu Hwf' Hsub HscS HscQ R Q α0 Hα0
      ftvar_in_uskl_open_uskl_wrt_uskl_upper ftvar_in_bskl_open_bskl_wrt_bskl_upper.
  - eapply ad_pat_consis__forall_syn_tagged
      with (L := L `union` dom Θ `union` dom Θ').
    intros α0 Hα0.
    str_forall H0 Hu Hwf' Hsub HscS HscQ R Q α0 Hα0
      ftvar_in_uskl_open_uskl_wrt_uskl_upper ftvar_in_bskl_open_bskl_wrt_bskl_upper.
  - eapply ad_pat_consis__forall_syn
      with (L := L `union` dom Θ `union` dom Θ').
    intros α0 Hα0.
    str_forall H0 Hu Hwf' Hsub HscS HscQ R Q α0 Hα0
      ftvar_in_uskl_open_uskl_wrt_uskl_upper ftvar_in_bskl_open_bskl_wrt_bskl_upper.
  - apply ad_pat_consis__ghostg; auto.
  - apply ad_pat_consis__dot_univ_ghost. apply IHad_pat_consis; auto.
  - apply ad_pat_consis__ghost; auto.
  - apply ad_pat_consis__univ_ghost. apply IHad_pat_consis; auto.
  - eapply ad_pat_consis__univ_ghost_inh
      with (L := L `union` dom Θ `union` dom Θ').
    intros α0 Hα0.
    apply H0.
    + clear - Hα0; fsetdec.
    + simpl_env; apply uniq_push; [ exact Hu | clear - Hα0; fsetdec ].
    + apply a_wf_aenv__tvar; [ clear - Hα0; fsetdec | exact Hwf' ].
    + apply binds_sub_cons with (e := (α0 ~ abind_tvar)); exact Hsub.
    + intros β Hβ. simpl in Hβ. simpl.
      apply add_2. apply HscS; exact Hβ.
    + intros β Hβ.
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f α0)) as HupB;
        simpl in HupB.
      destruct (β == α0) as [-> | Hne]; [ simpl; clear; fsetdec | ].
      simpl. apply add_2. apply HscQ; clear - Hβ HupB Hne; fsetdec.
  - apply ad_pat_consis__univ_ghost_drop. apply IHad_pat_consis; auto.
  - eapply ad_pat_consis__flex_l.
    + eapply binds_strengthen; [ exact H | exact Hu | exact Hsub | apply HscS; fsetdec ].
    + apply IHad_pat_consis; auto.
      intros α0 Hα0.
      assert (Hbd' : binds α (abind_flex_mono_def τ) Θ')
        by (eapply binds_strengthen; [ exact H | exact Hu | exact Hsub | apply HscS; fsetdec ]).
      assert (Hwfτ : a_wf_ptyp Θ' τ) by (eapply a_wf_aenv_binds_def_wf; [ exact Hwf' | exact Hbd' ]).
      pose proof (a_wf_ptyp_ftv_dom Hwfτ) as Hftv.
      pose proof (ftvar_ptyp_to_uskl_syn τ) as Hco.
      clear - Hα0 Hftv Hco. fsetdec.
  - eapply ad_pat_consis__flex_r.
    + eapply binds_strengthen; [ exact H | exact Hu | exact Hsub | apply HscQ; fsetdec ].
    + apply IHad_pat_consis; auto.
      intros α0 Hα0.
      assert (Hbd' : binds α (abind_flex_mono_def τ) Θ')
        by (eapply binds_strengthen; [ exact H | exact Hu | exact Hsub | apply HscQ; fsetdec ]).
      assert (Hwfτ : a_wf_ptyp Θ' τ) by (eapply a_wf_aenv_binds_def_wf; [ exact Hwf' | exact Hbd' ]).
      pose proof (a_wf_ptyp_ftv_dom Hwfτ) as Hftv.
      pose proof (ftvar_ptyp_to_bskl_syn τ) as Hco.
      clear - Hα0 Hftv Hco. fsetdec.
Qed.

Lemma consis_precise_mono_join : forall Θ Δ A Qb,
  {{ ⊢ Θ }}a ->
  mono_ptyp A ->
  (forall α, α `in` ftvar_in_ptyp A -> a_binds_tvar α Θ) ->
  {{ empty ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn A) ∼ Qb }}ad ->
  {{ Θ ⨟ Δ ⊢ₚᵣ (ptyp_to_pskl A) ⊑ (bskl_to_pskl Qb) }}ad.
Proof.
  intros Θ Δ A Qb Hwf HmA Hvis Hjoin.
  destruct (consis_mono_join Hjoin Hwf (A := A) eq_refl HmA) as [C [HmC [HQb Heq]]].
  unfold ad_precise.
  rewrite (ptyp_to_bskl_inh_syn_eq HmA).
  subst Qb.
  rewrite (bskl_to_pskl_ptyp_to_bskl_syn C).
  rewrite (ptyp_to_bskl_inh_syn_eq HmC).
  apply tyequiv_mono_refine_syn; auto.
Qed.

Lemma bskl_to_pskl_msubst_bskl : forall κ Q,
  bskl_to_pskl (msubst_bskl κ Q) = msubst_pskl κ (bskl_to_pskl Q).
Proof.
  intros κ Q; induction Q; simpl; try reflexivity.
  - rewrite bskl_to_pskl_pskl_to_bskl_syn. reflexivity.
  - rewrite IHQ1, IHQ2. reflexivity.
  - rewrite IHQ. reflexivity.
  - rewrite IHQ. reflexivity.
  - rewrite IHQ. reflexivity.
Qed.

Lemma consis_ghost_target_inh : forall Ψ Θ Qb,
  {{ Ψ ⨟ Θ ⊢ˢ uskl_ghost ∼ Qb }}ad ->
  pskl_to_bskl_inh (bskl_to_pskl Qb) = Qb.
Proof.
  intros Ψ Θ Qb H.
  remember uskl_ghost as R eqn:HR.
  induction H; try discriminate HR.
  - rewrite bskl_to_pskl_pskl_to_bskl_inh. reflexivity.
  - reflexivity.
Qed.

Lemma ad_pat_consis_guarded_r : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  {{ ⊢ Θ }}a ->
  forall P,
    R = pskl_to_uskl P ->
    guarded_pskl P ->
    lc_bskl Q ->
    guarded_bskl Q.
Proof.
  intros Ψ Θ R Q Hc Hwf; induction Hc; intros P0 HeqS Hg Hlc;
    try solve [ destruct P0; simpl in HeqS; try discriminate;
                inversion Hg ].
  - destruct P0; simpl in HeqS; try discriminate.
    auto with fresco.
  - destruct P0; simpl in HeqS; try discriminate.
    auto with fresco.
  - destruct P0; simpl in HeqS; try discriminate.
    inversion Hlc; subst. apply guarded_bskl__arrow; assumption.
  -
    destruct P0; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    apply IHHc with (P := ptyp_to_pskl τ); auto.
    + symmetry. apply pskl_to_uskl_ptyp.
    + apply mono_ptyp_to_pskl_guarded.
      eapply a_wf_aenv_binds_def_mono; eauto.
  -  apply guarded_bskl__var.
Qed.

Lemma ad_pat_consis_guarded_not_quant : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  {{ ⊢ Θ }}a ->
  forall P,
    R = pskl_to_uskl P ->
    guarded_pskl P ->
    (forall Q0, Q <> bskl_all_syn Q0) /\ (forall Q0, Q <> bskl_univ_ghost Q0).
Proof.
  intros Ψ Θ R Q Hc Hwf; induction Hc; intros P0 HeqS Hg;
    try solve [ destruct P0; simpl in HeqS; try discriminate;
                inversion Hg ];
    try solve [ split; intros ? Hq; discriminate ].

  destruct P0; simpl in HeqS; try discriminate.
  inversion HeqS; subst.
  apply IHHc with (P := ptyp_to_pskl τ); auto.
  - symmetry. apply pskl_to_uskl_ptyp.
  - apply mono_ptyp_to_pskl_guarded.
    eapply a_wf_aenv_binds_def_mono; eauto.
Qed.

Lemma ad_refine_syn_univ_ghost_guarded_inv : forall Θ Δ Q Q',
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δ ⊢ᵣ (bskl_univ_ghost Q) ⊳ Q' }}ad ->
  guarded_bskl Q' ->
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad.
Proof.
  intros Θ Δ Q Q' Hwf Hr.
  remember (bskl_univ_ghost Q) as Qt eqn:HeqQt.
  induction Hr; intros Hg; try discriminate HeqQt.
  - inversion HeqQt; subst. exact Hr.
  - inversion Hg.
  - inversion Hg.
  - inversion HeqQt; subst.
    eapply ad_refine_syn__flex_r; [ exact H | ].
    apply IHHr; [ exact Hwf | reflexivity | ].
    apply mono_bskl_guarded, mono_ptyp_to_bskl_syn.
    eapply a_wf_aenv_binds_def_mono; eauto.
Qed.

Lemma ad_refine_pskl_univ_ghost_guarded_inv : forall Θ Δ P P',
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_univ_ghost P) ⊳ P' }}ad ->
  guarded_pskl P' ->
  {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ P' }}ad.
Proof.
  intros Θ Δ P P' Hwf Hr.
  remember (pskl_univ_ghost P) as Pt eqn:HeqPt.
  induction Hr; intros Hg; try discriminate HeqPt.
  - inversion HeqPt; subst. exact Hr.
  - inversion Hg.
  - inversion Hg.
  - inversion HeqPt; subst.
    eapply ad_refine_pskl__flex_r; [ exact H | ].
    apply IHHr; [ exact Hwf | reflexivity | ].
    apply mono_ptyp_to_pskl_guarded.
    eapply a_wf_aenv_binds_def_mono; eauto.
Qed.

Lemma ad_pat_consis_univ_ghost_guarded_inv : forall Ψ Θ P Q,
  {{ ⊢ Θ }}a ->
  {{ Ψ ⨟ Θ ⊢ˢ (uskl_univ_ghost (pskl_to_uskl P)) ∼ Q }}ad ->
  guarded_pskl P ->
  guarded_bskl Q ->
  {{ Ψ ⨟ Θ ⊢ˢ (pskl_to_uskl P) ∼ Q }}ad.
Proof.
  intros Ψ Θ P Q Hwf Hc.
  remember (uskl_univ_ghost (pskl_to_uskl P)) as R eqn:HeqS.
  induction Hc; intros HgP HgQ; try discriminate HeqS.
  - inversion HgQ.
  - inversion HgQ.
  - inversion HeqS; subst. exact Hc.
  - inversion HeqS; subst.
    eapply ad_pat_consis__flex_r; [ exact H | ].
    apply IHHc; [ exact Hwf | reflexivity | exact HgP | ].
    apply mono_bskl_guarded, mono_ptyp_to_bskl_syn.
    eapply a_wf_aenv_binds_def_mono; eauto.
Qed.

Lemma ad_refine_syn_univ_ghost_keep_inv : forall Θ Δ Q' Q,
  {{ ⊢ Θ }}a ->
  guarded_bskl Q' ->
  {{ Θ ⨟ Δ ⊢ᵣ (bskl_univ_ghost Q') ⊳ (bskl_univ_ghost Q) }}ad ->
  {{ Θ ⨟ Δ ⊢ᵣ Q' ⊳ Q }}ad.
Proof.
  intros Θ Δ Q' Q Hwf Hg Hr.
  inversion Hr; subst; try discriminate.
  - match goal with
    | Hsub : ad_refine_syn _ _ _ (bskl_univ_ghost _) |- _ =>
        exfalso; eapply (ad_refine_syn_not_univ_ghost_r Hsub);
          [ intro; subst; inversion Hg
          | intros ? ?; subst; inversion Hg
          | reflexivity ]
    end.
  - assumption.
Qed.

Lemma ad_refine_pskl_univ_ghost_keep_inv : forall Θ Δ P P',
  {{ ⊢ Θ }}a ->
  guarded_pskl P ->
  {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_univ_ghost P) ⊳ (pskl_univ_ghost P') }}ad ->
  {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ P' }}ad.
Proof.
  intros Θ Δ P P' Hwf Hg Hr.
  inversion Hr; subst; try discriminate.
  - match goal with
    | Hsub : ad_refine_pskl _ _ _ (pskl_univ_ghost _) |- _ =>
        exfalso; eapply (ad_refine_pskl_not_univ_ghost_r Hsub);
          [ intro; subst; inversion Hg
          | intros ? ?; subst; inversion Hg
          | reflexivity ]
    end.
  - assumption.
Qed.

Lemma consis_downarrow_subject : forall Ψ Θ R Q,
  ad_pat_consis Ψ Θ R Q ->
  {{ ⊢ Θ }}a ->
  forall P0 A,
    R = pskl_to_uskl P0 ->
    Q = ptyp_to_bskl_syn A -> mono_ptyp A ->
    ad_pat_consis Ψ Θ (pskl_to_uskl (⇓ˢ[ Θ ] P0)) Q.
Proof.
  intros Ψ Θ R Q Hc Hwf; induction Hc;
    intros P0 C0 HeqS HeqC HmC0;
    unfold ptyp_to_bskl_syn in *.
  -
    destruct P0; simpl in HeqS; try discriminate.
    simpl. apply ad_pat_consis__unit; assumption.
  -
    destruct P0 as [ | | αp | | | | ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    destruct C0 as [ | | αc | | ]; simpl in HeqC; try discriminate.
    inversion HeqC; subst.
    simpl.
    replace (ptyp_to_pskl (msubst_lookup (aenv_msubst Θ) αc))
       with (ptyp_to_pskl (⇓ᵗ[ Θ ] (ptyp_var_f αc))) by reflexivity.
    assert (Hwfx : a_wf_ptyp Θ (ptyp_var_f αc)) by (apply a_wf_ptyp__var; exact H0).
    assert (Hmono_x : mono_ptyp (⇓ᵗ[ Θ ] (ptyp_var_f αc)))
      by (apply mono_downarrow; [ exact Hwf | exact Hwfx | apply mono_ptyp__var ]).
    assert (Hwf_x : a_wf_ptyp Θ (⇓ᵗ[ Θ ] (ptyp_var_f αc)))
      by (apply a_wf_ptyp_downarrow_mono; [ exact Hwf | exact Hwfx | apply mono_ptyp__var ]).
    assert (Hvis : forall β, β `in` ftvar_in_ptyp (⇓ᵗ[ Θ ] (ptyp_var_f αc)) ->
                   a_binds_tvar β Θ)
      by (intros β Hβ; eapply a_wf_ptyp_ftv_tvarish; [ exact Hwf_x | exact Hβ ]).
    assert (Heqd : {{ Θ ⊢ (⇓ᵗ[ Θ ] (ptyp_var_f αc)) ≡ᵗ (ptyp_var_f αc) }}a).
    { apply a_tyequiv__sym.
      apply a_tyequiv_to_downarrow_mono;
        [ exact Hwf | exact Hwfx | apply mono_ptyp__var ]. }
    destruct (tyequiv_mono_consis_transport_q Heqd Hwf Hmono_x Hvis) as [_ Hfwd].
    rewrite pskl_to_uskl_ptyp.
    change (bskl_var_f αc) with (ptyp_to_bskl_syn (ptyp_var_f αc)).
    apply Hfwd.
    eapply ad_pat_consis_psi_cong;
      [ apply consis_mono_refl; [ exact Hmono_x | exact Hvis ]
      | fsetdec ].
  -
    destruct P0 as [ | | | S01 S02 | | | ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    destruct C0 as [ | | | C1 C2 | ]; simpl in HeqC; try discriminate.
    inversion HeqC; subst.
    inversion HmC0 as [ | | ? ? HmC1 HmC2 ]; subst.
    simpl.
    apply ad_pat_consis__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
      [ apply (IHHc1 Hwf S01 C1 eq_refl eq_refl HmC1)
      | apply (IHHc2 Hwf S02 C2 eq_refl eq_refl HmC2)
      | exact H ].
  -  destruct HmC0; simpl in HeqC; discriminate.
  -  destruct HmC0; simpl in HeqC; discriminate.
  -  destruct HmC0; simpl in HeqC; discriminate.
  -  destruct HmC0; simpl in HeqC; discriminate.
  -  destruct HmC0; simpl in HeqC; discriminate.
  -  destruct HmC0; simpl in HeqC; discriminate.
  -
    destruct P0; simpl in HeqS; try discriminate.
    simpl. apply ad_pat_consis__ghost; [ exact H ].
  -  destruct HmC0; simpl in HeqC; discriminate.
  -  destruct HmC0; simpl in HeqC; discriminate.
  -
    destruct P0 as [ | | | | | | S0t ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    simpl. apply ad_pat_consis__univ_ghost_drop.
    apply (IHHc Hwf S0t C0 eq_refl eq_refl HmC0).
  -
    destruct P0 as [ | | αv | | | | ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    simpl.
    assert (Hlk : msubst_lookup (aenv_msubst Θ) αv = ⇓ᵗ[ Θ ] τ)
      by (apply aenv_msubst_lookup_def; assumption).
    rewrite Hlk.
    rewrite <- msubst_pskl_embed_ptyp.
    apply (IHHc Hwf (ptyp_to_pskl τ) C0
             (eq_sym (pskl_to_uskl_ptyp τ)) eq_refl HmC0).
  -
    destruct C0; simpl in HeqC; try discriminate.
    inversion HeqC; subst.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    apply ad_pat_consis__flex_r with (τ := τ); [ exact H | ].
    apply (IHHc Hwf P0 τ eq_refl eq_refl Hmτ).
Qed.

Definition mu_consis (Θ : aenv) (κ : metasubst) (P0 P : pskl)
    (Θ0 : aenv) : mu_ty :=
  (V_consis Θ κ P0 P, (length Θ0, (1, 0))).

Definition mu_unify (Θ : aenv) (κ : metasubst) (α β : atom)
    (Θ0 : aenv) : mu_ty :=
  (V_unify Θ κ α β, (length Θ0, (0, 0))).

Definition mu_assign (Θ : aenv) (κ : metasubst) (α : atom) (P : pskl)
    (Ξ Θ0 : aenv) : mu_ty :=
  (V_assign Θ κ α P, (length Ξ + length Θ0, (0, length Θ0))).

Lemma ad_refine_syn_extend_ftv : forall Θ Δ Q Q',
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad ->
  forall Δ',
  (forall α1, α1 `in` Δ' -> α1 `in` Δ \/
     (α1 `notin` ftvar_in_bskl Q' /\
      (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
         α1 `notin` ftvar_in_ptyp τ))) ->
  {{ Θ ⨟ Δ' ⊢ᵣ Q ⊳ Q' }}ad.
Proof.
  intros * H; induction H; intros Δ' Hcond; simpl in *.
  - apply ad_refine_syn__unit.
  - apply ad_refine_syn__var.
  - apply ad_refine_syn_arrow_intro.
    + apply IHad_refine_syn1. intros α1 Hα1.
      destruct (Hcond α1 Hα1) as [HinΔ | [Hf Hd]];
        [ left; exact HinΔ | right; split; [ | exact Hd ] ].
      clear - Hf. fsetdec.
    + apply IHad_refine_syn2. intros α1 Hα1.
      destruct (Hcond α1 Hα1) as [HinΔ | [Hf Hd]];
        [ left; exact HinΔ | right; split; [ | exact Hd ] ].
      clear - Hf. fsetdec.
  - apply ad_refine_syn_all_intro with (L := L).
    intros α Hα.
    apply H1; [ exact Hα | ].
    intros α1 Hα1.
    destruct (α1 == α) as [-> | Hne]; [ left; clear; fsetdec | ].
    destruct (Hcond α1 ltac:(clear - Hα1 Hne; fsetdec)) as [HinΔ | [Hf Hd]];
      [ left; clear - HinΔ; fsetdec | right; split ].
    + pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper
                    Q' (bskl_var_f α)) as Hup.
      simpl in Hup. clear - Hf Hup Hne. fsetdec.
    + intros β τ Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
        [ discriminate | exact (Hd β τ Hb') ].
  - apply ad_refine_syn__ghost.
    apply inter_empty_pointwise. intros α1 Hα1.
    destruct (Hcond α1 Hα1) as [HinΔ | [Hf Hd]].
    + intro Hc.
      assert (Hin : α1 `in` Δ ∩ ftvar_in_pskl P)
        by (apply inter_3; assumption).
      rewrite H in Hin. clear - Hin. fsetdec.
    + rewrite ftvar_in_bskl_syn in Hf. exact Hf.
  - apply ad_refine_syn_univ_ghost_remove_intro. apply IHad_refine_syn.
    exact Hcond.
  - apply ad_refine_syn_univ_ghost_fill_intro with (L := L `union` Δ').
    intros α Hα.
    apply H1; [ clear - Hα; fsetdec | ].
    intros α1 Hα1.
    destruct (Hcond α1 Hα1) as [HinΔ | [Hf Hd]];
      [ left; exact HinΔ | right ].
    split.
    + pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper
                    Q' (bskl_var_f α)) as Hup.
      simpl in Hup.
      assert (Hne : α1 <> α) by (clear - Hα Hα1; fsetdec).
      clear - Hf Hup Hne. fsetdec.
    + intros β τ Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
        [ discriminate | exact (Hd β τ Hb') ].
  - apply ad_refine_syn_univ_ghost_keep_intro.
    apply IHad_refine_syn.
    intros α1 Hα1.
    destruct (Hcond α1 Hα1) as [HinΔ | [Hf Hd]];
      [ left; exact HinΔ | right; split; [ | exact Hd ] ].
    clear - Hf. fsetdec.
  - eapply ad_refine_syn__flex_l; [ eassumption | ].
    apply IHad_refine_syn. exact Hcond.
  - eapply ad_refine_syn__flex_r; [ eassumption | ].
    apply IHad_refine_syn.
    intros α1 Hα1.
    destruct (Hcond α1 Hα1) as [HinΔ | [Hf Hd]];
      [ left; exact HinΔ | right; split; [ | exact Hd ] ].
    rewrite ftvar_ptyp_to_bskl_syn. exact (Hd _ _ H).
Qed.

Lemma ad_refine_pskl_ghost_src_target_ftv : forall Θ Δ Pt,
  {{ Θ ⨟ Δ ⊢ᵣₚ pskl_ghost ⊳ Pt }}ad ->
  {{ ⊢ Θ }}a ->
  forall α1, α1 `in` Δ -> binds α1 abind_tvar Θ ->
  α1 `notin` ftvar_in_pskl Pt.
Proof.
  intros * H.
  remember pskl_ghost as R eqn:HeqS.
  induction H; intros Hwf α1 HγΔ Hbγ; try discriminate HeqS.
  -
    intro Hc.
    assert (Hin : α1 `in` Δ ∩ ftvar_in_pskl P')
      by (apply inter_3; assumption).
    rewrite H in Hin. clear - Hin. fsetdec.
  -
    simpl. intro Hc.
    assert (Heqγ : α1 = α) by (clear - Hc; fsetdec). subst α.
    pose proof (binds_unique _ _ _ _ _ H Hbγ (a_wf_aenv_uniq Hwf)) as Hcon.
    discriminate.
Qed.

Lemma ad_refine_syn_ghost_src_target_ftv : forall Θ Δ Qt,
  {{ Θ ⨟ Δ ⊢ᵣ bskl_ghost ⊳ Qt }}ad ->
  {{ ⊢ Θ }}a ->
  forall α1, α1 `in` Δ -> binds α1 abind_tvar Θ ->
  α1 `notin` ftvar_in_bskl Qt.
Proof.
  intros * H.
  remember bskl_ghost as R eqn:HeqS.
  induction H; intros Hwf α1 HγΔ Hbγ; try discriminate HeqS.
  -
    rewrite ftvar_in_bskl_syn.
    intro Hc.
    assert (Hin : α1 `in` Δ ∩ ftvar_in_pskl P)
      by (apply inter_3; assumption).
    rewrite H in Hin. clear - Hin. fsetdec.
  -
    simpl. intro Hc.
    assert (Heqγ : α1 = α) by (clear - Hc; fsetdec). subst α.
    pose proof (binds_unique _ _ _ _ _ H Hbγ (a_wf_aenv_uniq Hwf)) as Hcon.
    discriminate.
Qed.

Lemma ad_refine_syn_guarded_src_all_inh_absurd : forall Θ Δ Q Q',
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ (bskl_all_inh Q') }}ad ->
  guarded_bskl Q ->
  False.
Proof.
  intros * Hwf Hr.
  remember (bskl_all_inh Q') as T eqn:HeqT.
  induction Hr; intros Hg; try discriminate HeqT.
  -
    inversion Hg.
  -
    destruct P; simpl in HeqT; discriminate.
  -
    inversion Hg.
  -
    apply IHHr; [ exact Hwf | exact HeqT | ].
    apply mono_bskl_guarded, mono_ptyp_to_bskl_syn.
    eapply a_wf_aenv_binds_def_mono; eauto.
Qed.

Lemma ad_refine_syn_guarded_src_all_syn_absurd : forall Θ Δ Q Q',
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ (bskl_all_syn Q') }}ad ->
  guarded_bskl Q ->
  False.
Proof.
  intros * Hwf Hr.
  remember (bskl_all_syn Q') as T eqn:HeqT.
  induction Hr; intros Hg; try discriminate HeqT;
    try solve [ inversion Hg ].
  apply IHHr; [ exact Hwf | exact HeqT | ].
  apply mono_bskl_guarded, mono_ptyp_to_bskl_syn.
  eapply a_wf_aenv_binds_def_mono; eauto.
Qed.

Lemma ad_refine_pskl_guarded_src_all_syn_absurd : forall Θ Δ P P',
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ (pskl_all_syn P') }}ad ->
  guarded_pskl P ->
  False.
Proof.
  intros * Hwf Hr.
  remember (pskl_all_syn P') as T eqn:HeqT.
  induction Hr; intros Hg; try discriminate HeqT;
    try solve [ inversion Hg ].
  apply IHHr; [ exact Hwf | exact HeqT | ].
  apply mono_ptyp_to_pskl_guarded.
  eapply a_wf_aenv_binds_def_mono; eauto.
Qed.

Lemma bskl_to_pskl_subst_var : forall α' α Q,
  subst_pskl_in_pskl (pskl_var_f α') α (bskl_to_pskl Q)
  = bskl_to_pskl (subst_bskl_in_bskl (bskl_var_f α') α Q).
Proof.
  intros α' α Q; induction Q; simpl;
    try solve [ reflexivity
              | rewrite IHQ; reflexivity
              | rewrite IHQ1, IHQ2; reflexivity ].
  destruct_if;
    reflexivity.
Qed.

Lemma msubst_lookup_in_or : forall (ζ : metasubst) (β : atom),
  In (β, msubst_lookup ζ β) ζ \/
  (β `notin` dom ζ /\ msubst_lookup ζ β = ptyp_var_f β).
Proof.
  induction ζ as [ | [α1 τ] ζ' IH ]; intros β; simpl.
  - right. split; [ fsetdec | reflexivity ].
  - destruct (β == α1) as [-> | Hne].
    + left. left. reflexivity.
    + destruct (IH β) as [Hin | [Hni Heq]];
        [ left; right; exact Hin
        | right; split; [ clear - Hni Hne; fsetdec | exact Heq ] ].
Qed.

Lemma msubst_pskl_subst_var : forall ζ α α' P,
  α `notin` dom ζ ->
  α' `notin` dom ζ ->
  (forall α1 τ, In (α1, τ) ζ -> α `notin` ftvar_in_ptyp τ) ->
  subst_pskl_in_pskl (pskl_var_f α') α (msubst_pskl ζ P)
  = msubst_pskl ζ (subst_pskl_in_pskl (pskl_var_f α') α P).
Proof.
  intros ζ α α' P Hαd HXd Him;
    induction P as [ | n | β | Pa IHa Pb IHb | Pb IHb | | Pt IHt ]; simpl;
    try solve [ reflexivity
              | rewrite IHb; reflexivity
              | rewrite IHt; reflexivity
              | rewrite IHa, IHb; reflexivity ].

  destruct_if as [-> | Hne].
  -
    rewrite (msubst_lookup_notin ζ Hαd). simpl.
    destruct_if as [_ | Hc]; [ | congruence ].
    cbn [msubst_pskl].
    rewrite (msubst_lookup_notin ζ HXd). reflexivity.
  -
    cbn [msubst_pskl].
    destruct (msubst_lookup_in_or ζ β) as [Hin | [Hni Heq]].
    + apply subst_pskl_in_pskl_fresh_eq.
      pose proof (Him _ _ Hin) as Hfr.
      pose proof (ftvar_ptyp_to_pskl (msubst_lookup ζ β)) as Hfe.
      clear - Hfr Hfe. fsetdec.
    + rewrite Heq. simpl.
      destruct_if as [Hc | _]; [ congruence | reflexivity ].
Qed.

Lemma a_inc_images_ftv_dom : forall Θ0 ζ Θ,
  ζ ∷ Θ0 ⊑ Θ ->
  forall α1 τ, In (α1, τ) ζ -> ftvar_in_ptyp τ [<=] dom Θ.
Proof.
  intros Θ0 ζ Θ H; induction H; intros α10 τ0 Hin.
  - inversion Hin.
  - destruct Hin as [Heq | Hin];
      [ inversion Heq; subst; apply a_wf_ptyp_ftv_dom; assumption
      | eapply IHa_inc; exact Hin ].
  - destruct Hin as [Heq | Hin];
      [ inversion Heq; subst; apply a_wf_ptyp_ftv_dom; assumption
      | eapply IHa_inc; exact Hin ].
  - pose proof (IHa_inc _ _ Hin) as Hsub.
    intros α2 Hα2. repeat rewrite dom_app. simpl dom.
    pose proof (Hsub α2 Hα2). clear - H2. fsetdec.
  - pose proof (IHa_inc _ _ Hin) as Hsub.
    intros α2 Hα2. repeat rewrite dom_app. simpl dom.
    pose proof (Hsub α2 Hα2). clear - H2. fsetdec.
  - pose proof (IHa_inc _ _ Hin) as Hsub.
    intros α2 Hα2. repeat rewrite dom_app. simpl dom.
    pose proof (Hsub α2 Hα2). clear - H1. fsetdec.
Qed.

Lemma msubst_pskl_ftv_ex : forall ζ P α',
  α' `in` ftvar_in_pskl (msubst_pskl ζ P) ->
  exists β, β `in` ftvar_in_pskl P /\
            α' `in` ftvar_in_ptyp (msubst_lookup ζ β).
Proof.
  intros ζ P; induction P as [ | n | α2 | Pa IHa Pb IHb | Pb IHb | | Pt IHt ];
    intros α' Hα; simpl in *.
  - clear - Hα; fsetdec.
  - clear - Hα; fsetdec.
  - exists α2. split; [ fsetdec | ].
    rewrite ftvar_ptyp_to_pskl in Hα. exact Hα.
  - apply union_1 in Hα. destruct Hα as [H1 | H2].
    + destruct (IHa α' H1) as [β [HY1 HY2]].
      exists β; split; [ fsetdec | exact HY2 ].
    + destruct (IHb α' H2) as [β [HY1 HY2]].
      exists β; split; [ fsetdec | exact HY2 ].
  - destruct (IHb α' Hα) as [β [HY1 HY2]].
    exists β; split; [ fsetdec | exact HY2 ].
  - clear - Hα; fsetdec.
  - destruct (IHt α' Hα) as [β [HY1 HY2]].
    exists β; split; [ fsetdec | exact HY2 ].
Qed.

Lemma aenv_msubst_cons_def : forall α τ Θ,
  aenv_msubst ((α ~ abind_flex_mono_def τ) ++ Θ)
  = (α, msubst_ptyp (aenv_msubst Θ) τ) :: aenv_msubst Θ.
Proof. reflexivity. Qed.

Lemma aenv_msubst_image_ftv : forall Θ,
  {{ ⊢ Θ }}a ->
  forall β,
  ftvar_in_ptyp (msubst_lookup (aenv_msubst Θ) β) [<=] add β (dom Θ).
Proof.
  intros Θ Hwf; induction Hwf; intros β;
    try rewrite aenv_msubst_flex_head;
    try rewrite aenv_msubst_cons_def;
    try rewrite aenv_msubst_tvar;
    try rewrite aenv_msubst_var_typ;
    try rewrite aenv_msubst_var_skl.
  -  simpl. clear; fsetdec.
  -
    destruct (β == α) as [-> | Hne].
    + rewrite msubst_lookup_cons_eq. simpl. simpl_env.
      clear; fsetdec.
    + rewrite msubst_lookup_cons_neq by exact Hne. simpl_env.
      pose proof (IHHwf β) as Him. clear - Him. fsetdec.
  -
    destruct (β == α) as [-> | Hne].
    + rewrite msubst_lookup_cons_eq.
      intros α0 Hα0.
      destruct (msubst_ptyp_ftv _ _ Hα0) as [α2 [HZ1 HZ2]].
      assert (HZd : α2 `in` dom Θ)
        by (pose proof (a_wf_ptyp_ftv_dom H0) as Hsc;
            clear - Hsc HZ1; fsetdec).
      pose proof (IHHwf α2) as Him.
      simpl_env. clear - HZ2 Him HZd. fsetdec.
    + rewrite msubst_lookup_cons_neq by exact Hne. simpl_env.
      pose proof (IHHwf β) as Him. clear - Him. fsetdec.
  -  simpl_env.
    pose proof (IHHwf β) as Him. clear - Him. fsetdec.
  -  simpl_env.
    pose proof (IHHwf β) as Him. clear - Him. fsetdec.
  -  simpl_env.
    pose proof (IHHwf β) as Him. clear - Him. fsetdec.
Qed.

Lemma aenv_msubst_image_no_def : forall Θ,
  {{ ⊢ Θ }}a ->
  forall β α', α' `in` ftvar_in_ptyp (msubst_lookup (aenv_msubst Θ) β) ->
  forall τ, ~ binds α' (abind_flex_mono_def τ) Θ.
Proof.
  intros Θ Hwf; induction Hwf; intros β α' Hα τq Hb;
    try rewrite aenv_msubst_flex_head in Hα;
    try rewrite aenv_msubst_cons_def in Hα;
    try rewrite aenv_msubst_tvar in Hα;
    try rewrite aenv_msubst_var_typ in Hα;
    try rewrite aenv_msubst_var_skl in Hα.
  -  inversion Hb.
  -
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq1 Heq2] | Hb'];
      [ discriminate | ].
    destruct (β == α) as [-> | Hne].
    + rewrite msubst_lookup_cons_eq in Hα. simpl in Hα.
      assert (α' = α) by (clear - Hα; fsetdec). subst α'.
      apply binds_In in Hb'. contradiction.
    + rewrite msubst_lookup_cons_neq in Hα by exact Hne.
      exact (IHHwf β α' Hα τq Hb').
  -
    destruct (β == α) as [-> | Hne].
    + rewrite msubst_lookup_cons_eq in Hα.
      destruct (msubst_ptyp_ftv _ _ Hα) as [α2 [HZ1 HZ2]].
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq1 Heq2] | Hb'].
      * subst α'. exfalso.
        assert (HZd : α2 `in` dom Θ)
          by (pose proof (a_wf_ptyp_ftv_dom H0) as Hsc;
              clear - Hsc HZ1; fsetdec).
        pose proof (aenv_msubst_image_ftv Hwf α2) as Him.
        assert (Hin1 : α `in` add α2 (dom Θ))
          by (clear - HZ2 Him; fsetdec).
        assert (Hne1 : α <> α2) by (intro; subst; contradiction).
        clear - Hin1 Hne1 H. fsetdec.
      * exact (IHHwf α2 α' HZ2 τq Hb').
    + rewrite msubst_lookup_cons_neq in Hα by exact Hne.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq1 Heq2] | Hb'].
      * subst α'. exfalso.
        pose proof (aenv_msubst_image_ftv Hwf β) as Him.
        assert (Hin1 : α `in` add β (dom Θ))
          by (clear - Hα Him; fsetdec).
        assert (Hne1 : α <> β) by (intro; subst; contradiction).
        clear - Hin1 Hne1 H. fsetdec.
      * exact (IHHwf β α' Hα τq Hb').
  -
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq1 Heq2] | Hb'];
      [ discriminate | exact (IHHwf β α' Hα τq Hb') ].
  -
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq1 Heq2] | Hb'];
      [ discriminate | exact (IHHwf β α' Hα τq Hb') ].
  -
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq1 Heq2] | Hb'];
      [ discriminate | exact (IHHwf β α' Hα τq Hb') ].
Qed.

Lemma aenv_msubst_lookup_no_def : forall Θ α,
  (forall τ, ~ binds α (abind_flex_mono_def τ) Θ) ->
  msubst_lookup (aenv_msubst Θ) α = ptyp_var_f α.
Proof.
  induction Θ as [ | [α1 b] Θ' IH ]; intros α Hnd.
  - reflexivity.
  - destruct b as [ | A | Q | | τ0 ]; simpl aenv_msubst.
    + apply IH. intros τ Hb. apply (Hnd τ). unfold binds. right. exact Hb.
    + apply IH. intros τ Hb. apply (Hnd τ). unfold binds. right. exact Hb.
    + apply IH. intros τ Hb. apply (Hnd τ). unfold binds. right. exact Hb.
    + destruct (α == α1) as [-> | Hne].
      * rewrite msubst_lookup_cons_eq. reflexivity.
      * rewrite msubst_lookup_cons_neq by exact Hne.
        apply IH. intros τ Hb. apply (Hnd τ). unfold binds. right. exact Hb.
    + destruct (α == α1) as [-> | Hne].
      * exfalso. apply (Hnd τ0). unfold binds. left. reflexivity.
      * rewrite msubst_lookup_cons_neq by exact Hne.
        apply IH. intros τ Hb. apply (Hnd τ). unfold binds. right. exact Hb.
Qed.

Lemma downarrow_idem_sub_ptyp : forall Θ Θs A,
  {{ ⊢ Θ }}a ->
  (forall x (b : abind), binds x b Θs -> binds x b Θ) ->
  ⇓ᵗ[ Θs ] (⇓ᵗ[ Θ ] A) = ⇓ᵗ[ Θ ] A.
Proof.
  intros * Hwf Hsub.
  apply msubst_ptyp_lookup_refl. intros α Hα.
  apply aenv_msubst_lookup_no_def. intros τ Hb.
  destruct (msubst_ptyp_ftv _ _ Hα) as [β [HY1 HY2]].
  assert (Hno : forall τ0, ~ binds α (abind_flex_mono_def τ0) Θ)
    by (intros τ0; eapply aenv_msubst_image_no_def;
        [ exact Hwf | exact HY2 ]).
  exact (Hno τ (Hsub _ _ Hb)).
Qed.

Lemma downarrow_idem_sub_pskl : forall Θ Θs P,
  {{ ⊢ Θ }}a ->
  (forall x (b : abind), binds x b Θs -> binds x b Θ) ->
  ⇓ˢ[ Θs ] (⇓ˢ[ Θ ] P) = ⇓ˢ[ Θ ] P.
Proof.
  intros * Hwf Hsub.
  apply msubst_pskl_lookup_refl. intros α Hα.
  apply aenv_msubst_lookup_no_def. intros τ Hb.
  destruct (msubst_pskl_ftv_ex _ _ Hα) as [β [HY1 HY2]].
  assert (Hno : forall τ0, ~ binds α (abind_flex_mono_def τ0) Θ)
    by (intros τ0; eapply aenv_msubst_image_no_def;
        [ exact Hwf | exact HY2 ]).
  exact (Hno τ (Hsub _ _ Hb)).
Qed.

Lemma a_pskl_tyequiv_weaken : forall Θ Θ' P P',
  (forall x (b : abind), binds x b Θ -> binds x b Θ') ->
  {{ Θ ⊢ P ≡ˢ P' }}a ->
  {{ Θ' ⊢ P ≡ˢ P' }}a.
Proof.
  intros * Hmon. apply a_pskl_tyequiv_transport.
  intros; apply a_pskl_tyequiv__flex_def; auto.
Qed.

Lemma a_scope_pskl_weaken : forall Θ Θ' P,
  (forall x (b : abind), binds x b Θ -> binds x b Θ') ->
  a_scope_pskl Θ P ->
  a_scope_pskl Θ' P.
Proof.
  intros Θ Θ' P Hmon [Hlc Hb]. split; [ exact Hlc | ].
  intros α Hα. destruct (Hb α Hα) as [Hb' | [Hb' | [τ Hb']]];
    [ left | right; left | right; right; exists τ ]; apply Hmon; exact Hb'.
Qed.

Lemma a_inc_var_skl_mid_strip_id : forall Ξ x P Θ0 κ Θ1,
  a_decls Ξ ->
  is_id_msubst κ ->
  κ ∷ (Ξ ++ (x ~ abind_var_skl P) ++ Θ0) ⊑ ((x ~ abind_var_skl P) ++ Θ1) ->
  κ ∷ (Ξ ++ Θ0) ⊑ Θ1.
Proof.
  induction Ξ as [ | [a b] Ξ' IH ]; intros x P Θ0 κ Θ1 Hdec Hid Hinc.
  - simpl in Hinc.
    destruct (a_inc_var_skl_inv Hinc)
      as [Ξv [P' [Θ2 [Heqt [Heqv [Hsuf Hinc']]]]]].
    destruct Ξv as [ | [z bz] Ξv' ].
    + simpl in Heqt. inversion Heqt; subst. exact Hinc'.
    + exfalso. simpl in Heqt. inversion Heqt; subst.
      inversion Hsuf as [ | z0 b0 Ξ0 Hsuf0 Hsb ]; subst.
      inversion Hsb.
  - inversion Hdec as [ | α1 Ξ'' Hdec' [Heqγ HeqΞ] ]; subst.
    simpl in Hinc.
    inversion Hinc as [ | Θs κs Θts aa τ Hinc' Hwfτ Hmτ | | | | ]; subst.
    apply is_id_msubst_inv in Hid as [Heqτ Hid']; subst.
    apply a_inc__flex; [ | | apply mono_ptyp__var ].
    2:{ apply a_wf_ptyp__var.
        inversion Hwfτ as [ | Θw Xw Hbt | | ]; subst.
        eapply a_binds_tvar_strip_mid with
          (c := x) (b := abind_var_skl P) (Ξ := (@nil (atom * abind)));
          [ simpl; exact Hbt
          | intro Hc; inversion Hc
          | intro Hc; inversion Hc
          | intros ? Hc; inversion Hc ]. }
    eapply IH; [ exact Hdec' | exact Hid' | exact Hinc' ].
Qed.

Lemma a_inc_equiv_decls_cons_inv : forall a Ξ' Θ0 Θ' κ1 κ2 σ1 σ2,
  uniq (((a ~ abind_flex_mono) ++ Ξ') ++ Θ0) ->
  dom κ1 [=] dom ((a ~ abind_flex_mono) ++ Ξ') ->
  dom σ1 [=] dom ((a ~ abind_flex_mono) ++ Ξ') ->
  a_inc_equiv (((a ~ abind_flex_mono) ++ Ξ') ++ Θ0) (κ1 ++ κ2) (σ1 ++ σ2) Θ' ->
  exists τ1 τ2 κ1' σ1',
    κ1 = (a, τ1) :: κ1' /\ σ1 = (a, τ2) :: σ1' /\
    uniq (Ξ' ++ Θ0) /\ dom κ1' [=] dom Ξ' /\ dom σ1' [=] dom Ξ' /\
    a_inc_equiv (Ξ' ++ Θ0) (κ1' ++ κ2) (σ1' ++ σ2) Θ' /\
    {{ Θ' ⊢ τ1 ≡ᵗ τ2 }}a.
Proof.
  intros a Ξ' Θ0 Θ' κ1 κ2 σ1 σ2 Huq Hdκ Hdσ Hie.
  assert (Huκ : uniq (κ1 ++ κ2))
    by (eapply a_inc_equiv_uniq_l; [ exact Hie | exact Huq ]).
  assert (Huσ : uniq (σ1 ++ σ2))
    by (eapply a_inc_equiv_uniq_r; [ exact Hie | exact Huq ]).
  assert (HaΞ : a `notin` dom Ξ')
    by (clear - Huq; simpl_env in Huq; solve_uniq).
  assert (Huq' : uniq (Ξ' ++ Θ0))
    by (clear - Huq; simpl_env in Huq; solve_uniq).
  destruct κ1 as [ | [ar tr] κ1' ];
    [ exfalso; rewrite dom_nil in Hdκ;
      assert (Hin : a `in` dom ((a ~ abind_flex_mono) ++ Ξ'))
        by (simpl; fsetdec);
      rewrite <- Hdκ in Hin; clear - Hin; fsetdec | ].
  destruct σ1 as [ | [asg ts] σ1' ];
    [ exfalso; rewrite dom_nil in Hdσ;
      assert (Hin : a `in` dom ((a ~ abind_flex_mono) ++ Ξ'))
        by (simpl; fsetdec);
      rewrite <- Hdσ in Hin; clear - Hin; fsetdec | ].
  assert (Harκ : ar `notin` dom κ1')
    by (clear - Huκ; simpl_env in Huκ; solve_uniq).
  assert (Hasσ : asg `notin` dom σ1')
    by (clear - Huσ; simpl_env in Huσ; solve_uniq).
  simpl in Hie.
  inversion Hie as [ | R q1 q2 T aa u1 u2 Hie' Hequ | | | | ]; subst.
  simpl_env in Hdκ; simpl_env in Hdσ.
  exists tr, ts, κ1', σ1'.
  split; [ reflexivity | ]. split; [ reflexivity | ].
  split; [ exact Huq' | ].
  split; [ clear - Hdκ Harκ HaΞ; fsetdec | ].
  split; [ clear - Hdσ Hasσ HaΞ; fsetdec | ].
  split; [ exact Hie' | exact Hequ ].
Qed.
Arguments a_inc_equiv_decls_cons_inv {a Ξ' Θ0 Θ' κ1 κ2 σ1 σ2}.

Lemma a_inc_equiv_mid_insert_var_skl :
  forall Ξ x Θ0 Θ' Ξv κ1 κ2 σ1 σ2 Pm Pm',
  a_decls Ξ ->
  uniq (Ξ ++ Θ0) ->
  dom κ1 [=] dom Ξ ->
  dom σ1 [=] dom Ξ ->
  {{ Θ' ⊢ Pm' ≡ˢ (msubst_pskl κ2 Pm) }}a ->
  a_suffix Ξv ->
  a_inc_equiv (Ξ ++ Θ0) (κ1 ++ κ2) (σ1 ++ σ2) Θ' ->
  a_inc_equiv (Ξ ++ (x ~ abind_var_skl Pm) ++ Θ0)
              (κ1 ++ κ2) (σ1 ++ σ2)
              (Ξv ++ (x ~ abind_var_skl Pm') ++ Θ').
Proof.
  induction Ξ as [ | [a bnd] Ξ' IH ];
    intros x Θ0 Θ' Ξv κ1 κ2 σ1 σ2 Pm Pm' Hdec Huq Hdκ Hdσ Heqm Hsuf Hie.
  - rewrite dom_nil in Hdκ, Hdσ.
    apply metasubst_dom_empty in Hdκ; apply metasubst_dom_empty in Hdσ;
      subst.
    simpl in Hie |- *.
    apply a_inc_equiv__var_skl; [ exact Hie | exact Heqm | exact Hsuf ].
  - inversion Hdec as [ | α1 Ξ'' Hdec' [Heqγ HeqΞ] ]; subst.
    destruct (a_inc_equiv_decls_cons_inv Huq Hdκ Hdσ Hie)
      as (τa & τb & κ1' & σ1' & -> & -> & Huq' & Hdκ' & Hdσ' & Hie' & Hequ).
    simpl. apply a_inc_equiv__flex.
    2:{ apply a_tyequiv_weaken with (Θ := Θ');
        [ intros y b Hb; simpl_env; auto | exact Hequ ]. }
    apply IH; auto.
Qed.

Lemma a_inc_equiv_mid_insert_tvar :
  forall Ξ c Θ0 Θ' Ξv κ1 κ2 σ1 σ2,
  a_decls Ξ ->
  uniq (Ξ ++ Θ0) ->
  dom κ1 [=] dom Ξ ->
  dom σ1 [=] dom Ξ ->
  a_suffix Ξv ->
  a_inc_equiv (Ξ ++ Θ0) (κ1 ++ κ2) (σ1 ++ σ2) Θ' ->
  a_inc_equiv (Ξ ++ (c ~ abind_tvar) ++ Θ0)
              (κ1 ++ κ2) (σ1 ++ σ2)
              (Ξv ++ (c ~ abind_tvar) ++ Θ').
Proof.
  induction Ξ as [ | [a bnd] Ξ' IH ];
    intros c Θ0 Θ' Ξv κ1 κ2 σ1 σ2 Hdec Huq Hdκ Hdσ Hsuf Hie.
  - rewrite dom_nil in Hdκ, Hdσ.
    apply metasubst_dom_empty in Hdκ; apply metasubst_dom_empty in Hdσ;
      subst.
    simpl in Hie |- *.
    apply a_inc_equiv__tvar; [ exact Hie | exact Hsuf ].
  - inversion Hdec as [ | α1 Ξ'' Hdec' [Heqγ HeqΞ] ]; subst.
    destruct (a_inc_equiv_decls_cons_inv Huq Hdκ Hdσ Hie)
      as (τa & τb & κ1' & σ1' & -> & -> & Huq' & Hdκ' & Hdσ' & Hie' & Hequ).
    simpl. apply a_inc_equiv__flex.
    2:{ apply a_tyequiv_weaken with (Θ := Θ');
        [ intros y b Hb; simpl_env; auto | exact Hequ ]. }
    apply IH; auto.
Qed.

Lemma a_inc_mid_strip_flex_def : forall Ξ β τd Θ0 κ Θ,
  a_decls Ξ ->
  κ ∷ (Ξ ++ (β ~ abind_flex_mono_def τd) ++ Θ0) ⊑ Θ ->
  exists κ1 τ κ2,
    κ = κ1 ++ (β, τ) :: κ2 /\
    dom κ1 [=] dom Ξ /\
    κ2 ∷ Θ0 ⊑ Θ /\
    κ1 ++ κ2 ∷ (Ξ ++ Θ0) ⊑ Θ /\
    a_wf_ptyp Θ τ /\ mono_ptyp τ /\
    {{ Θ ⊢ τ ≡ᵗ (msubst_ptyp κ2 τd) }}a.
Proof.
  induction Ξ as [ | [a b] Ξ' IH ]; intros β τd Θ0 κ Θ Hdec Hinc.
  -
    simpl in Hinc.
    inversion Hinc as [ | | Θs κs Θt βs τ0 τ' Hinc' Hwfτ Hmτ Heqv
                          [Heqβ Heqκ] Heqt | | | ]; subst.
    exists (@nil (atom * ptyp)), τ', κs. simpl.
    split; [ reflexivity | ].
    split; [ clear; fsetdec | ].
    split; [ exact Hinc' | ].
    split; [ exact Hinc' | ].
    split; [ exact Hwfτ | ].
    split; [ exact Hmτ | exact Heqv ].
  -
    inversion Hdec as [ | α1 Ξ'' Hdec' [Heqγ HeqΞ] ]; subst.
    simpl in Hinc.
    inversion Hinc as [ | Θs κs Θt as' τ Hinc' Hwfτ Hmτ [Heqa Heqκ] Heqt
                      | | | | ]; subst.
    destruct (IH β τd Θ0 κs Θ Hdec' Hinc')
      as [κ1 [τ2 [κ2 [Heqκ [Hdom [Hinc2 [Hrec [Hwf2 [Hm2 Heqv2]]]]]]]]].
    exists ((a, τ) :: κ1), τ2, κ2. simpl.
    split; [ rewrite Heqκ; reflexivity | ].
    split; [ clear - Hdom; simpl_env; fsetdec | ].
    split; [ exact Hinc2 | ].
    split; [ apply a_inc__flex; auto | ].
    split; [ exact Hwf2 | ].
    split; [ exact Hm2 | exact Heqv2 ].
Qed.

Lemma a_inc_equiv_mid_insert_flex_def :
  forall Ξ β τd Θ0 Θ κ1 κ2 σ1 σ2 τ1 τ2,
  a_decls Ξ ->
  uniq (Ξ ++ Θ0) ->
  dom κ1 [=] dom Ξ ->
  dom σ1 [=] dom Ξ ->
  {{ Θ ⊢ τ1 ≡ᵗ τ2 }}a ->
  {{ Θ ⊢ τ1 ≡ᵗ (msubst_ptyp κ2 τd) }}a ->
  a_inc_equiv (Ξ ++ Θ0) (κ1 ++ κ2) (σ1 ++ σ2) Θ ->
  a_inc_equiv (Ξ ++ (β ~ abind_flex_mono_def τd) ++ Θ0)
              (κ1 ++ (β, τ1) :: κ2) (σ1 ++ (β, τ2) :: σ2) Θ.
Proof.
  induction Ξ as [ | [a bnd] Ξ' IH ];
    intros β τd Θ0 Θ κ1 κ2 σ1 σ2 τ1 τ2 Hdec Huq Hdκ Hdσ Heqτ Heqd Hie.
  - rewrite dom_nil in Hdκ, Hdσ.
    apply metasubst_dom_empty in Hdκ; apply metasubst_dom_empty in Hdσ;
      subst.
    simpl in Hie |- *.
    apply a_inc_equiv__flex_def;
      [ exact Hie | exact Heqτ | exact Heqd ].
  - inversion Hdec as [ | α1 Ξ'' Hdec' [Heqγ HeqΞ] ]; subst.
    destruct (a_inc_equiv_decls_cons_inv Huq Hdκ Hdσ Hie)
      as (τa & τb & κ1' & σ1' & -> & -> & Huq' & Hdκ' & Hdσ' & Hie' & Hequ).
    simpl. apply a_inc_equiv__flex; [ | exact Hequ ].
    apply IH; auto.
Qed.

Lemma a_inc_tvar_mid_strip_id : forall Ξ c Θ0 κ Θ1,
  a_decls Ξ ->
  uniq (Ξ ++ (c ~ abind_tvar) ++ Θ0) ->
  is_id_msubst κ ->
  κ ∷ (Ξ ++ (c ~ abind_tvar) ++ Θ0) ⊑ ((c ~ abind_tvar) ++ Θ1) ->
  κ ∷ (Ξ ++ Θ0) ⊑ Θ1.
Proof.
  induction Ξ as [ | [a b] Ξ' IH ]; intros c Θ0 κ Θ1 Hdec Huq Hid Hinc.
  - simpl in Hinc.
    destruct (a_inc_tvar_inv Hinc) as [Ξv [Θ2 [Heqt [Hsuf Hinc']]]].
    destruct Ξv as [ | [z bz] Ξv' ].
    + simpl in Heqt. inversion Heqt; subst. exact Hinc'.
    + exfalso. simpl in Heqt. inversion Heqt; subst.
      inversion Hsuf as [ | z0 b0 Ξ0 Hsuf0 Hsb ]; subst.
      inversion Hsb.
  - inversion Hdec as [ | α1 Ξ'' Hdec' [Heqγ HeqΞ] ]; subst.
    assert (Hac : a <> c)
      by (clear - Huq; simpl_env in Huq; solve_uniq).
    assert (Huq' : uniq (Ξ' ++ (c ~ abind_tvar) ++ Θ0))
      by (clear - Huq; simpl_env in Huq; solve_uniq).
    simpl in Hinc.
    inversion Hinc as [ | Θs κs Θts aa τ Hinc' Hwfτ Hmτ | | | | ]; subst.
    apply is_id_msubst_inv in Hid as [Heqτ Hid']; subst.
    apply a_inc__flex; [ | | apply mono_ptyp__var ].
    2:{ apply a_wf_ptyp__var.
        inversion Hwfτ as [ | Θw Xw Hbt | | ]; subst.
        eapply a_binds_tvar_strip_mid with
          (c := c) (b := abind_tvar) (Ξ := (@nil (atom * abind)));
          [ simpl; exact Hbt
          | intro Hc; inversion Hc; subst; exact (Hac eq_refl)
          | intro Hc; inversion Hc
          | intros ? Hc; inversion Hc ]. }
    eapply IH; [ exact Hdec' | exact Huq' | exact Hid' | exact Hinc' ].
Qed.

Definition consis_complete_at (m : mu_ty) : Prop :=
  forall (N : atoms) Δ1 Δ2 Θ0 P0 P κ Θ Ψ Qb,
    m = mu_consis Θ κ P0 P Θ0 ->
    {{ ⊢ Θ0 }}a ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
    (forall α, α `in` (Δ1 `union` Δ2) -> binds α abind_tvar Θ0) ->
    no_flex_dep (Δ1 `union` Δ2) Θ0 ->
    flex_above_free (Δ1 `union` Δ2) Θ0 ->
    κ ∷ Θ0 ⊑ Θ ->
    {{ ⊢ Θ }}a ->
    no_flex_dep (Δ1 `union` Δ2) Θ ->
    Ψ [=] empty ->
    {{ Ψ ⨟ Θ ⊢ˢ (pskl_to_uskl (msubst_pskl κ P)) ∼ Qb }}ad ->
    {{ Θ ⨟ Δ1 ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Qb }}ad ->
    {{ Θ ⨟ Δ2 ⊢ᵣₚ (msubst_pskl κ P) ⊳ (bskl_to_pskl Qb) }}ad ->
    {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Qb) }}a ->
    exists P1 Θ1,
      a_consis Δ1 Δ2 Θ0 P0 P P1 Θ1 /\
      (forall γ, γ `in` dom Θ1 -> γ `in` dom Θ0 \/ γ `notin` N) /\
      (forall κ1, is_id_msubst κ1 -> κ1 ∷ Θ0 ⊑ Θ1 ->
         exists ζ,
           ζ ∷ Θ1 ⊑ Θ /\
           a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ /\
           {{ Θ ⨟ (Δ1 `union` Δ2) ⊢ₚᵣ (msubst_bskl ζ (pskl_to_bskl_syn P1)) ⊑ (bskl_to_pskl Qb) }}ad).

Definition unify_complete_at (m : mu_ty) : Prop :=
  forall (N : atoms) Θ0 α β κ Θ,
    m = mu_unify Θ κ α β Θ0 ->
    {{ ⊢ Θ0 }}a ->
    a_flex_tvar Θ0 α ->
    a_flex_tvar Θ0 β ->
    κ ∷ Θ0 ⊑ Θ ->
    {{ ⊢ Θ }}a ->
    {{ Θ ⊢ (msubst_lookup κ α) ≡ᵗ (msubst_lookup κ β) }}a ->
    exists Θ1,
      {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a /\
      (forall γ, γ `in` dom Θ1 -> γ `in` dom Θ0 \/ γ `notin` N) /\
      (forall κ1, is_id_msubst κ1 -> κ1 ∷ Θ0 ⊑ Θ1 ->
         exists ζ,
           ζ ∷ Θ1 ⊑ Θ /\
           a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ).

Definition assign_complete_at (m : mu_ty) : Prop :=
  forall (N : atoms) Θ0 Ξ α P κ Θ,
    m = mu_assign Θ κ α P Ξ Θ0 ->
    a_decls Ξ ->
    {{ ⊢ (Ξ ++ Θ0) }}a ->
    a_flex_tvar Θ0 α ->
    {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P }}a ->
    a_non_flex (Ξ ++ Θ0) P ->
    dom Ξ [<=] ftvar_in_pskl P ->
    κ ∷ (Ξ ++ Θ0) ⊑ Θ ->
    {{ ⊢ Θ }}a ->
    {{ empty ⨟ Θ ⊢ˢ (pskl_to_uskl (msubst_pskl κ P))
                 ∼ (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup κ α))) }}ad ->
    exists Θ1,
      {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a /\
      (forall γ, γ `in` dom Θ1 -> γ `in` dom (Ξ ++ Θ0) \/ γ `notin` N) /\
      (forall κ1, is_id_msubst κ1 -> κ1 ∷ (Ξ ++ Θ0) ⊑ Θ1 ->
         exists ζ,
           ζ ∷ Θ1 ⊑ Θ /\
           a_inc_equiv (Ξ ++ Θ0) κ (msubst_compose ζ κ1) Θ).

Definition complete_at (m : mu_ty) : Prop :=
  consis_complete_at m /\ unify_complete_at m /\ assign_complete_at m.

Lemma mu_lt_intro : forall (V' V n' n t' t k' k : nat),
  (V' < V \/
   (V' = V /\ (n' < n \/ (n' = n /\ (t' < t \/ (t' = t /\ k' < k)))))) ->
  mu_lt (V', (n', (t', k'))) (V, (n, (t, k))).
Proof.
  intros. unfold mu_lt, lex; simpl.
  destruct H as [HV | [-> [Hn | [-> [Ht | [-> Hk]]]]]].
  - left; exact HV.
  - right; split; [ reflexivity | left; exact Hn ].
  - right; split; [ reflexivity | right; split;
      [ reflexivity | left; exact Ht ] ].
  - right; split; [ reflexivity | right; split;
      [ reflexivity | right; split; [ reflexivity | exact Hk ] ] ].
Qed.

Lemma avoid_relay_cons : forall (α1 : atom) (b1 b0 : abind) (N : atoms)
    (Θ0' Θ1' : aenv),
  (forall γ, γ `in` dom Θ1' -> γ `in` dom Θ0' \/ γ `notin` (add α1 N)) ->
  forall γ, γ `in` dom ((α1 ~ b1) ++ Θ1') ->
    γ `in` dom ((α1 ~ b0) ++ Θ0') \/ γ `notin` N.
Proof.
  intros α1 b1 b0 N Θ0' Θ1' Hnew.
  eapply avoid_relay with (D0' := dom Θ0') (D1' := dom Θ1');
    [ exact Hnew | simpl_env | simpl_env | simpl_env ]; fsetdec.
Qed.

Lemma avoid_relay_cons_mid : forall (α1 : atom) (b1 b0 : abind) (N : atoms)
    (Ξ Θ0' Θ1' : aenv),
  (forall γ, γ `in` dom Θ1' -> γ `in` dom (Ξ ++ Θ0') \/ γ `notin` (add α1 N)) ->
  forall γ, γ `in` dom ((α1 ~ b1) ++ Θ1') ->
    γ `in` dom (Ξ ++ (α1 ~ b0) ++ Θ0') \/ γ `notin` N.
Proof.
  intros α1 b1 b0 N Ξ Θ0' Θ1' Hnew.
  eapply avoid_relay with (D0' := dom (Ξ ++ Θ0')) (D1' := dom Θ1');
    [ exact Hnew | simpl_env | simpl_env | simpl_env ]; fsetdec.
Qed.

Lemma avoid_truncate_cons : forall (α : atom) (b : abind) (N : atoms)
    (Θ0 Θ1 : aenv),
  (forall γ, γ `in` dom ((α ~ b) ++ Θ1) ->
     γ `in` dom ((α ~ b) ++ Θ0) \/ γ `notin` N) ->
  α `notin` dom Θ1 ->
  forall γ, γ `in` dom Θ1 -> γ `in` dom Θ0 \/ γ `notin` N.
Proof.
  intros α b N Θ0 Θ1 Hnew Hα.
  eapply avoid_truncate with (α := α); [ | exact Hα ].
  intros γ Hγ.
  destruct (Hnew γ ltac:(simpl_env; clear - Hγ; solve_notin_auto)) as [Hin | Hni];
    [ left; simpl_env in Hin; clear - Hin; fsetdec | right; exact Hni ].
Qed.

Lemma avoid_same_dom : forall (α1 : atom) (b1 b0 : abind) (N : atoms)
    (Θ0' : aenv),
  forall γ, γ `in` dom ((α1 ~ b1) ++ Θ0') ->
    γ `in` dom ((α1 ~ b0) ++ Θ0') \/ γ `notin` N.
Proof. intros. left. simpl_env in *. fsetdec. Qed.

Lemma Vpskl_ptyp_to_pskl : forall Θ κ A,
  Vpskl Θ κ (ptyp_to_pskl A) = Vptyp Θ κ A.
Proof.
  intros. unfold Vpskl, Vptyp.
  rewrite msubst_pskl_embed_ptyp. rewrite msubst_pskl_embed_ptyp.
  apply size_pskl_ptyp_to_pskl.
Qed.

Lemma Vvar_strengthen_mid : forall Ξ (c : atom) b Θt κ α,
  uniq (Ξ ++ (c ~ b) ++ Θt) ->
  a_wf_ptyp Θt (msubst_lookup κ α) ->
  Vvar (Ξ ++ (c ~ b) ++ Θt) κ α = Vvar Θt κ α.
Proof.
  intros Ξ c b Θt κ α Huniq Hwf. unfold Vvar.
  rewrite <- app_assoc in Huniq |- *.
  rewrite (downarrow_app_agree_ptyp _ _ _ Huniq
             (a_wf_ptyp_ftv_dom Hwf)).
  reflexivity.
Qed.

Local Ltac ftv_rev_extend α Fr β Θ Hwf HbX Hdefs HwfY HbXY HdefsY :=
  assert (HwfY : {{ ⊢ ((β ~ abind_tvar) ++ Θ) }}a)
    by (apply a_wf_aenv__tvar; [ clear - Fr; solve_notin_auto | exact Hwf ]);
  assert (HbXY : binds α abind_tvar ((β ~ abind_tvar) ++ Θ))
    by (apply binds_cons_3; exact HbX);
  assert (HdefsY : forall β0 τ,
            binds β0 (abind_flex_mono_def τ) ((β ~ abind_tvar) ++ Θ) ->
            α `notin` ftvar_in_ptyp τ)
    by (intros β0 τ Hb;
        apply binds_cons_1 in Hb as [[_ Heqb] | Hb];
        [ discriminate Heqb | exact (Hdefs _ _ Hb) ]).

Lemma ad_refine_syn_rigid_ftv_rev : forall Θ Δ Qs Qt α',
  {{ ⊢ Θ }}a ->
  binds α' abind_tvar Θ ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
               α' `notin` ftvar_in_ptyp τ) ->
  {{ Θ ⨟ Δ ⊢ᵣ Qs ⊳ Qt }}ad ->
  α' `notin` ftvar_in_bskl Qt ->
  α' `notin` ftvar_in_bskl Qs.
Proof.
  intros Θ Δ Qs Qt α' Hwf HbX Hdefs Hr.
  induction Hr; intros Hout; simpl in *.
  -  clear; fsetdec.
  -  clear - Hout; fsetdec.
  -
    assert (Hn1 : α' `notin` ftvar_in_bskl Q1)
      by (apply IHHr1;
          [ assumption | assumption | assumption | clear - Hout; fsetdec ]).
    assert (Hn2 : α' `notin` ftvar_in_bskl Q2)
      by (apply IHHr2;
          [ assumption | assumption | assumption | clear - Hout; fsetdec ]).
    clear - Hn1 Hn2; fsetdec.
  -
    pick fresh β for (L `union` dom Θ `union` singleton α'
                        `union` ftvar_in_bskl Q' `union` ftvar_in_bskl Q).
    ftv_rev_extend α' Fr β Θ Hwf HbX Hdefs HwfY HbXY HdefsY.
    assert (HnT : α' `notin`
              ftvar_in_bskl (open_bskl_wrt_bskl Q' (bskl_var_f β))).
    { pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q' (bskl_var_f β))
        as Hup.
      simpl in Hup. clear - Hout Hup Fr. fsetdec. }
    pose proof (H1 β ltac:(clear - Fr; solve_notin_auto) HwfY HbXY HdefsY HnT) as HnS.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_lower Q (bskl_var_f β))
      as Hlo.
    clear - HnS Hlo. fsetdec.
  -  clear; fsetdec.
  -  exact (IHHr Hwf HbX Hdefs Hout).
  -
    pick fresh β for (L `union` dom Θ `union` singleton α'
                        `union` ftvar_in_bskl Q' `union` ftvar_in_bskl Q).
    ftv_rev_extend α' Fr β Θ Hwf HbX Hdefs HwfY HbXY HdefsY.
    assert (HnT : α' `notin`
              ftvar_in_bskl (open_bskl_wrt_bskl Q' (bskl_var_f β))).
    { pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q' (bskl_var_f β))
        as Hup.
      simpl in Hup. clear - Hout Hup Fr. fsetdec. }
    pose proof (H1 β ltac:(clear - Fr; solve_notin_auto) HwfY HbXY HdefsY HnT) as HnS.
    simpl in HnS. clear - HnS. fsetdec.
  -  exact (IHHr Hwf HbX Hdefs Hout).
  -
    assert (Hne : α' <> α).
    { intro Heq; subst α.
      pose proof (binds_unique _ _ _ _ _ HbX H (a_wf_aenv_uniq Hwf)) as Hc;
        discriminate. }
    clear - Hne; fsetdec.
  -
    apply IHHr; [ assumption | assumption | assumption | ].
    rewrite ftvar_ptyp_to_bskl_syn.
    apply (Hdefs _ _ H).
Qed.

Lemma ad_pat_consis_rigid_ftv_rev_scoped_open :
  forall L Θ α' D Q R (Rβ : atom -> uskl),
  {{ ⊢ Θ }}a ->
  binds α' abind_tvar Θ ->
  α' `notin` D ->
  (forall α1 τ, binds α1 (abind_flex_mono_def τ) Θ -> α1 `in` D ->
               ftvar_in_ptyp τ [<=] D) ->
  (forall β, β `notin` L ->
     {{ ⊢ ((β ~ abind_tvar) ++ Θ) }}a ->
     binds α' abind_tvar ((β ~ abind_tvar) ++ Θ) ->
     forall D', α' `notin` D' ->
     (forall α1 τ, binds α1 (abind_flex_mono_def τ) ((β ~ abind_tvar) ++ Θ) ->
                  α1 `in` D' -> ftvar_in_ptyp τ [<=] D') ->
     ftvar_in_bskl (open_bskl_wrt_bskl Q (bskl_var_f β)) [<=] D' ->
     α' `notin` ftvar_in_uskl (Rβ β)) ->
  (forall β, ftvar_in_uskl R [<=] ftvar_in_uskl (Rβ β)) ->
  ftvar_in_bskl Q [<=] D ->
  α' `notin` ftvar_in_uskl R.
Proof.
  intros L Θ α' D Q R Rβ Hwf HbX HXD Hdefs IH Hlo Hout.
  pick fresh β for (L `union` dom Θ `union` singleton α' `union` D
                      `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
  assert (HwfY : {{ ⊢ ((β ~ abind_tvar) ++ Θ) }}a)
    by (apply a_wf_aenv__tvar; [ clear - Fr; solve_notin_auto | exact Hwf ]).
  assert (HbXY : binds α' abind_tvar ((β ~ abind_tvar) ++ Θ))
    by (apply binds_cons_3; exact HbX).
  assert (HdefsY' : forall α1 τ,
            binds α1 (abind_flex_mono_def τ) ((β ~ abind_tvar) ++ Θ) ->
            α1 `in` (add β D) -> ftvar_in_ptyp τ [<=] (add β D)).
  { intros α1 τ Hb HγD.
    apply binds_cons_1 in Hb as [[_ Heqb] | Hb];
      [ discriminate Heqb | ].
    assert (Hγne : α1 <> β).
    { intro Heq; subst α1. apply binds_In in Hb.
      clear - Hb Fr. fsetdec. }
    assert (HγD' : α1 `in` D) by (clear - HγD Hγne; fsetdec).
    pose proof (Hdefs _ _ Hb HγD') as Hs. clear - Hs. fsetdec. }
  assert (HnS : α' `notin` ftvar_in_uskl (Rβ β)).
  { assert (HβL : β `notin` L) by (clear - Fr; solve_notin_auto).
    assert (HαD : α' `notin` add β D) by (clear - HXD Fr; solve_notin_auto).
    apply (IH β HβL HwfY HbXY (add β D) HαD HdefsY').
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f β))
      as Hup.
    simpl in Hup. clear - Hout Hup. fsetdec. }
  pose proof (Hlo β) as Hlo'. clear - HnS Hlo'. fsetdec.
Qed.
Lemma ad_pat_consis_rigid_ftv_rev_scoped : forall Ψ Θ R' Qt α' D,
  {{ ⊢ Θ }}a ->
  binds α' abind_tvar Θ ->
  α' `notin` D ->
  (forall α1 τ, binds α1 (abind_flex_mono_def τ) Θ -> α1 `in` D ->
               ftvar_in_ptyp τ [<=] D) ->
  {{ Ψ ⨟ Θ ⊢ˢ R' ∼ Qt }}ad ->
  ftvar_in_bskl Qt [<=] D ->
  α' `notin` ftvar_in_uskl R'.
Proof.
  intros Ψ Θ R' Qt α' D Hwf HbX HXD Hdefs Hc.
  revert D HXD Hdefs.
  induction Hc; intros D HXD Hdefs Hout; simpl in *.
  -  clear; fsetdec.
  -  clear - Hout HXD; fsetdec.
  -
    assert (Hn1 : α' `notin` ftvar_in_uskl R1)
      by (apply (IHHc1 Hwf HbX D HXD Hdefs); clear - Hout; fsetdec).
    assert (Hn2 : α' `notin` ftvar_in_uskl R2)
      by (apply (IHHc2 Hwf HbX D HXD Hdefs); clear - Hout; fsetdec).
    clear - Hn1 Hn2; fsetdec.
  -
    eapply ad_pat_consis_rigid_ftv_rev_scoped_open
      with (Rβ := fun β => open_uskl_wrt_uskl R (uskl_var_f β));
      eauto using ftvar_in_uskl_open_uskl_wrt_uskl_lower.
  -
    eapply ad_pat_consis_rigid_ftv_rev_scoped_open
      with (Rβ := fun β => open_uskl_wrt_uskl R (uskl_var_f β));
      eauto using ftvar_in_uskl_open_uskl_wrt_uskl_lower.
  -
    eapply ad_pat_consis_rigid_ftv_rev_scoped_open
      with (Rβ := fun β => open_uskl_wrt_uskl R (uskl_var_f β));
      eauto using ftvar_in_uskl_open_uskl_wrt_uskl_lower.
  -
    eapply ad_pat_consis_rigid_ftv_rev_scoped_open
      with (Rβ := fun β => open_uskl_wrt_uskl R (uskl_var_f β));
      eauto using ftvar_in_uskl_open_uskl_wrt_uskl_lower.
  -  clear; fsetdec.
  -  apply (IHHc Hwf HbX D HXD Hdefs Hout).
  -  clear; fsetdec.
  -  apply (IHHc Hwf HbX D HXD Hdefs Hout).
  -
    eapply ad_pat_consis_rigid_ftv_rev_scoped_open
      with (Rβ := fun _ => uskl_univ_ghost R); eauto.
    intros _. simpl. clear. fsetdec.
  -  apply (IHHc Hwf HbX D HXD Hdefs Hout).
  -
    assert (Hne : α' <> α).
    { intro Heq; subst α.
      pose proof (binds_unique _ _ _ _ _ HbX H (a_wf_aenv_uniq Hwf)) as Hc';
        discriminate. }
    clear - Hne; fsetdec.
  -
    apply (IHHc Hwf HbX D HXD Hdefs).
    rewrite ftvar_ptyp_to_bskl_syn.
    apply (Hdefs _ _ H). clear - Hout. fsetdec.
Qed.

Lemma ad_pat_consis_rigid_ftv_rev : forall Ψ Θ R' Qt α',
  {{ ⊢ Θ }}a ->
  binds α' abind_tvar Θ ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
               α' `notin` ftvar_in_ptyp τ) ->
  {{ Ψ ⨟ Θ ⊢ˢ R' ∼ Qt }}ad ->
  α' `notin` ftvar_in_bskl Qt ->
  α' `notin` ftvar_in_uskl R'.
Proof.
  intros Ψ Θ R' Qt α' Hwf HbX Hdefs Hc Hout.
  eapply ad_pat_consis_rigid_ftv_rev_scoped
    with (D := remove α' (dom Θ `union` ftvar_in_bskl Qt));
    [ exact Hwf | exact HbX | clear; fsetdec | | exact Hc | ].
  - intros β τ Hb Hβ.
    assert (Hscope : ftvar_in_ptyp τ [<=] dom Θ)
      by (eapply a_wf_aenv_def_ftv_dom; eauto).
    pose proof (Hdefs β τ Hb) as Hfresh.
    clear - Hscope Hfresh; fsetdec.
  - clear - Hout; fsetdec.
Qed.

Lemma a_wf_pskl_msubst_inc_gen : forall Θ0 κ Θ,
  κ ∷ Θ0 ⊑ Θ ->
  {{ ⊢ Θ0 }}a ->
  forall Θ1 Δ P,
  {{ Θ1 ⨟ Δ ⊢ₚₛ P }}a ->
  forall Θ',
  (forall β, a_binds_tvar β Θ1 -> β `in` dom κ -> a_binds_tvar β Θ0) ->
  (forall α, α `in` Δ -> α `notin` dom κ) ->
  (forall β γ, a_binds_tvar β Θ1 ->
     γ `in` ftvar_in_ptyp (msubst_lookup κ β) ->
     a_binds_tvar γ Θ' /\ (β `notin` Δ -> γ `notin` Δ)) ->
  {{ Θ' ⨟ Δ ⊢ₚₛ (msubst_pskl κ P) }}a.
Proof.
  intros Θ0 κ Θ Hinc Hwf0 Θ1 Δ P Hwf; induction Hwf;
    intros Θ' Hκ0 HΔ Himg; simpl.
  - apply a_wf_pskl__unit.
  -
    destruct (AtomSetProperties.In_dec α (dom κ)) as [Hin | Hni].
    + pose proof (a_inc_lookup_wf Hinc Hwf0 (Hκ0 α H Hin)) as Hwfτ.
      eapply a_wf_pskl_tvar_mono_ftv;
        [ apply a_wf_ptyp_to_wf_pskl; exact Hwfτ | ].
      intros γ Hγ _. rewrite ftvar_ptyp_to_pskl in Hγ.
      exact (proj1 (Himg α γ H Hγ)).
    + rewrite (msubst_lookup_notin κ Hni). simpl.
      apply a_wf_pskl__var.
      apply (proj1 (Himg α α H
               ltac:(rewrite (msubst_lookup_notin κ Hni); simpl; clear; fsetdec))).
  - apply a_wf_pskl__arrow;
      [ apply IHHwf1 | apply IHHwf2 ]; assumption.
  -
    assert (Hlcκ : msubst_lc κ) by (eapply a_inc_msubst_lc; eauto).
    apply a_wf_pskl__all with (L := L `union` dom κ `union` dom Θ').
    intros α Hα.
    rewrite <- msubst_pskl_open_lc;
      [ | exact Hlcκ | clear - Hα; fsetdec ].
    apply H0; [ clear - Hα; fsetdec | | | ].
    + intros β Hβ Hβκ.
      destruct (a_binds_tvar_cons_tvar_inv Hβ) as [Heq | Hβ'];
        [ subst β; exfalso; clear - Hα Hβκ; fsetdec | exact (Hκ0 β Hβ' Hβκ) ].
    + intros β Hβ.
      destruct (β == α) as [-> | Hne].
      * clear - Hα; fsetdec.
      * apply HΔ. clear - Hβ Hne; fsetdec.
    + intros β γ Hβ Hγ.
      destruct (a_binds_tvar_cons_tvar_inv Hβ) as [Heq | Hβ'].
      * subst β.
        rewrite (@msubst_lookup_notin κ α ltac:(clear - Hα; fsetdec)) in Hγ.
        simpl in Hγ. assert (γ = α) by (clear - Hγ; fsetdec). subst γ.
        split; [ apply a_binds_tvar_cons_tvar; left; reflexivity | ].
        intros Hc. exfalso. clear - Hc. fsetdec.
      * destruct (Himg β γ Hβ' Hγ) as [Hγt Hγn].
        assert (Hγd : γ `in` dom Θ')
          by (destruct Hγt as [Hb|[Hb|[τ Hb]]]; apply binds_In in Hb; exact Hb).
        split; [ apply a_binds_tvar_cons_tvar; right; exact Hγt | ].
        intros Hβn.
        assert (Hβn' : β `notin` Δ) by (clear - Hβn; fsetdec).
        specialize (Hγn Hβn').
        assert (γ <> α) by (intro; subst; clear - Hγd Hα; fsetdec).
        clear - Hγn H1. fsetdec.
  - apply a_wf_pskl__ghost.
  -
    apply a_wf_pskl__univ_ghost.
    + eapply guarded_pskl_msubst_inc; eauto.
    + apply IHHwf.
      * intros β Hβ Hβκ. apply a_binds_tvar_aenv_minus in Hβ as [Hβ _].
        exact (Hκ0 β Hβ Hβκ).
      * intros β Hβ. exfalso. clear - Hβ. fsetdec.
      * intros β γ Hβ Hγ. apply a_binds_tvar_aenv_minus in Hβ as [Hβ Hβn].
        destruct (Himg β γ Hβ Hγ) as [Hγt Hγn].
        split; [ apply a_binds_tvar_aenv_minus; split; auto | ].
        intros _. clear. fsetdec.
Qed.

Lemma a_wf_pskl_msubst_inc : forall Θ0 κ Θ Δ P,
  κ ∷ Θ0 ⊑ Θ ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ Δ ⊢ₚₛ P }}a ->
  (forall α, α `in` Δ -> α `notin` dom κ) ->
  (forall β γ, a_binds_tvar β Θ0 -> β `notin` Δ ->
     γ `in` ftvar_in_ptyp (msubst_lookup κ β) -> γ `notin` Δ) ->
  {{ Θ ⨟ Δ ⊢ₚₛ (msubst_pskl κ P) }}a.
Proof.
  intros Θ0 κ Θ Δ P Hinc Hwf0 Hwf HΔ Himg.
  eapply a_wf_pskl_msubst_inc_gen; [ exact Hinc | exact Hwf0 | exact Hwf
                                   | intros β Hβ _; exact Hβ | exact HΔ | ].
  intros β γ Hβ Hγ. split.
  - pose proof (a_inc_lookup_wf Hinc Hwf0 Hβ) as Hwfτ.
    eapply a_wf_ptyp_ftv_tvarish; eauto.
  - intros Hβn. exact (Himg β γ Hβ Hβn Hγ).
Qed.

Lemma refine_join_reinherit : forall Θr Δ P' P0,
  {{ Θr ⨟ Δ ⊢ᵣₚ P' ⊳ P0 }}ad ->
  forall Θj Δw,
  {{ ⊢ Θr }}a ->
  {{ ⊢ Θj }}a ->
  (forall x b, binds x b Θr -> binds x b Θj) ->
  {{ Θr ⨟ Δw ⊢ₚₛ P' }}a ->
  {{ empty ⨟ Θj ⊢ˢ (pskl_to_uskl P') ∼ (pskl_to_bskl_syn P0) }}ad ->
  {{ Θr ⨟ Δ ⊢ᵣ (pskl_to_bskl_inh P') ⊳ (pskl_to_bskl_inh P0) }}ad.
Proof.
  intros Θr Δ P' P0 Hr.
  induction Hr; intros Θj Δw Hwfr Hwf Hincl HwfA Hj; simpl in Hj |- *.
  -  apply ad_refine_syn__unit.
  -  apply ad_refine_syn__var; exact H.
  -
    inversion HwfA; subst.
    inversion Hj; subst.
    apply ad_refine_syn_arrow_intro;
      [ eapply IHHr1 | eapply IHHr2 ]; try eassumption;
      (eapply ad_pat_consis_psi_cong; [ eassumption | fsetdec ]).
  -
    inversion HwfA; subst.
    inversion Hj; subst.
    match goal with
    | Hn : forall _, _ -> ad_pat_consis _ _ _ _ |- _ => rename Hn into Hsub
    end.
    match goal with
    | Hn : forall _, _ -> a_wf_pskl _ _ _ |- _ => rename Hn into Hwfb
    end.
    simpl.
    match type of Hsub with
    | forall _, _ `notin` ?LL -> _ =>
        match type of Hwfb with
        | forall _, _ `notin` ?LW -> _ =>
            apply ad_refine_syn_all_intro with
              (L := L `union` LL `union` LW `union` dom Θ `union` dom Θj
                    `union` ftvar_in_pskl P `union` ftvar_in_pskl P')
        end
    end.
    intros α Hα.
    rewrite <- pskl_to_bskl_inh_open, <- pskl_to_bskl_inh_open.
    apply (H0 α ltac:(clear - Hα; solve_notin_auto) ((α ~ abind_tvar) ++ Θj) (add α Δw)).
    + apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwfr ].
    + apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ].
    + intros x b Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqx Heqb] | Hb'];
        [ subst; unfold binds; left; reflexivity
        | apply binds_cons_3; apply Hincl; exact Hb' ].
    + apply Hwfb. clear - Hα; fsetdec.
    + rewrite pskl_to_uskl_open_var, pskl_to_bskl_syn_open.
      apply Hsub. clear - Hα; fsetdec.
  -
    pose proof (consis_ghost_target_inh Hj) as Hqi.
    rewrite bskl_to_pskl_pskl_to_bskl_syn in Hqi.
    rewrite Hqi. apply ad_refine_syn__ghost; exact H.
  -
    assert (HgP : guarded_pskl P) by (inversion HwfA; assumption).
    assert (HwfPΔ : {{ Θ ⨟ Δw ⊢ₚₛ P }}a)
      by (apply a_wf_pskl_univ_ghost_body; exact HwfA).
    apply ad_refine_syn_univ_ghost_remove_intro.
    apply (IHHr Θj Δw Hwfr Hwf Hincl HwfPΔ).

    inversion Hj; subst.
    +
      exfalso.
      match goal with
      | HeqQ : pskl_to_bskl_syn P' = bskl_univ_ghost _ |- _ =>
          destruct P'; simpl in HeqQ; try discriminate
      | HeqQ : bskl_univ_ghost _ = pskl_to_bskl_syn P' |- _ =>
          destruct P'; simpl in HeqQ; try discriminate
      end.
      eapply (ad_refine_pskl_not_univ_ghost_r Hr);
        [ intro; subst; inversion HgP
        | intros ? ?; subst; inversion HgP
        | reflexivity ].
    +
      exfalso.
      match goal with
      | HeqQ : pskl_to_bskl_syn P' = bskl_all_inh _ |- _ =>
          destruct P'; simpl in HeqQ; discriminate
      | HeqQ : bskl_all_inh _ = pskl_to_bskl_syn P' |- _ =>
          destruct P'; simpl in HeqQ; discriminate
      end.
    +
      assumption.
    +
      match goal with
      | HeqQ : pskl_to_bskl_syn P' = bskl_var_f _ |- _ =>
          destruct P'; simpl in HeqQ; try discriminate;
          inversion HeqQ; subst
      | HeqQ : bskl_var_f _ = pskl_to_bskl_syn P' |- _ =>
          destruct P'; simpl in HeqQ; try discriminate;
          inversion HeqQ; subst
      end.
      eapply ad_pat_consis_univ_ghost_guarded_inv;
        [ exact Hwf | | exact HgP | apply guarded_bskl__var ].
      eapply ad_pat_consis__flex_r; eassumption.
  -
    exfalso.
    assert (HgP : guarded_pskl P) by (inversion HwfA; assumption).
    inversion Hj; subst.
    match goal with
    | Hdrop : {{ _ ⨟ _ ⊢ˢ (pskl_to_uskl P) ∼ _ }}ad |- _ =>
        exact (proj1 (ad_pat_consis_guarded_not_quant Hdrop Hwf eq_refl HgP)
                 _ eq_refl)
    end.
  -
    assert (HgP : guarded_pskl P) by (inversion HwfA; assumption).
    assert (HwfPΔ : {{ Θ ⨟ Δw ⊢ₚₛ P }}a)
      by (apply a_wf_pskl_univ_ghost_body; exact HwfA).
    apply ad_refine_syn_univ_ghost_keep_intro.
    apply (IHHr Θj Δw Hwfr Hwf Hincl HwfPΔ).
    inversion Hj; subst.
    +  assumption.
    +
      exfalso.
      match goal with
      | Hdrop : {{ _ ⨟ _ ⊢ˢ (pskl_to_uskl P) ∼ _ }}ad |- _ =>
          exact (proj2 (ad_pat_consis_guarded_not_quant Hdrop Hwf eq_refl HgP)
                   _ eq_refl)
      end.
  -
    assert (Hmτ : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwfr | exact H ]).
    apply ad_refine_syn__flex_l with (τ := τ); [ exact H | ].
    rewrite <- (ptyp_to_bskl_inh_syn_eq Hmτ).
    eapply IHHr with (Δw := Δw); try eassumption.
    + apply a_wf_ptyp_to_wf_pskl.
      eapply a_wf_aenv_binds_def_wf; [ exact Hwfr | exact H ].
    + rewrite pskl_to_uskl_ptyp.
      eapply consis_unfold_def_subject;
        [ exact Hj | exact Hwf | reflexivity | apply Hincl; exact H ].
  -
    assert (Hmτ : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwfr | exact H ]).
    apply ad_refine_syn__flex_r with (τ := τ); [ exact H | ].
    rewrite <- (ptyp_to_bskl_inh_syn_eq Hmτ).
    eapply IHHr with (Δw := Δw); try eassumption.
    unfold ptyp_to_bskl_syn.
    eapply consis_unfold_def_join;
      [ exact Hj | exact Hwf | reflexivity | apply Hincl; exact H ].
Qed.

Lemma consis_forall_subject_transport : forall Ψ Θ R Qt,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Qt }}ad ->
  forall R0 R0' L0,
  R = uskl_all_syn R0 ->
  (forall α, α `notin` L0 -> forall Ψ' Q',
     {{ Ψ' ⨟ ((α ~ abind_tvar) ++ Θ) ⊢ˢ
       (open_uskl_wrt_uskl R0 (uskl_var_f α)) ∼ Q' }}ad ->
     {{ Ψ' ⨟ ((α ~ abind_tvar) ++ Θ) ⊢ˢ
       (open_uskl_wrt_uskl R0' (uskl_var_f α)) ∼ Q' }}ad) ->
  {{ Ψ ⨟ Θ ⊢ˢ (uskl_all_syn R0') ∼ Qt }}ad.
Proof.
  intros Ψ Θ R Qt Hc; induction Hc; intros R0 R0' L0 HeqS Htr;
    try discriminate HeqS.
  -
    inversion HeqS; subst.
    apply ad_pat_consis__forall_inh_untagged with (L := L `union` L0).
    intros α Hα.
    apply Htr; [ clear - Hα; fsetdec | ].
    apply H; clear - Hα; fsetdec.
  -
    inversion HeqS; subst.
    apply ad_pat_consis__forall_syn with (L := L `union` L0).
    intros α Hα.
    apply Htr; [ clear - Hα; fsetdec | ].
    apply H; clear - Hα; fsetdec.
  -
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    eapply IHHc; eauto.
Qed.

Lemma consis_univ_ghost_subject_transport : forall Ψ Θ R Qt,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Qt }}ad ->
  {{ ⊢ Θ }}a ->
  forall R0 R0',
  R = uskl_univ_ghost R0 ->
  (forall Θ' Ψ' Q',
     {{ ⊢ Θ' }}a ->
     (forall x b, binds x b Θ -> binds x b Θ') ->
     {{ Ψ' ⨟ Θ' ⊢ˢ R0 ∼ Q' }}ad -> {{ Ψ' ⨟ Θ' ⊢ˢ R0' ∼ Q' }}ad) ->
  {{ Ψ ⨟ Θ ⊢ˢ (uskl_univ_ghost R0') ∼ Qt }}ad.
Proof.
  intros Ψ Θ R Qt Hc; induction Hc; intros HwfΘ R0 R0' HeqS Htr;
    try discriminate HeqS.
  -
    inversion HeqS; subst.
    apply ad_pat_consis__univ_ghost.
    apply (Htr Θ); [ exact HwfΘ | intros x b Hb; exact Hb | exact Hc ].
  -
    inversion HeqS; subst.
    apply ad_pat_consis__univ_ghost_inh with (L := L `union` dom Θ).
    intros α Hα.
    assert (HwfX : {{ ⊢ ((α ~ abind_tvar) ++ Θ) }}a)
      by (apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact HwfΘ ]).
    apply (H0 α ltac:(clear - Hα; solve_notin_auto) HwfX R0 R0' eq_refl).
    intros Θ' Ψ' Q' Hwf' Hincl' Hc'.
    apply (Htr Θ' Ψ' Q' Hwf'); [ | exact Hc' ].
    intros x b Hb. apply Hincl'. apply binds_cons_3. exact Hb.
  -
    inversion HeqS; subst.
    apply ad_pat_consis__univ_ghost_drop.
    apply (Htr Θ); [ exact HwfΘ | intros x b Hb; exact Hb | exact Hc ].
  -
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    eapply IHHc; eauto.
Qed.

Lemma skl_tyequiv_consis_transport : forall Θ P P',
  {{ Θ ⊢ P ≡ˢ P' }}a ->
  forall Θ',
  {{ ⊢ Θ' }}a ->
  (forall x b, binds x b Θ -> binds x b Θ') ->
  (forall Ψ Qt, {{ Ψ ⨟ Θ' ⊢ˢ (pskl_to_uskl P) ∼ Qt }}ad ->
                {{ Ψ ⨟ Θ' ⊢ˢ (pskl_to_uskl P') ∼ Qt }}ad) /\
  (forall Ψ Qt, {{ Ψ ⨟ Θ' ⊢ˢ (pskl_to_uskl P') ∼ Qt }}ad ->
                {{ Ψ ⨟ Θ' ⊢ˢ (pskl_to_uskl P) ∼ Qt }}ad).
Proof.
  intros Θ P P' Heq; induction Heq; intros Θ' Hwf' Hincl.
  -  split; intros Ψ Qt Hc; exact Hc.
  -
    destruct (IHHeq Θ' Hwf' Hincl) as [Hd1 Hd2].
    split; [ exact Hd2 | exact Hd1 ].
  -
    destruct (IHHeq1 Θ' Hwf' Hincl) as [H1l H1r].
    destruct (IHHeq2 Θ' Hwf' Hincl) as [H2l H2r].
    split; intros Ψ Qt Hc; [ apply H2l, H1l, Hc | apply H1r, H2r, Hc ].
  -
    split; intros Ψ Qt Hc.
    +
      rewrite pskl_to_uskl_ptyp.
      eapply consis_unfold_def_subject;
        [ exact Hc | exact Hwf' | reflexivity | apply Hincl; exact H ].
    +
      simpl.
      eapply ad_pat_consis__flex_l; [ apply Hincl; exact H | ].
      rewrite pskl_to_uskl_ptyp in Hc. exact Hc.
  -
    destruct (IHHeq1 Θ' Hwf' Hincl) as [H1l H1r].
    destruct (IHHeq2 Θ' Hwf' Hincl) as [H2l H2r].
    split; intros Ψ Qt Hc; simpl in Hc |- *.
    + eapply consis_arrow_subject_transport;
        [ exact Hc | reflexivity | exact H1l | exact H2l ].
    + eapply consis_arrow_subject_transport;
        [ exact Hc | reflexivity | exact H1r | exact H2r ].
  -
    split; intros Ψ Qt Hc; simpl in Hc |- *.
    + eapply consis_forall_subject_transport with (L0 := L `union` dom Θ');
        [ exact Hc | reflexivity | ].
      intros α Hα Ψ' Q' Hc'.
      assert (HwfX : {{ ⊢ ((α ~ abind_tvar) ++ Θ') }}a)
        by (apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf' ]).
      assert (HinclX : forall x b, binds x b Θ ->
                binds x b ((α ~ abind_tvar) ++ Θ'))
        by (intros x b Hb; apply binds_cons_3; apply Hincl; exact Hb).
      destruct (H0 α ltac:(clear - Hα; solve_notin_auto)
                  ((α ~ abind_tvar) ++ Θ') HwfX HinclX) as [Hl _].
      rewrite <- pskl_to_uskl_open_var in Hc'.
      rewrite <- pskl_to_uskl_open_var.
      apply Hl. exact Hc'.
    + eapply consis_forall_subject_transport with (L0 := L `union` dom Θ');
        [ exact Hc | reflexivity | ].
      intros α Hα Ψ' Q' Hc'.
      assert (HwfX : {{ ⊢ ((α ~ abind_tvar) ++ Θ') }}a)
        by (apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf' ]).
      assert (HinclX : forall x b, binds x b Θ ->
                binds x b ((α ~ abind_tvar) ++ Θ'))
        by (intros x b Hb; apply binds_cons_3; apply Hincl; exact Hb).
      destruct (H0 α ltac:(clear - Hα; solve_notin_auto)
                  ((α ~ abind_tvar) ++ Θ') HwfX HinclX) as [_ Hr].
      rewrite <- pskl_to_uskl_open_var in Hc'.
      rewrite <- pskl_to_uskl_open_var.
      apply Hr. exact Hc'.
  -
    split; intros Ψ Qt Hc; simpl in Hc |- *.
    + eapply consis_univ_ghost_subject_transport;
        [ exact Hc | exact Hwf' | reflexivity | ].
      intros Θ'' Ψ' Q' Hwf'' Hincl' Hc'.
      destruct (IHHeq Θ'' Hwf''
                  (fun x b Hb => Hincl' x b (Hincl x b Hb))) as [Hl _].
      apply Hl. exact Hc'.
    + eapply consis_univ_ghost_subject_transport;
        [ exact Hc | exact Hwf' | reflexivity | ].
      intros Θ'' Ψ' Q' Hwf'' Hincl' Hc'.
      destruct (IHHeq Θ'' Hwf''
                  (fun x b Hb => Hincl' x b (Hincl x b Hb))) as [_ Hr].
      apply Hr. exact Hc'.
Qed.

Lemma ad_refine_pskl_mono_refl : forall Θ Δ τ,
  mono_ptyp τ ->
  a_wf_ptyp Θ τ ->
  {{ Θ ⨟ Δ ⊢ᵣₚ (ptyp_to_pskl τ) ⊳ (ptyp_to_pskl τ) }}ad.
Proof.
  intros Θ Δ τ Hm Hwf.
  apply ad_refine_pskl_refl.
  apply a_wf_pskl_mono_ptyp; assumption.
Qed.

Lemma ad_refine_syn_unfold_def_source : forall Θ Δ Q Qt,
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ Qt }}ad ->
  {{ ⊢ Θ }}a ->
  forall α1 τ, Q = bskl_var_f α1 ->
  binds α1 (abind_flex_mono_def τ) Θ ->
  {{ Θ ⨟ Δ ⊢ᵣ (ptyp_to_bskl_syn τ) ⊳ Qt }}ad.
Proof.
  intros Θ Δ Q Qt Hr Hwf; induction Hr; intros α10 τ0 HeqS Hb;
    try discriminate HeqS.
  -
    inversion HeqS; subst.
    eapply ad_refine_syn__flex_r; [ exact Hb | ].
    apply ad_refine_syn_mono_refl.
    eapply a_wf_aenv_binds_def_mono; eauto.
  -
    inversion HeqS; subst.
    pose proof (binds_unique _ _ _ _ _ H Hb (a_wf_aenv_uniq Hwf)) as Heqd.
    inversion Heqd; subst.
    exact Hr.
  -
    eapply ad_refine_syn__flex_r; [ eassumption | ].
    eapply IHHr; eauto.
Qed.

Lemma ad_refine_syn_arrow_source_transport : forall Θ Δ Q Qt,
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ Qt }}ad ->
  forall Q1 Q2 Q1' Q2',
  Q = bskl_arrow Q1 Q2 ->
  (forall Qt', {{ Θ ⨟ Δ ⊢ᵣ Q1 ⊳ Qt' }}ad ->
               {{ Θ ⨟ Δ ⊢ᵣ Q1' ⊳ Qt' }}ad) ->
  (forall Qt', {{ Θ ⨟ Δ ⊢ᵣ Q2 ⊳ Qt' }}ad ->
               {{ Θ ⨟ Δ ⊢ᵣ Q2' ⊳ Qt' }}ad) ->
  {{ Θ ⨟ Δ ⊢ᵣ (bskl_arrow Q1' Q2') ⊳ Qt }}ad.
Proof.
  intros Θ Δ Q Qt Hr; induction Hr; intros S1' S2' Q1' Q2' HeqS Htr1 Htr2;
    try discriminate HeqS.
  -
    inversion HeqS; subst.
    apply ad_refine_syn_arrow_intro; [ apply Htr1 | apply Htr2 ]; assumption.
  -
    eapply ad_refine_syn__flex_r; [ eassumption | ].
    eapply IHHr; eauto.
Qed.

Lemma ad_refine_syn_forall_source_transport : forall Θ Δ Q Qt,
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ Qt }}ad ->
  forall Q0 Q0' L0,
  Q = bskl_all_inh Q0 ->
  (forall α, α `notin` L0 -> forall Δ' Qt',
     {{ ((α ~ abind_tvar) ++ Θ) ⨟ Δ' ⊢ᵣ (open_bskl_wrt_bskl Q0 (bskl_var_f α)) ⊳ Qt' }}ad ->
     {{ ((α ~ abind_tvar) ++ Θ) ⨟ Δ' ⊢ᵣ (open_bskl_wrt_bskl Q0' (bskl_var_f α)) ⊳ Qt' }}ad) ->
  {{ Θ ⨟ Δ ⊢ᵣ (bskl_all_inh Q0') ⊳ Qt }}ad.
Proof.
  intros Θ Δ Q Qt Hr; induction Hr; intros Q0 Q0' L0 HeqS Htr;
    try discriminate HeqS.
  -
    inversion HeqS; subst.
    apply ad_refine_syn_all_intro with (L := L `union` L0).
    intros α Hα.
    apply Htr; [ clear - Hα; fsetdec | ].
    apply H0; clear - Hα; fsetdec.
  -
    eapply ad_refine_syn__flex_r; [ eassumption | ].
    eapply IHHr; eauto.
Qed.

Lemma ad_refine_syn_univ_ghost_source_transport : forall Θ Δ Q Qt,
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ Qt }}ad ->
  {{ ⊢ Θ }}a ->
  forall Q0 Q0',
  Q = bskl_univ_ghost Q0 ->
  (forall Θ' Qt',
     {{ ⊢ Θ' }}a ->
     (forall x b, binds x b Θ -> binds x b Θ') ->
     {{ Θ' ⨟ Δ ⊢ᵣ Q0 ⊳ Qt' }}ad ->
     {{ Θ' ⨟ Δ ⊢ᵣ Q0' ⊳ Qt' }}ad) ->
  {{ Θ ⨟ Δ ⊢ᵣ (bskl_univ_ghost Q0') ⊳ Qt }}ad.
Proof.
  intros Θ Δ Q Qt Hr; induction Hr; intros HwfΘ Q0 Q0' HeqS Htr;
    try discriminate HeqS.
  -
    inversion HeqS; subst.
    apply ad_refine_syn_univ_ghost_remove_intro.
    apply (Htr Θ); [ exact HwfΘ | intros x b Hb; exact Hb | exact Hr ].
  -
    inversion HeqS; subst.
    apply ad_refine_syn_univ_ghost_fill_intro with (L := L `union` dom Θ).
    intros α Hα.
    assert (HwfX : {{ ⊢ ((α ~ abind_tvar) ++ Θ) }}a)
      by (apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact HwfΘ ]).
    apply (H1 α ltac:(clear - Hα; solve_notin_auto) HwfX Q0 Q0' eq_refl).
    intros Θ' Qt' Hwf' Hincl' Hr'.
    apply (Htr Θ' Qt' Hwf'); [ | exact Hr' ].
    intros x b Hb. apply Hincl'. apply binds_cons_3. exact Hb.
  -
    inversion HeqS; subst.
    apply ad_refine_syn_univ_ghost_keep_intro.
    apply (Htr Θ); [ exact HwfΘ | intros x b Hb; exact Hb | exact Hr ].
  -
    eapply ad_refine_syn__flex_r; [ eassumption | ].
    eapply IHHr; eauto.
Qed.

Lemma skl_tyequiv_refine_syn_transport : forall Θ P P',
  {{ Θ ⊢ P ≡ˢ P' }}a ->
  forall Θ',
  {{ ⊢ Θ' }}a ->
  (forall x b, binds x b Θ -> binds x b Θ') ->
  (forall Δ Qt,
     {{ Θ' ⨟ Δ ⊢ᵣ (pskl_to_bskl_inh P) ⊳ Qt }}ad ->
     {{ Θ' ⨟ Δ ⊢ᵣ (pskl_to_bskl_inh P') ⊳ Qt }}ad) /\
  (forall Δ Qt,
     {{ Θ' ⨟ Δ ⊢ᵣ (pskl_to_bskl_inh P') ⊳ Qt }}ad ->
     {{ Θ' ⨟ Δ ⊢ᵣ (pskl_to_bskl_inh P) ⊳ Qt }}ad).
Proof.
  intros Θ P P' Heq; induction Heq; intros Θ' Hwf' Hincl.
  -  split; intros Δ Qt Hr; exact Hr.
  -
    destruct (IHHeq Θ' Hwf' Hincl) as [Hd1 Hd2].
    split; [ exact Hd2 | exact Hd1 ].
  -
    destruct (IHHeq1 Θ' Hwf' Hincl) as [H1l H1r].
    destruct (IHHeq2 Θ' Hwf' Hincl) as [H2l H2r].
    split; intros Δ Qt Hr;
      [ apply H2l, H1l, Hr | apply H1r, H2r, Hr ].
  -
    assert (HbΘ' : binds α (abind_flex_mono_def τ) Θ')
      by (apply Hincl; exact H).
    assert (Hmτ : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf' | exact HbΘ' ]).
    split; intros Δ Qt Hr.
    +
      rewrite (ptyp_to_bskl_inh_syn_eq Hmτ).
      eapply ad_refine_syn_unfold_def_source;
        [ exact Hr | exact Hwf' | reflexivity | exact HbΘ' ].
    +
      simpl.
      eapply ad_refine_syn__flex_l; [ exact HbΘ' | ].
      rewrite (ptyp_to_bskl_inh_syn_eq Hmτ) in Hr. exact Hr.
  -
    destruct (IHHeq1 Θ' Hwf' Hincl) as [H1l H1r].
    destruct (IHHeq2 Θ' Hwf' Hincl) as [H2l H2r].
    split; intros Δ Qt Hr; simpl in Hr |- *.
    + eapply ad_refine_syn_arrow_source_transport;
        [ exact Hr | reflexivity | apply H1l | apply H2l ].
    + eapply ad_refine_syn_arrow_source_transport;
        [ exact Hr | reflexivity | apply H1r | apply H2r ].
  -
    split; intros Δ Qt Hr; simpl in Hr |- *.
    + eapply ad_refine_syn_forall_source_transport with (L0 := L `union` dom Θ');
        [ exact Hr | reflexivity | ].
      intros α Hα Δ' Qt' Hr'.
      destruct (H0 α ltac:(clear - Hα; solve_notin_auto)
                  ((α ~ abind_tvar) ++ Θ')
                  ltac:(apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf' ])
                  (fun x b Hb => binds_cons_3 _ _ _ _ _ _ (Hincl x b Hb)))
        as [Hl _].
      rewrite <- pskl_to_bskl_inh_open in Hr'.
      rewrite <- pskl_to_bskl_inh_open.
      apply Hl. exact Hr'.
    + eapply ad_refine_syn_forall_source_transport with (L0 := L `union` dom Θ');
        [ exact Hr | reflexivity | ].
      intros α Hα Δ' Qt' Hr'.
      destruct (H0 α ltac:(clear - Hα; solve_notin_auto)
                  ((α ~ abind_tvar) ++ Θ')
                  ltac:(apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf' ])
                  (fun x b Hb => binds_cons_3 _ _ _ _ _ _ (Hincl x b Hb)))
        as [_ Hrr].
      rewrite <- pskl_to_bskl_inh_open in Hr'.
      rewrite <- pskl_to_bskl_inh_open.
      apply Hrr. exact Hr'.
  -
    split; intros Δ Qt Hr; simpl in Hr |- *.
    + eapply ad_refine_syn_univ_ghost_source_transport;
        [ exact Hr | exact Hwf' | reflexivity | ].
      intros Θ'' Qt' Hwf'' Hincl' Hr'.
      destruct (IHHeq Θ'' Hwf''
                  (fun x b Hb => Hincl' x b (Hincl x b Hb))) as [Hl _].
      apply Hl. exact Hr'.
    + eapply ad_refine_syn_univ_ghost_source_transport;
        [ exact Hr | exact Hwf' | reflexivity | ].
      intros Θ'' Qt' Hwf'' Hincl' Hr'.
      destruct (IHHeq Θ'' Hwf''
                  (fun x b Hb => Hincl' x b (Hincl x b Hb))) as [_ Hrr].
      apply Hrr. exact Hr'.
Qed.

Lemma ad_refine_pskl_unfold_def_source : forall Θ Δ P Pt,
  {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ Pt }}ad ->
  {{ ⊢ Θ }}a ->
  forall α1 τ, P = pskl_var_f α1 ->
  binds α1 (abind_flex_mono_def τ) Θ ->
  {{ Θ ⨟ Δ ⊢ᵣₚ (ptyp_to_pskl τ) ⊳ Pt }}ad.
Proof.
  intros Θ Δ P Pt Hr Hwf; induction Hr; intros α10 τ0 HeqS Hb;
    try discriminate HeqS.
  -
    inversion HeqS; subst.
    eapply ad_refine_pskl__flex_r; [ exact Hb | ].
    apply ad_refine_pskl_mono_refl;
      [ eapply a_wf_aenv_binds_def_mono; eauto
      | eapply a_wf_aenv_binds_def_wf; eauto ].
  -
    inversion HeqS; subst.
    pose proof (binds_unique _ _ _ _ _ H Hb (a_wf_aenv_uniq Hwf)) as Heqd.
    inversion Heqd; subst.
    exact Hr.
  -
    eapply ad_refine_pskl__flex_r; [ eassumption | ].
    eapply IHHr; eauto.
Qed.

Lemma ad_refine_pskl_arrow_source_transport : forall Θ Δ P Pt,
  {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ Pt }}ad ->
  forall P1 P2 P1' P2',
  P = pskl_arrow P1 P2 ->
  (forall Qt', {{ Θ ⨟ Δ ⊢ᵣₚ P1 ⊳ Qt' }}ad ->
               {{ Θ ⨟ Δ ⊢ᵣₚ P1' ⊳ Qt' }}ad) ->
  (forall Qt', {{ Θ ⨟ Δ ⊢ᵣₚ P2 ⊳ Qt' }}ad ->
               {{ Θ ⨟ Δ ⊢ᵣₚ P2' ⊳ Qt' }}ad) ->
  {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_arrow P1' P2') ⊳ Pt }}ad.
Proof.
  intros Θ Δ P Pt Hr; induction Hr; intros S1' S2' P1' P2' HeqS Htr1 Htr2;
    try discriminate HeqS.
  -
    inversion HeqS; subst.
    apply ad_refine_pskl__arrow; [ apply Htr1 | apply Htr2 ]; assumption.
  -
    eapply ad_refine_pskl__flex_r; [ eassumption | ].
    eapply IHHr; eauto.
Qed.

Lemma ad_refine_pskl_forall_source_transport : forall Θ Δ P Pt,
  {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ Pt }}ad ->
  forall P0 P0' L0,
  P = pskl_all_syn P0 ->
  (forall α, α `notin` L0 -> forall Δ' Pt',
     {{ ((α ~ abind_tvar) ++ Θ) ⨟ Δ' ⊢ᵣₚ (open_pskl_wrt_pskl P0 (pskl_var_f α)) ⊳ Pt' }}ad ->
     {{ ((α ~ abind_tvar) ++ Θ) ⨟ Δ' ⊢ᵣₚ (open_pskl_wrt_pskl P0' (pskl_var_f α)) ⊳ Pt' }}ad) ->
  {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_all_syn P0') ⊳ Pt }}ad.
Proof.
  intros Θ Δ P Pt Hr; induction Hr; intros P0 P0' L0 HeqS Htr;
    try discriminate HeqS.
  -
    inversion HeqS; subst.
    apply ad_refine_pskl__all with (L := L `union` L0).
    intros α Hα.
    apply Htr; [ clear - Hα; fsetdec | ].
    apply H; clear - Hα; fsetdec.
  -
    eapply ad_refine_pskl__flex_r; [ eassumption | ].
    eapply IHHr; eauto.
Qed.

Lemma ad_refine_pskl_univ_ghost_source_transport : forall Θ Δ P Pt,
  {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ Pt }}ad ->
  {{ ⊢ Θ }}a ->
  forall P0 P0',
  P = pskl_univ_ghost P0 ->
  (forall Θ' Pt',
     {{ ⊢ Θ' }}a ->
     (forall x b, binds x b Θ -> binds x b Θ') ->
     {{ Θ' ⨟ Δ ⊢ᵣₚ P0 ⊳ Pt' }}ad ->
     {{ Θ' ⨟ Δ ⊢ᵣₚ P0' ⊳ Pt' }}ad) ->
  {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_univ_ghost P0') ⊳ Pt }}ad.
Proof.
  intros Θ Δ P Pt Hr; induction Hr; intros HwfΘ P0 P0' HeqS Htr;
    try discriminate HeqS.
  -
    inversion HeqS; subst.
    apply ad_refine_pskl__univ_ghost_remove.
    apply (Htr Θ); [ exact HwfΘ | intros x b Hb; exact Hb | exact Hr ].
  -
    inversion HeqS; subst.
    apply ad_refine_pskl__univ_ghost_fill with (L := L `union` dom Θ).
    intros α Hα.
    assert (HwfX : {{ ⊢ ((α ~ abind_tvar) ++ Θ) }}a)
      by (apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact HwfΘ ]).
    apply (H0 α ltac:(clear - Hα; solve_notin_auto) HwfX P0 P0' eq_refl).
    intros Θ' Pt' Hwf' Hincl' Hr'.
    apply (Htr Θ' Pt' Hwf'); [ | exact Hr' ].
    intros x b Hb. apply Hincl'. apply binds_cons_3. exact Hb.
  -
    inversion HeqS; subst.
    apply ad_refine_pskl__univ_ghost_keep.
    apply (Htr Θ); [ exact HwfΘ | intros x b Hb; exact Hb | exact Hr ].
  -
    eapply ad_refine_pskl__flex_r; [ eassumption | ].
    eapply IHHr; eauto.
Qed.

Lemma skl_tyequiv_refine_pskl_transport : forall Θ P P',
  {{ Θ ⊢ P ≡ˢ P' }}a ->
  forall Θ',
  {{ ⊢ Θ' }}a ->
  (forall x b, binds x b Θ -> binds x b Θ') ->
  (forall Δ Pt,
     {{ Θ' ⨟ Δ ⊢ᵣₚ P ⊳ Pt }}ad ->
     {{ Θ' ⨟ Δ ⊢ᵣₚ P' ⊳ Pt }}ad) /\
  (forall Δ Pt,
     {{ Θ' ⨟ Δ ⊢ᵣₚ P' ⊳ Pt }}ad ->
     {{ Θ' ⨟ Δ ⊢ᵣₚ P ⊳ Pt }}ad).
Proof.
  intros Θ P P' Heq; induction Heq; intros Θ' Hwf' Hincl.
  -  split; intros Δ Pt Hr; exact Hr.
  -
    destruct (IHHeq Θ' Hwf' Hincl) as [Hd1 Hd2].
    split; [ exact Hd2 | exact Hd1 ].
  -
    destruct (IHHeq1 Θ' Hwf' Hincl) as [H1l H1r].
    destruct (IHHeq2 Θ' Hwf' Hincl) as [H2l H2r].
    split; intros Δ Pt Hr;
      [ apply H2l, H1l, Hr | apply H1r, H2r, Hr ].
  -
    assert (HbΘ' : binds α (abind_flex_mono_def τ) Θ')
      by (apply Hincl; exact H).
    split; intros Δ Pt Hr.
    + eapply ad_refine_pskl_unfold_def_source;
        [ exact Hr | exact Hwf' | reflexivity | exact HbΘ' ].
    + eapply ad_refine_pskl__flex_l; [ exact HbΘ' | exact Hr ].
  -
    destruct (IHHeq1 Θ' Hwf' Hincl) as [H1l H1r].
    destruct (IHHeq2 Θ' Hwf' Hincl) as [H2l H2r].
    split; intros Δ Pt Hr.
    + eapply ad_refine_pskl_arrow_source_transport;
        [ exact Hr | reflexivity | apply H1l | apply H2l ].
    + eapply ad_refine_pskl_arrow_source_transport;
        [ exact Hr | reflexivity | apply H1r | apply H2r ].
  -
    split; intros Δ Pt Hr.
    + eapply ad_refine_pskl_forall_source_transport with (L0 := L `union` dom Θ');
        [ exact Hr | reflexivity | ].
      intros α Hα Δ' Qt' Hr'.
      destruct (H0 α ltac:(clear - Hα; solve_notin_auto)
                  ((α ~ abind_tvar) ++ Θ')
                  ltac:(apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf' ])
                  (fun x b Hb => binds_cons_3 _ _ _ _ _ _ (Hincl x b Hb)))
        as [Hl _].
      apply Hl. exact Hr'.
    + eapply ad_refine_pskl_forall_source_transport with (L0 := L `union` dom Θ');
        [ exact Hr | reflexivity | ].
      intros α Hα Δ' Qt' Hr'.
      destruct (H0 α ltac:(clear - Hα; solve_notin_auto)
                  ((α ~ abind_tvar) ++ Θ')
                  ltac:(apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf' ])
                  (fun x b Hb => binds_cons_3 _ _ _ _ _ _ (Hincl x b Hb)))
        as [_ Hrr].
      apply Hrr. exact Hr'.
  -
    split; intros Δ Pt Hr.
    + eapply ad_refine_pskl_univ_ghost_source_transport;
        [ exact Hr | exact Hwf' | reflexivity | ].
      intros Θ'' Qt' Hwf'' Hincl' Hr'.
      destruct (IHHeq Θ'' Hwf''
                  (fun x b Hb => Hincl' x b (Hincl x b Hb))) as [Hl _].
      apply Hl. exact Hr'.
    + eapply ad_refine_pskl_univ_ghost_source_transport;
        [ exact Hr | exact Hwf' | reflexivity | ].
      intros Θ'' Qt' Hwf'' Hincl' Hr'.
      destruct (IHHeq Θ'' Hwf''
                  (fun x b Hb => Hincl' x b (Hincl x b Hb))) as [_ Hrr].
      apply Hrr. exact Hr'.
Qed.

Lemma ad_refine_syn_all_inh_guarded_absurd : forall Θ Δ Q Q',
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δ ⊢ᵣ (bskl_all_inh Q) ⊳ Q' }}ad ->
  guarded_bskl Q' ->
  False.
Proof.
  intros Θ Δ Q Q' Hwf Hr.
  remember (bskl_all_inh Q) as R eqn:HeqS.
  induction Hr; intros Hg; try discriminate HeqS.
  -
    inversion Hg.
  -
    apply IHHr; [ exact Hwf | exact HeqS | ].
    apply mono_bskl_guarded, mono_ptyp_to_bskl_syn.
    eapply a_wf_aenv_binds_def_mono; eauto.
Qed.

Lemma ad_refine_syn_flex_target_unfold : forall Θ Δ Q α τ,
  {{ ⊢ Θ }}a ->
  binds α (abind_flex_mono_def τ) Θ ->
  (forall α0, α0 `in` Δ -> binds α0 abind_tvar Θ) ->
  Δ ∩ ftvar_in_ptyp τ [=] empty ->
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ (bskl_var_f α) }}ad ->
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ (ptyp_to_bskl_syn τ) }}ad.
Proof.
  intros Θ Δ Q α τ Hwf Hbα HΔ HdisjΔ Hr.
  assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
  assert (Hwfτ : a_wf_ptyp Θ τ) by (eapply a_wf_aenv_binds_def_wf; eauto).
  remember (bskl_var_f α) as T eqn:HeqT.
  induction Hr; try discriminate HeqT.
  -
    inversion HeqT; subst α0.
    eapply ad_refine_syn__flex_l; [ exact Hbα | ].
    apply ad_refine_syn_mono_refl; assumption.
  -
    destruct P as [ | n | β1 | | | | ]; simpl in HeqT; try discriminate.
    inversion HeqT; subst β1.
    replace (ptyp_to_bskl_syn τ)
      with (pskl_to_bskl_syn (ptyp_to_pskl τ)) by reflexivity.
    apply ad_refine_syn__ghost.
    rewrite ftvar_ptyp_to_pskl. exact HdisjΔ.
  -
    apply ad_refine_syn_univ_ghost_remove_intro.
    apply IHHr; assumption.
  -
    eapply ad_refine_syn__flex_l; [ exact H | ].
    apply IHHr; assumption.
  -
    inversion HeqT; subst α0.
    pose proof (binds_unique _ _ _ _ _ H Hbα (a_wf_aenv_uniq Hwf)) as Heq.
    inversion Heq; subst τ0.
    exact Hr.
Qed.

Lemma ad_refine_pskl_flex_target_unfold : forall Θ Δ P α τ,
  {{ ⊢ Θ }}a ->
  binds α (abind_flex_mono_def τ) Θ ->
  (forall α0, α0 `in` Δ -> binds α0 abind_tvar Θ) ->
  Δ ∩ ftvar_in_ptyp τ [=] empty ->
  {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ (pskl_var_f α) }}ad ->
  {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ (ptyp_to_pskl τ) }}ad.
Proof.
  intros Θ Δ P α τ Hwf Hbα HΔ HdisjΔ Hr.
  assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
  assert (Hwfτ : a_wf_ptyp Θ τ) by (eapply a_wf_aenv_binds_def_wf; eauto).
  remember (pskl_var_f α) as T eqn:HeqT.
  induction Hr; try discriminate HeqT.
  -
    inversion HeqT; subst α0.
    eapply ad_refine_pskl__flex_l; [ exact Hbα | ].
    apply ad_refine_pskl_mono_refl; assumption.
  -
    inversion HeqT; subst P'.
    apply ad_refine_pskl__ghost.
    rewrite ftvar_ptyp_to_pskl. exact HdisjΔ.
  -
    apply ad_refine_pskl__univ_ghost_remove.
    apply IHHr; assumption.
  -
    eapply ad_refine_pskl__flex_l; [ exact H | ].
    apply IHHr; assumption.
  -
    inversion HeqT; subst α0.
    pose proof (binds_unique _ _ _ _ _ H Hbα (a_wf_aenv_uniq Hwf)) as Heq.
    inversion Heq; subst τ0.
    exact Hr.
Qed.
