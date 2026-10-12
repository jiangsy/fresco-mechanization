Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.prop_tag.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_ln.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.decl.prop_skeleton.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo_decl.def_subtyping.
Require Import src.fresco.algo.consistency.prop_soundness_consis.
Require Import src.fresco.algo_decl.prop_refinement.
Require Import src.fresco.algo_decl.prop_stability.
Require Import src.fresco.algo_decl.prop_subtyping.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo.subtyping.prop_looksub.
Require Import src.fresco.algo.subtyping.prop_soundness_subtag.

Set Implicit Arguments.

Lemma a_solvetag_split : forall C1 C2 ψ Ψ,
  {{ (C1 ++ C2) ⊩ ψ ⤳ Ψ }}da ->
  exists Ψ1 Ψ2,
    {{ C1 ⊩ ψ ⤳ Ψ1 }}da /\ {{ C2 ⊩ ψ ⤳ Ψ2 }}da /\ Ψ [=] Ψ1 `union` Ψ2.
Proof.
  induction C1 as [ | c C1' IH ]; intros C2 ψ Ψ Hs; simpl in Hs.
  - exists empty, Ψ. repeat apply conj;
      [ apply a_solvetag__empty; fsetdec | exact Hs | fsetdec ].
  - destruct c as [ M Q | Q ].
    +
      inversion Hs as [ | M0 Q0 ψ0 Ψ0 Hsub Hnil | ]; subst.
      symmetry in H0. apply app_eq_nil in H0. destruct H0 as [-> ->].
      exists Ψ, empty. repeat apply conj;
        [ apply a_solvetag__sub; exact Hsub
        | apply a_solvetag__empty; fsetdec | fsetdec ].
    +
      inversion Hs as [ | | Q0 C0 ψ0 Ψall Ψa Ψb Heqp Hrest HΨ ]; subst.
      destruct (IH C2 ψ Ψb Hrest) as [Ψ1 [Ψ2 [Hs1 [Hs2 HΨe]]]].
      exists (Ψa `union` Ψ1), Ψ2. repeat apply conj.
      * eapply a_solvetag__eq; [ exact Heqp | exact Hs1 | fsetdec ].
      * exact Hs2.
      * clear - HΨ HΨe. fsetdec.
Qed.

Scheme a_solvetag_sub_mut := Induction for a_solvetag_sub Sort Prop
  with a_solvetag_eq_mut := Induction for a_solvetag_eq Sort Prop.
Combined Scheme a_solvetag_sub_eq_mutind
  from a_solvetag_sub_mut, a_solvetag_eq_mut.

Lemma a_solvetag_sub_eq_psi_cong :
  (forall ψ M P Ψ, {{ ψ ≼[ M ] P ⤳ Ψ }}da ->
     forall Ψ', Ψ [=] Ψ' -> {{ ψ ≼[ M ] P ⤳ Ψ' }}da) /\
  (forall ψ P Ψ, {{ ψ ∼ P ⤳ Ψ }}da ->
     forall Ψ', Ψ [=] Ψ' -> {{ ψ ∼ P ⤳ Ψ' }}da).
Proof.
  apply a_solvetag_sub_eq_mutind;
    intros; try (econstructor; eauto; fsetdec).
Qed.

Lemma a_solvetag_psi_cong : forall 𝒞 ψ Ψ Ψ',
  {{ 𝒞 ⊩ ψ ⤳ Ψ }}da -> Ψ [=] Ψ' -> {{ 𝒞 ⊩ ψ ⤳ Ψ' }}da.
Proof.
  intros 𝒞 ψ Ψ Ψ' Hs; revert Ψ'; induction Hs; intros Ψ' Heq.
  - apply a_solvetag__empty. fsetdec.
  - apply a_solvetag__sub. eapply (proj1 a_solvetag_sub_eq_psi_cong); eauto.
  - eapply a_solvetag__eq; [ exact H | exact Hs | clear - Heq H0; fsetdec ].
Qed.

Fixpoint msubst_uskl (ρ : list (atom * uskl)) (T : uskl) : uskl :=
  match ρ with
  | nil => T
  | (β, ψg) :: ρ' => subst_uskl_in_uskl ψg β (msubst_uskl ρ' T)
  end.

Lemma uskl_to_pskl_msubst_strip : forall ρ ψ,
  ⌊ msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψ)) ⌋ˢ = ⌊ msubst_uskl ρ ψ ⌋ˢ.
Proof.
  induction ρ as [ | [β ψg] ρ' IH ]; intros ψ; simpl;
    [ apply uskl_to_pskl_pskl_to_uskl | ].
  rewrite ! uskl_to_pskl_subst, IH. reflexivity.
Qed.

Definition rsubst_lc (ρ : list (atom * uskl)) : Prop :=
  forall β ψg, binds β ψg ρ -> lc_uskl ψg.

Lemma msubst_uskl_open_comm : forall ρ R α,
  rsubst_lc ρ ->
  α `notin` dom ρ ->
  (forall β ψg, binds β ψg ρ -> α `notin` ftvar_in_uskl ψg) ->
  msubst_uskl ρ (open_uskl_wrt_uskl R (uskl_var_f α))
  = open_uskl_wrt_uskl (msubst_uskl ρ R) (uskl_var_f α).
Proof.
  induction ρ as [ | [α1 ψg] ρ' IH ]; intros R α Hlc Hdom Hftv;
    simpl; [ reflexivity | ].
  assert (Hlcγ : lc_uskl ψg)
    by (eapply Hlc; unfold binds; simpl; left; reflexivity).
  assert (Hlc' : rsubst_lc ρ')
    by (intros b p Hb; eapply Hlc; unfold binds; simpl; right; exact Hb).
  assert (Hdom' : α `notin` dom ρ')
    by (simpl in Hdom; clear - Hdom; fsetdec).
  assert (Hftv' : forall b p, binds b p ρ' -> α `notin` ftvar_in_uskl p)
    by (intros b p Hb; eapply Hftv; unfold binds; simpl; right; exact Hb).
  rewrite (IH R α Hlc' Hdom' Hftv').
  rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl; [ | exact Hlcγ ].
  f_equal.
  assert (Hαγ : α <> α1) by (simpl in Hdom; clear - Hdom; fsetdec).
  assert (HXf : α `notin` ftvar_in_uskl ψg)
    by (eapply Hftv; unfold binds; simpl; left; reflexivity).
  simpl.
  destruct_if as [-> | _];
    [ contradiction | reflexivity ].
Qed.

Local Ltac vacuous_forall_l_extract H1 :=
  intros α Hα;
  match goal with
  | Hb : ⌊ ?T2b ⌋ˢ = ⌊ ?Rb ⌋ˢ
    |- a_extract _ _ _ _ ⌊ open_uskl_wrt_uskl ?T2b _ ⌋ˢ _ _ _ =>
      replace (⌊ open_uskl_wrt_uskl T2b (uskl_var_f α) ⌋ˢ)
        with (⌊ open_uskl_wrt_uskl Rb (uskl_var_f α) ⌋ˢ)
        by (rewrite ! uskl_to_pskl_open; rewrite Hb; reflexivity)
  end;
  apply H1; exact Hα.

Local Ltac vacuous_forall_l_family :=
  intros Ψg ψg Hfr Hsort Hera;
  match goal with
  | IHfam : forall (a : atoms) (b : uskl), _ |- _ =>
      eapply (IHfam Ψg ψg Hfr Hsort Hera eq_refl)
  end;
  [ apply lc_body_uskl_wrt_uskl;
      [ eauto using lc_body_uskl_all_syn_1, lc_body_uskl_all_tag_2
      | apply is_dskl_lc; inversion Hsort; assumption ]
  | rewrite ! uskl_to_pskl_open_gen;
    match goal with Hb : ⌊ _ ⌋ˢ = ⌊ _ ⌋ˢ |- _ => rewrite Hb end;
    reflexivity ].

Local Ltac vacuous_forall_l R2' Herase L Ξ P1 H H1 H2 H3 :=
  (destruct R2'; simpl in Herase; inversion Herase; subst;
    match goal with Hl : lc_uskl _ |- _ => inversion Hl; subst end);
  [> eapply a_subtag__forall_l_untagged with (L := L) (Ξ := Ξ) (P1 := P1);
       [ exact H | right; reflexivity | vacuous_forall_l_extract H1
       | exact H2 | exact H3 | vacuous_forall_l_family ]
  |  eapply a_subtag__forall_l_tagged with (L := L) (Ξ := Ξ) (P1 := P1);
       [ exact H | right; reflexivity | vacuous_forall_l_extract H1
       | exact H2 | exact H3 | vacuous_forall_l_family ] ].

Lemma a_subtag_vacuous_erasure : forall NM M P0 Ψ Θ0 R1' P Θ1,
  {{ Θ0 ⊢[ NM | M | P0 | Ψ ] R1' ⩽ P ⊣ Θ1 }}da ->
  P0 = pskl_ghost ->
  forall R2', lc_uskl R2' -> ⌊ R2' ⌋ˢ = ⌊ R1' ⌋ˢ ->
  {{ Θ0 ⊢[ NM | M | P0 | Ψ ] R2' ⩽ P ⊣ Θ1 }}da.
Proof.
  intros NM M P0 Ψ Θ0 R1' P Θ1 H.
  induction H; intros HP0 R2' HlcT2 Herase; subst; try discriminate HP0.
  -
    rewrite <- Herase. apply a_subtag__infer; assumption.
  -
    inv_guarded_ghost.
  -

    assert (HgT2 : guarded_uskl R2').
    { inversion H; subst; simpl in Herase;
        destruct R2'; simpl in Herase; inversion Herase; subst;
        inversion HlcT2; subst; constructor; assumption. }
    rewrite <- Herase. apply a_subtag__univ_ghost_r; assumption.
  -
    vacuous_forall_l R2' Herase L Ξ P1 H H1 H2 H3.
  -
    vacuous_forall_l R2' Herase L Ξ P1 H H1 H2 H3.
  -
    destruct R2'; simpl in Herase; inversion Herase; subst.
    + apply a_subtag__ghost; assumption.
    + apply a_subtag__ghostg; assumption.
  -
    destruct R2'; simpl in Herase; inversion Herase; subst.
    + apply a_subtag__ghost; [ assumption ].
    + apply a_subtag__ghostg; assumption.
  -
    destruct R2'; simpl in Herase; inversion Herase; subst;
      match goal with Hl : lc_uskl _ |- _ => inversion Hl; subst end.
    + apply a_subtag__univ_ghost_l; [ assumption | ].
      eapply IHa_subtag; [ reflexivity | assumption | assumption ].
    + apply a_subtag__univ_ghost_lg; [ assumption | ].
      eapply IHa_subtag; [ reflexivity | assumption | assumption ].
  -
    destruct R2'; simpl in Herase; inversion Herase; subst;
      match goal with Hl : lc_uskl _ |- _ => inversion Hl; subst end.
    + apply a_subtag__univ_ghost_l; [ assumption | ].
      eapply IHa_subtag; [ reflexivity | assumption | assumption ].
    + apply a_subtag__univ_ghost_lg; [ assumption | ].
      eapply IHa_subtag; [ reflexivity | assumption | assumption ].
  -
    destruct R2'; simpl in Herase; inversion Herase; subst.
    apply a_subtag__flex_mono; assumption.
Qed.

Lemma a_consistag_psi_cong : forall Δ1 Δ2 P0 Ψ Θ0 R P Θ1,
  {{ Θ0 ⊢[ Δ1 | Δ2 | P0 | Ψ ] R ∼ P ⊣ Θ1 }}da ->
  forall Ψ', Ψ [=] Ψ' ->
  {{ Θ0 ⊢[ Δ1 | Δ2 | P0 | Ψ' ] R ∼ P ⊣ Θ1 }}da.
Proof.
  intros Δ1 Δ2 P0 Ψ Θ0 R P Θ1 H; induction H; intros Ψ' Heq; econstructor;
    solve
      [ eassumption
      | (match goal with
         | IH : forall Ψ0 : atoms, _ [=] Ψ0 -> _ |- _ =>
             eapply IH; eassumption
         end)
      | (intros;
         match goal with
         | IH : forall α : atom, α `notin` _ ->
                  forall Ψ0, _ [=] Ψ0 -> _ |- _ =>
             eapply IH; [ eassumption | eassumption ]
         end)
      | fsetdec ].
Qed.

Definition msubst_ftv (ρ : list (atom * uskl)) : atoms :=
  fold_right (fun p acc => ftvar_in_uskl (snd p) `union` acc) empty ρ.

Lemma msubst_ftv_binds : forall ρ β ψg,
  binds β ψg ρ -> ftvar_in_uskl ψg [<=] msubst_ftv ρ.
Proof.
  induction ρ as [ | [α1 g] ρ' IH ]; intros β ψg Hb; simpl in *;
    [ inversion Hb | ].
  destruct Hb as [Heq | Hb].
  - inversion Heq; subst. clear; fsetdec.
  - specialize (IH _ _ Hb). clear - IH; fsetdec.
Qed.

Lemma msubst_uskl_arrow : forall ρ R R',
  msubst_uskl ρ (uskl_arrow R R')
  = uskl_arrow (msubst_uskl ρ R) (msubst_uskl ρ R').
Proof. induction ρ as [|[α1 g] ρ' IH]; intros; simpl; [reflexivity|]; rewrite IH; reflexivity. Qed.

Lemma msubst_uskl_univ_ghost : forall ρ R,
  msubst_uskl ρ (uskl_univ_ghost R) = uskl_univ_ghost (msubst_uskl ρ R).
Proof. induction ρ as [|[α1 g] ρ' IH]; intros; simpl; [reflexivity|]; rewrite IH; reflexivity. Qed.

Lemma msubst_uskl_dot_univ_ghost : forall ρ R,
  msubst_uskl ρ (uskl_dot_univ_ghost R) = uskl_dot_univ_ghost (msubst_uskl ρ R).
Proof. induction ρ as [|[α1 g] ρ' IH]; intros; simpl; [reflexivity|]; rewrite IH; reflexivity. Qed.

Lemma msubst_uskl_all_syn : forall ρ R,
  msubst_uskl ρ (uskl_all_syn R) = uskl_all_syn (msubst_uskl ρ R).
Proof. induction ρ as [|[α1 g] ρ' IH]; intros; simpl; [reflexivity|]; rewrite IH; reflexivity. Qed.

Lemma msubst_uskl_all_tag : forall ρ ε R,
  msubst_uskl ρ (uskl_all_tag ε R) = uskl_all_tag ε (msubst_uskl ρ R).
Proof. induction ρ as [|[α1 g] ρ' IH]; intros; simpl; [reflexivity|]; rewrite IH; reflexivity. Qed.

Lemma msubst_uskl_lc : forall ρ R,
  rsubst_lc ρ -> lc_uskl R -> lc_uskl (msubst_uskl ρ R).
Proof.
  induction ρ as [ | [β ψg] ρ' IH ]; intros R Hlc HT; simpl; [ exact HT | ].
  apply subst_uskl_in_uskl_lc_uskl.
  - apply IH; [ | exact HT ].
    intros b p Hb; eapply Hlc; unfold binds; simpl; right; exact Hb.
  - eapply Hlc; unfold binds; simpl; left; reflexivity.
Qed.

Lemma a_solvetag_eq_atom_empty : forall ψ P0 Ψ,
  {{ ψ ∼ P0 ⤳ Ψ }}da ->
  (ψ = uskl_unit \/ exists α, ψ = uskl_var_f α) ->
  Ψ [=] empty.
Proof.
  intros ψ P0 Ψ H; induction H; intros Hshape;
    try (destruct Hshape as [Hd | [α0 Hd]]; discriminate Hd);
    try assumption.
  -
    apply IHa_solvetag_eq; exact Hshape.
Qed.

Lemma a_consistag_vacuous_erasure : forall Δ1 Δ2 P0 Ψ Θ0 R1 P Θ1,
  {{ Θ0 ⊢[ Δ1 | Δ2 | P0 | Ψ ] R1 ∼ P ⊣ Θ1 }}da ->
  P0 = pskl_ghost ->
  forall T2, uskl_to_pskl T2 = uskl_to_pskl R1 ->
  {{ Θ0 ⊢[ Δ1 | Δ2 | P0 | Ψ ] T2 ∼ P ⊣ Θ1 }}da.
Proof.
  intros Δ1 Δ2 P0 Ψ Θ0 R1 P Θ1 H;
    induction H; intros HP0 T2 Herase; subst; try discriminate HP0.
  -
    destruct T2; simpl in Herase; inversion Herase; subst;
      [ apply a_consistag__ghost; [ simpl; clear; fsetdec | assumption ]
      | apply a_consistag__ghostg; assumption ].
  -
    destruct T2; simpl in Herase; inversion Herase; subst.
    eapply a_consistag__flex_l; eassumption.
  -
    destruct T2; simpl in Herase; inversion Herase; subst;
      [ apply a_consistag__ghost; [ simpl; clear; fsetdec | assumption ]
      | apply a_consistag__ghostg; assumption ].
  -
    inv_guarded_ghost.
  -
    rewrite <- Herase.
    apply a_consistag__ghost_r; [ rewrite Herase; assumption | assumption ].
Qed.

Inductive no_all_syn_pskl : pskl -> Prop :=
| nas_pskl__unit    : no_all_syn_pskl pskl_unit
| nas_pskl__var_b   : forall n, no_all_syn_pskl (pskl_var_b n)
| nas_pskl__var_f   : forall α, no_all_syn_pskl (pskl_var_f α)
| nas_pskl__arrow   : forall P1 P2,
    no_all_syn_pskl P1 -> no_all_syn_pskl P2 -> no_all_syn_pskl (pskl_arrow P1 P2)
| nas_pskl__ghost    : no_all_syn_pskl pskl_ghost
| nas_pskl__univ_ghost : forall P, no_all_syn_pskl P -> no_all_syn_pskl (pskl_univ_ghost P).

Inductive no_all_syn_uskl : uskl -> Prop :=
| nas_uskl__unit     : no_all_syn_uskl uskl_unit
| nas_uskl__var_b    : forall n, no_all_syn_uskl (uskl_var_b n)
| nas_uskl__var_f    : forall α, no_all_syn_uskl (uskl_var_f α)
| nas_uskl__arrow    : forall R1 R2,
    no_all_syn_uskl R1 -> no_all_syn_uskl R2 -> no_all_syn_uskl (uskl_arrow R1 R2)
| nas_uskl__ghost     : no_all_syn_uskl uskl_ghost
| nas_uskl__dot_ghost    : no_all_syn_uskl uskl_dot_ghost
| nas_uskl__univ_ghost  : forall R, no_all_syn_uskl R -> no_all_syn_uskl (uskl_univ_ghost R)
| nas_uskl__dot_univ_ghost : forall R, no_all_syn_uskl R -> no_all_syn_uskl (uskl_dot_univ_ghost R).

Lemma ad_pat_consis_mono_no_all_syn : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  {{ ⊢ Θ }}a ->
  mono_bskl Q ->
  no_all_syn_uskl R.
Proof.
  intros Ψ Θ R Q H; induction H; intros Hwf Hmono;
    try solve [ inversion Hmono ];
    try solve [ constructor ].
  -
    inversion Hmono; subst.
    constructor; [ apply IHad_pat_consis1 | apply IHad_pat_consis2 ]; auto.
  -
    constructor. apply IHad_pat_consis; auto.
  -
    apply IHad_pat_consis; [ exact Hwf | ].
    apply mono_ptyp_to_bskl_syn.
    eapply a_wf_aenv_binds_def_mono; [ exact Hwf | eassumption ].
Qed.

Lemma msubst_ghostfree_eq_strip : forall ρ ψ,
  uskl_ghost_free ψ ->
  no_all_syn_uskl (msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψ))) ->
  msubst_uskl ρ ψ = msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψ)).
Proof.
  intros ρ ψ H; induction H; intros Hnas.
  -  reflexivity.
  -  reflexivity.
  -
    simpl. rewrite ! msubst_uskl_arrow.
    simpl in Hnas. rewrite msubst_uskl_arrow in Hnas. inversion Hnas; subst.
    erewrite IHuskl_ghost_free1 by eassumption.
    erewrite IHuskl_ghost_free2 by eassumption.
    reflexivity.
  -
    simpl in Hnas. rewrite msubst_uskl_all_syn in Hnas. inversion Hnas.
  -
    simpl in Hnas. rewrite msubst_uskl_all_syn in Hnas. inversion Hnas.
Qed.

Lemma a_consistag_flexvar_subject_no_all_syn : forall Δ1 Δ2 α Ψ Θ0 R P Θ1,
  {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_var_f α) | Ψ ] R ∼ P ⊣ Θ1 }}da ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ (uskl_to_pskl R) }}a ->
  no_all_syn_uskl R.
Proof.
  intros Δ1 Δ2 α Ψ Θ0 R P Θ1 H.
  remember (pskl_var_f α) as P0 eqn:HP0. revert HP0.
  induction H; intros HP0 Hwf HwfS;
    try discriminate HP0; try solve [ constructor ].
  -
    rewrite uskl_to_pskl_pskl_to_uskl in HwfS.
    match goal with
    | Hass : a_assign _ _ _ _ _ |- _ =>
        eapply ad_pat_consis_mono_no_all_syn;
          [ eapply (proj2 (a_assign_sound Hass ltac:(constructor) Hwf HwfS))
          | eapply (a_assign_preserves_wf Hass ltac:(constructor) Hwf HwfS)
          | constructor ]
    end.
  -
    constructor.
    simpl in HwfS. inversion HwfS; subst.
    match goal with H : {{ (aenv_minus _ _) ⨟ _ ⊢ₚₛ _ }}a |- _ =>
      rewrite aenv_minus_empty in H end.
    eapply IHa_consistag;
      [ first [ eassumption | reflexivity ] | exact Hwf | eassumption ].
Qed.

Local Ltac delta_open_goal β Hβ Hrig Δ1 Δ2 :=
  let Θ := lazymatch goal with |- context [ (β ~ abind_tvar) ++ ?Θ ] => Θ end in
  let D := lazymatch goal with
           | |- forall _, _ `in` ?D -> _ => D
           | |- no_flex_dep ?D _ => D
           | |- flex_above_free ?D _ => D
           end in
  let H := fresh "HΔ" in
  pose proof (@delta_inv_open_tvar (Δ1 `union` Δ2) D β Θ
                ltac:(assumption) ltac:(clear - Hβ; fsetdec) ltac:(clear; fsetdec)
                Hrig ltac:(assumption) ltac:(assumption)) as H;
  first [ exact (proj1 H) | exact (proj1 (proj2 H)) | exact (proj2 (proj2 H)) ].

Local Ltac decoration_var_forall_open IH β Hβ ρ ψ Θ0 Hlcρ Hcbody HlcSbody
    HwfP0β HbodyS Hrig Δ1 Δ2 :=
  let Hβρ := fresh "Hβρ" in let Hβf := fresh "Hβf" in
  let HβΘ := fresh "HβΘ" in let Hcβ := fresh "Hcβ" in
  assert (Hβρ : β `notin` dom ρ) by (clear - Hβ; fsetdec);
  assert (Hβf : forall α1 ψg, binds α1 ψg ρ -> β `notin` ftvar_in_uskl ψg)
    by (let α1 := fresh in let ψg := fresh in let Hb := fresh in
        let Hsc := fresh in
        intros α1 ψg Hb; pose proof (msubst_ftv_binds _ _ _ Hb) as Hsc;
        clear - Hβ Hsc; fsetdec);
  assert (HβΘ : β `notin` dom Θ0) by (clear - Hβ; fsetdec);
  rewrite <- (@msubst_uskl_open_comm ρ ψ β Hlcρ Hβρ Hβf);
  eapply (IH β ltac:(clear - Hβ; solve_notin_auto));
    [ exact Hlcρ
    |
      rewrite strip_uskl_open;
      pose proof (Hcbody β ltac:(clear - Hβ; solve_notin_auto)) as Hcβ;
      rewrite <- (@msubst_uskl_open_comm ρ (pskl_to_uskl (uskl_to_pskl ψ)) β
                    Hlcρ Hβρ Hβf) in Hcβ;
      exact Hcβ
    | apply a_wf_aenv__tvar; [ exact HβΘ | assumption ]
    |
      rewrite strip_uskl_open;
      rewrite (@msubst_uskl_open_comm ρ (pskl_to_uskl (uskl_to_pskl ψ)) β
                 Hlcρ Hβρ Hβf);
      apply HlcSbody
    |
      eapply a_wf_pskl_delta_mono;
        [ apply HwfP0β
        | let Hx := fresh in intros ? _ Hx; clear - Hx; fsetdec ]
    |
      rewrite strip_uskl_open;
      rewrite (@msubst_uskl_open_comm ρ (pskl_to_uskl (uskl_to_pskl ψ)) β
                 Hlcρ Hβρ Hβf);
      rewrite uskl_to_pskl_open;
      eapply a_wf_pskl_delta_mono;
        [ exact (HbodyS β ltac:(clear - Hβ; solve_notin_auto))
        | let Hx := fresh in intros ? _ Hx; clear - Hx; fsetdec ]
    | delta_open_goal β HβΘ Hrig Δ1 Δ2
    | delta_open_goal β HβΘ Hrig Δ1 Δ2
    | delta_open_goal β HβΘ Hrig Δ1 Δ2 ].

Lemma a_consistag_decoration_var : forall ψ P0 Ψa,
  {{ ψ ∼ P0 ⤳ Ψa }}da ->
  forall Δ1 Δ2 Ψ Θ0 P Θ1 ρ,
    rsubst_lc ρ ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | P0 | Ψ ]
      (msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψ))) ∼ P ⊣ Θ1 }}da ->
    {{ ⊢ Θ0 }}a ->
    lc_uskl (msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψ))) ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
    {{ Θ0 ⨟ empty ⊢ₚₛ (uskl_to_pskl (msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψ)))) }}a ->
    (forall α, α `in` (Δ1 `union` Δ2) -> binds α abind_tvar Θ0) ->
    no_flex_dep (Δ1 `union` Δ2) Θ0 ->
    flex_above_free (Δ1 `union` Δ2) Θ0 ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | P0 | (Ψ `union` Ψa) ]
      (msubst_uskl ρ ψ) ∼ P ⊣ Θ1 }}da.
Proof.
  intros ψ P0 Ψa H; induction H;
    intros Δ1 Δ2 Ψc Θ0 Qc Θ1 ρ Hlcρ Hcons Hwf HlcS HwfP0 HwfS Hrig Hnfd Hfaf.
  -
    simpl in Hcons |- *.
    eapply a_consistag_psi_cong; [ exact Hcons | clear - H; fsetdec ].
  -
    simpl in Hcons |- *.
    eapply a_consistag_psi_cong; [ exact Hcons | clear - H; fsetdec ].
  -
    eapply a_consistag_psi_cong;
      [ eapply a_consistag_vacuous_erasure;
          [ exact Hcons | reflexivity | ]
      | clear - H; fsetdec ].
    symmetry; apply uskl_to_pskl_msubst_strip.
  -
    simpl in HlcS. rewrite msubst_uskl_arrow in HlcS.
    apply lc_uskl_arrow_inv in HlcS as [HlcS1 HlcS2].
    simpl in HwfS. rewrite msubst_uskl_arrow in HwfS. simpl in HwfS.
    apply a_wf_pskl_arrow_inv in HwfS as [HwfS1 HwfS2].
    apply a_wf_pskl_arrow_inv in HwfP0 as [HwfP1 HwfP2].
    rewrite msubst_uskl_arrow.
    simpl in Hcons. rewrite msubst_uskl_arrow in Hcons.
    inversion Hcons; subst. clear Hcons.
    lazymatch goal with
    | Hc1 : {{ _ ⊢[ _ | _ | _ | ?Ψi1 ] _ ∼ _ ⊣ ?Θm }}da,
      Hc2 : {{ ?Θm ⊢[ _ | _ | _ | ?Ψi2 ] _ ∼ _ ⊣ _ }}da,
      HΨi : _ [=] union ?Ψi1 ?Ψi2 |- _ =>
        destruct (a_consistag_sound_aux Hc1 Hwf HlcS1 HwfP1 HwfS1 Hrig Hnfd Hfaf)
          as [Hle [HwfΘm [HnfdΘm [HfafΘm _]]]];
        eapply a_consistag__arrow with
          (Ψ1 := Ψi1 `union` Ψ1) (Ψ2 := Ψi2 `union` Ψ2) (Θ1 := Θm);
        [ eapply IHa_solvetag_eq1;
            [ exact Hlcρ | exact Hc1 | exact Hwf | exact HlcS1 | exact HwfP1
            | exact HwfS1 | exact Hrig | exact Hnfd | exact Hfaf ]
        | eapply IHa_solvetag_eq2;
            [ exact Hlcρ | exact Hc2 | exact HwfΘm | exact HlcS2
            | eapply a_wf_pskl_isub; [ exact HwfP2 | exact Hle ]
            | eapply a_wf_pskl_isub; [ exact HwfS2 | exact Hle ]
            | intros α Hα; eapply a_isub_binds_tvar; [ exact Hle | apply Hrig; exact Hα ]
            | exact HnfdΘm | exact HfafΘm ]
        | clear - HΨi H1; fsetdec ]
    end.
  -
    rewrite msubst_uskl_all_tag.
    simpl in Hcons. rewrite msubst_uskl_all_syn in Hcons.
    inversion Hcons; subst.
    match goal with
    | Hc : forall a, a `notin` _ -> {{ _ ⊢[ _ | _ | _ | _ ] _ ∼ _ ⊣ _ }}da |- _ =>
        rename Hc into Hcbody
    end.
    simpl in HlcS. rewrite msubst_uskl_all_syn in HlcS. inversion HlcS; subst.
    match goal with Hb : forall _, lc_uskl _ |- _ => rename Hb into HlcSbody end.
    inversion HwfP0 as [ | | | LP Θa Δa P0a Hbody0 Heqa | | ]; subst.
    simpl in HwfS. rewrite msubst_uskl_all_syn in HwfS. simpl in HwfS.
    inversion HwfS as [ | | | LS ΘbS ΔbS SbS HbodyS HeqS | | ]; subst.
    eapply a_consistag__forall_inh_tagged
      with (Ψ0 := Ψc `union` Ψ0) (ε := ε)
           (L := LP `union` LS `union` L `union` L0 `union` dom ρ
                 `union` msubst_ftv ρ `union` dom Θ0);
      [ intros β Hβ | clear - H1; fsetdec ].
    decoration_var_forall_open H0 β Hβ ρ ψ Θ0 Hlcρ Hcbody HlcSbody
      (Hbody0 β ltac:(clear - Hβ; solve_notin_auto)) HbodyS Hrig Δ1 Δ2.
  -
    rewrite msubst_uskl_dot_univ_ghost.
    simpl in HlcS. rewrite msubst_uskl_univ_ghost in HlcS.
    apply lc_uskl_univ_ghost_inv in HlcS.
    simpl in HwfS. rewrite msubst_uskl_univ_ghost in HwfS. simpl in HwfS.
    apply a_wf_pskl_univ_ghost_inv in HwfS as [_ HwfS].
    apply a_wf_pskl_univ_ghost_inv in HwfP0 as [_ HwfP0].
    simpl in Hcons. rewrite msubst_uskl_univ_ghost in Hcons.
    inversion Hcons; subst;
      try (match goal with Hg : guarded_pskl (pskl_univ_ghost _) |- _ =>
             solve [ inversion Hg ] end);
      try (match goal with Hg : guarded_uskl (uskl_univ_ghost _) |- _ =>
             solve [ inversion Hg ] end).
    match goal with
    | Hc : {{ _ ⊢[ _ | _ | _ | _ ]
             (msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψ))) ∼ _ ⊣ _ }}da |- _ =>
        apply a_consistag__univ_ghostg;
        eapply IHa_solvetag_eq;
          [ exact Hlcρ | exact Hc | exact Hwf | exact HlcS | exact HwfP0
          | exact HwfS | exact Hrig | exact Hnfd | exact Hfaf ]
    end.
  -
    rewrite msubst_uskl_all_tag.
    simpl in Hcons. rewrite msubst_uskl_all_syn in Hcons.
    inversion Hcons; subst;
      try (match goal with Hg : guarded_uskl (uskl_all_syn _) |- _ =>
             solve [ inversion Hg ] end).
    match goal with
    | Hc : forall a, a `notin` _ -> {{ _ ⊢[ _ | _ | _ | _ ] _ ∼ _ ⊣ _ }}da |- _ =>
        rename Hc into Hcbody
    end.
    simpl in HlcS. rewrite msubst_uskl_all_syn in HlcS. inversion HlcS; subst.
    match goal with Hb : forall _, lc_uskl _ |- _ => rename Hb into HlcSbody end.
    simpl in HwfS. rewrite msubst_uskl_all_syn in HwfS. simpl in HwfS.
    inversion HwfS as [ | | | LS ΘbS ΔbS SbS HbodyS HeqS | | ]; subst.
    eapply a_consistag__forall_syn_tagged
      with (ε := ε) (L := LS `union` L `union` L0 `union` dom ρ
                          `union` msubst_ftv ρ `union` dom Θ0);
      intros β Hβ.
    decoration_var_forall_open H0 β Hβ ρ ψ Θ0 Hlcρ Hcbody HlcSbody
      (a_wf_pskl_reassoc HwfP0 β) HbodyS Hrig Δ1 Δ2.
  -
    destruct ψ; simpl in H; try solve [ inversion H ]; simpl in Hcons.
    +
      eapply a_consistag_psi_cong; [ exact Hcons | ].
      assert (Hemp : Ψ [=] empty)
        by (eapply a_solvetag_eq_atom_empty; [ exact H0 | left; reflexivity ]).
      clear - Hemp; fsetdec.
    +
      eapply a_consistag_psi_cong; [ exact Hcons | ].
      assert (Hemp : Ψ [=] empty)
        by (eapply a_solvetag_eq_atom_empty; [ exact H0 | right; eauto ]).
      clear - Hemp; fsetdec.
    +
      inversion H; subst.
      assert (Hml1 : lc_uskl (msubst_uskl ρ ψ1))
        by (apply msubst_uskl_lc; [ exact Hlcρ | apply lc_uskl_of_pskl; assumption ]).
      assert (Hml2 : lc_uskl (msubst_uskl ρ ψ2))
        by (apply msubst_uskl_lc; [ exact Hlcρ | apply lc_uskl_of_pskl; assumption ]).
      apply a_wf_pskl_univ_ghost_inv in HwfP0 as [_ HwfP0].
      rewrite msubst_uskl_arrow in Hcons.
      inversion Hcons; subst.
      apply a_consistag__univ_ghost_r.
      * rewrite msubst_uskl_arrow. constructor; assumption.
      * rewrite msubst_uskl_arrow; unfold a_non_flex; simpl; split;
          [ constructor; apply lc_uskl_to_pskl; assumption
          | intro Hf; inversion Hf ].
      * eapply IHa_solvetag_eq;
          [ exact Hlcρ
          | simpl; rewrite msubst_uskl_arrow; eassumption
          | exact Hwf | exact HlcS | exact HwfP0 | exact HwfS
          | exact Hrig | exact Hnfd | exact Hfaf ].
  -
    assert (Hnas : no_all_syn_uskl
                     (msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψ))))
      by (eapply a_consistag_flexvar_subject_no_all_syn;
            [ exact Hcons | exact Hwf | exact HwfS ]).
    assert (Heq : msubst_uskl ρ ψ
                  = msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψ)))
      by (apply msubst_ghostfree_eq_strip; [ exact H | exact Hnas ]).
    rewrite Heq.
    eapply a_consistag_psi_cong; [ exact Hcons | clear - H0; fsetdec ].
Qed.

Lemma a_subtag_psi_cong : forall NM M P0 Ψ Θ0 R P Θ1,
  {{ Θ0 ⊢[ NM | M | P0 | Ψ ] R ⩽ P ⊣ Θ1 }}da ->
  forall Ψ', Ψ [=] Ψ' ->
  {{ Θ0 ⊢[ NM | M | P0 | Ψ' ] R ⩽ P ⊣ Θ1 }}da.
Proof.
  intros NM M P0 Ψ Θ0 R P Θ1 H; induction H; intros Ψ' Heq.
  -  apply a_subtag__infer; clear - H Heq; fsetdec.
  -  eapply a_subtag__check; try assumption.
    eapply a_consistag_psi_cong; [ eassumption | exact Heq ].
  -  eapply a_subtag__forall_r; try eassumption.
    match goal with
    | IH : forall Ψ0, _ |- _ => eapply IH; exact Heq
    end.
  -  apply a_subtag__univ_ghost_r; [ assumption | clear - H0 Heq; fsetdec ].
  -  eapply a_subtag__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
      [ eassumption | eassumption
      | match goal with Ho : _ [=] union Ψ1 Ψ2 |- _ => clear - Ho Heq; fsetdec end ].
  -
    eapply a_subtag__forall_l_tagged with (L := L) (Ξ := Ξ) (P1 := P1);
      try eassumption.
    intros Ψg ψg Hfr Hsort Hera.
    match goal with
    | IHfam : forall (a : atoms) (b : uskl), _ |- _ =>
        eapply (IHfam Ψg ψg Hfr Hsort Hera); clear - Heq; fsetdec
    end.
  -
    eapply a_subtag__forall_l_untagged with (L := L) (Ξ := Ξ) (P1 := P1);
      try eassumption.
    intros Ψg ψg Hfr Hsort Hera.
    match goal with
    | IHfam : forall (a : atoms) (b : uskl), _ |- _ =>
        eapply (IHfam Ψg ψg Hfr Hsort Hera); clear - Heq; fsetdec
    end.
  -  apply a_subtag__ghost; clear - H Heq; fsetdec.
  -  apply a_subtag__ghostg; clear - H Heq; fsetdec.
  -  apply a_subtag__univ_ghost_l; [ assumption | ].
    match goal with IH : forall Ψ0, _ |- _ => eapply IH; exact Heq end.
  -  apply a_subtag__univ_ghost_lg; [ assumption | ].
    match goal with IH : forall Ψ0, _ |- _ => eapply IH; exact Heq end.
  -  apply a_subtag__flex_mono; [ eassumption | clear - H0 Heq; fsetdec ].
Qed.

Lemma a_solvetag_sub_eq_tags_bound :
  (forall ψ M P Ψ, {{ ψ ≼[ M ] P ⤳ Ψ }}da -> Ψ [<=] ftag_in_uskl ψ) /\
  (forall ψ P Ψ, {{ ψ ∼ P ⤳ Ψ }}da -> Ψ [<=] ftag_in_uskl ψ).
Proof.
  apply a_solvetag_sub_eq_mutind;
    intros; simpl;
    try solve [ clear - e; fsetdec ];
    try solve [ assumption ];
    try solve [ match goal with HΨ : _ [=] union _ _ |- _ =>
                  clear - HΨ H H0; fsetdec end ];
    try match goal with
        | H : forall β, β `notin` ?L -> _ [<=] ftag_in_uskl _ |- _ =>
            destruct (atom_fresh L) as [β Hβ];
            pose proof (H β Hβ) as Hb;
            try rewrite (ftag_in_uskl_open_var _ β) in Hb;
            try (clear - Hb; fsetdec)
        end.

  match goal with HΨ : _ [=] add _ _ |- _ => clear - HΨ Hb; fsetdec end.
Qed.

Lemma a_solvetag_sub_tags_bound : forall ψ M P Ψ,
  {{ ψ ≼[ M ] P ⤳ Ψ }}da -> Ψ [<=] ftag_in_uskl ψ.
Proof. intros; eapply (proj1 a_solvetag_sub_eq_tags_bound); eauto. Qed.

Lemma a_solvetag_sub_eq_ghost_empty :
  (forall ψ M P Ψ, {{ ψ ≼[ M ] P ⤳ Ψ }}da -> P = pskl_ghost -> Ψ [=] empty) /\
  (forall ψ P Ψ, {{ ψ ∼ P ⤳ Ψ }}da -> P = pskl_ghost -> Ψ [=] empty).
Proof.
  apply a_solvetag_sub_eq_mutind;
    intros; subst; try discriminate;
    try solve [ assumption ];
    try solve [ auto ];
    try solve [ inv_guarded_ghost ];
    try match goal with
        | H : forall β, β `notin` ?L -> pskl_ghost = pskl_ghost -> _ |- _ =>
            destruct (atom_fresh L) as [β Hβ]; exact (H β Hβ eq_refl)
        end.
Qed.

Lemma a_solvetag_sub_ghost_empty : forall ψ M Ψ,
  {{ ψ ≼[ M ] pskl_ghost ⤳ Ψ }}da -> Ψ [=] empty.
Proof. intros; eapply (proj1 a_solvetag_sub_eq_ghost_empty); eauto. Qed.

Lemma a_solvetag_sub_eq_target_rename :
  (forall ψ M P Ψ, {{ ψ ≼[ M ] P ⤳ Ψ }}da ->
     forall α β0, {{ ψ ≼[ M ] (subst_pskl_in_pskl (pskl_var_f β0) α P) ⤳ Ψ }}da) /\
  (forall ψ P Ψ, {{ ψ ∼ P ⤳ Ψ }}da ->
     forall α β0, {{ ψ ∼ (subst_pskl_in_pskl (pskl_var_f β0) α P) ⤳ Ψ }}da).
Proof.
  apply a_solvetag_sub_eq_mutind;
    intros; simpl;

    try solve [ constructor; auto ];

    try solve [ apply a_solvetag_sub__forall_l with (L := L);
                intros β Hβ; auto ];
    try solve [ apply a_solvetag_eq__forall_syn with (L := L);
                intros β Hβ;
                match goal with
                | IH : forall b : atom, _ |- _ =>
                    solve [ specialize (IH β Hβ α β0); simpl in IH; exact IH ]
                end ];

    try solve [ apply a_solvetag_sub__check;
                [ apply pskl_ghost_free_subst_var; assumption
                | assumption | apply guarded_pskl_subst_var; assumption
                | auto ] ];

    try solve [ eapply a_solvetag_sub__arrow; eauto ];
    try solve [ eapply a_solvetag_eq__arrow; eauto ];

    try solve [ destruct_if;
                apply a_solvetag_eq__flex_r; assumption ];

    try solve [ apply a_solvetag_sub__forall_r
                  with (L := L `union` singleton α);
                [ apply pskl_ghost_free_subst_var; assumption | ];
                intros β Hβ;
                rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
                  [ | clear - Hβ; fsetdec | constructor ];
                match goal with
                | IH : forall b : atom, _ |- _ =>
                    solve [ apply IH; clear - Hβ; fsetdec ]
                end ];
    try solve [ eapply a_solvetag_eq__forall_inh
                  with (L := L `union` singleton α);
                [ intros β Hβ;
                  rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
                    [ | clear - Hβ; fsetdec | constructor ];
                  match goal with
                  | IH : forall b : atom, _ |- _ =>
                      solve [ apply IH; clear - Hβ; fsetdec ]
                  end
                | eassumption ] ];

    try solve [ apply a_solvetag_eq__univ_ghost_r; [ assumption | auto ] ].
Qed.

Lemma a_solvetag_subst_cstrs : forall 𝒞 ψ Ψ,
  {{ 𝒞 ⊩ ψ ⤳ Ψ }}da ->
  forall α β0, {{ (subst_cstrs β0 α 𝒞) ⊩ ψ ⤳ Ψ }}da.
Proof.
  induction 1; intros α0 β1; simpl.
  - apply a_solvetag__empty; assumption.
  - apply a_solvetag__sub.
    apply (proj1 a_solvetag_sub_eq_target_rename); assumption.
  - eapply a_solvetag__eq;
      [ apply (proj2 a_solvetag_sub_eq_target_rename); eassumption
      | apply IHa_solvetag | assumption ].
Qed.

Lemma a_solvetag_sub_all_syn_open : forall ψ P Ψ,
  {{ ψ ≼[ mode_tc ] (pskl_all_syn P) ⤳ Ψ }}da ->
  forall β, {{ ψ ≼[ mode_tc ] (open_pskl_wrt_pskl P (pskl_var_f β)) ⤳ Ψ }}da.
Proof.
  intros ψ P Ψ H.
  remember (pskl_all_syn P) as Q0 eqn:HQ.
  remember mode_tc as M0 eqn:HM.
  revert P HQ. induction H; intros B0 HQ β0; subst; try discriminate HQ.
  -
    apply a_solvetag_sub__var; assumption.
  -
    apply a_solvetag_sub__forall_l with (L := L). intros β Hβ.
    apply H0; auto.
  -
    apply a_solvetag_sub__univ_ghost_lg. apply IHa_solvetag_sub; auto.
  -
    match goal with Hg : guarded_pskl (pskl_all_syn _) |- _ =>
      inversion Hg end.
  -
    inversion HQ; subst.
    destruct (atom_fresh (L `union` ftvar_in_pskl B0 `union` singleton β0))
      as [β' Hβ'].

    pose proof (H0 β' ltac:(clear - Hβ'; solve_notin_auto)) as Hinst.
    pose proof (proj1 a_solvetag_sub_eq_target_rename _ _ _ _ Hinst β' β0)
      as Hren.
    rewrite <- subst_pskl_in_pskl_intro in Hren;
      [ exact Hren | clear - Hβ'; fsetdec ].
Qed.

Lemma msubst_uskl_unit : forall ρ, msubst_uskl ρ uskl_unit = uskl_unit.
Proof. induction ρ as [|[α1 g] ρ' IH]; simpl; [reflexivity|]; rewrite IH; reflexivity. Qed.

Lemma msubst_uskl_ghost : forall ρ, msubst_uskl ρ uskl_ghost = uskl_ghost.
Proof. induction ρ as [|[α1 g] ρ' IH]; simpl; [reflexivity|]; rewrite IH; reflexivity. Qed.

Lemma msubst_uskl_dot_ghost : forall ρ, msubst_uskl ρ uskl_dot_ghost = uskl_dot_ghost.
Proof. induction ρ as [|[α1 g] ρ' IH]; simpl; [reflexivity|]; rewrite IH; reflexivity. Qed.

Lemma guarded_msubst_decorate : forall ρ ψ,
  rsubst_lc ρ ->
  lc_uskl ψ ->
  guarded_uskl (msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψ))) ->
  guarded_uskl (msubst_uskl ρ ψ).
Proof.
  intros ρ ψ Hlcρ Hlc Hg. destruct ψ; simpl in Hg |- *.
  - rewrite msubst_uskl_unit in *. exact Hg.
  - inversion Hlc.
  - exact Hg.
  - rewrite msubst_uskl_arrow in *. inversion Hlc; subst.
    constructor; apply msubst_uskl_lc; assumption.
  - rewrite msubst_uskl_all_syn in Hg. inversion Hg.
  - rewrite msubst_uskl_all_syn in Hg. inversion Hg.
  - rewrite msubst_uskl_ghost in Hg. inversion Hg.
  - rewrite msubst_uskl_univ_ghost in Hg. inversion Hg.
  - rewrite msubst_uskl_ghost in Hg. inversion Hg.
  - rewrite msubst_uskl_univ_ghost in Hg. inversion Hg.
Qed.

Lemma erase_swap : forall ρ (ψ : uskl) R,
  ⌊ R ⌋ˢ = ⌊ msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψ)) ⌋ˢ ->
  ⌊ msubst_uskl ρ ψ ⌋ˢ = ⌊ R ⌋ˢ.
Proof.
  intros ρ ψ R H. rewrite H. symmetry. apply uskl_to_pskl_msubst_strip.
Qed.

Local Ltac strip_shape_cases HeqT Hlcψ :=
  try rewrite msubst_uskl_unit in HeqT;
  try rewrite msubst_uskl_arrow in HeqT;
  try rewrite msubst_uskl_all_syn in HeqT;
  try rewrite msubst_uskl_ghost in HeqT;
  try rewrite msubst_uskl_univ_ghost in HeqT;
  try discriminate HeqT;
  try solve [ inversion Hlcψ ].

Local Ltac tagfree_solves_nothing Hst :=
  let Hb := fresh "Hb" in
  pose proof (a_solvetag_sub_tags_bound Hst) as Hb;
  simpl in Hb; clear - Hb; fsetdec.

Lemma a_subtag_decoration_var : forall NM M P0 Ψ Θ0 R P Θ1,
  {{ Θ0 ⊢[ NM | M | P0 | Ψ ] R ⩽ P ⊣ Θ1 }}da ->
  forall ψ Ψa ρ,
    R = msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψ)) ->
    {{ ψ ≼[ M ] P0 ⤳ Ψa }}da ->
    rsubst_lc ρ ->
    lc_uskl ψ ->
    {{ ⊢ Θ0 }}a ->
    lc_uskl R ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
    {{ Θ0 ⨟ empty ⊢ₚₛ ⌊ R ⌋ˢ }}a ->
    (NM = a_sub_mode_sk -> mod_comp_sk (pskl_to_bskl_inh P0) M) ->
    {{ Θ0 ⊢[ NM | M | P0 | (Ψ `union` Ψa) ] (msubst_uskl ρ ψ) ⩽ P ⊣ Θ1 }}da.
Proof.
  intros NM M P0 Ψ Θ0 R P Θ1 Hsub.
  induction Hsub;
    intros ψf Ψa ρ HeqT Hst Hlcρ Hlcψ Hwf HlcT HwfP0 HwfT Hmod.
  -
    assert (Hemp : Ψa [=] empty)
      by (eapply a_solvetag_sub_ghost_empty; eauto).
    eapply a_subtag_psi_cong with (Ψ := Ψ);
      [ | clear - Hemp; fsetdec ].
    rewrite HeqT. rewrite uskl_to_pskl_msubst_strip.
    apply a_subtag__infer; assumption.
  -
    inversion Hst; subst; simpl in *.
    +
      eapply a_subtag_psi_cong with (Ψ := Ψ);
        [ eapply a_subtag__check; eassumption
        | fsetdec_empty ].
    +
      match goal with Hg : guarded_uskl (msubst_uskl _ _) |- _ =>
        rewrite msubst_uskl_all_syn in Hg; inversion Hg end.
    +
      match goal with Hg : guarded_uskl (msubst_uskl _ _) |- _ =>
        rewrite msubst_uskl_univ_ghost in Hg; inversion Hg end.
    +
      inv_guarded_ghost.
    +
      eapply a_subtag__check.
      * assumption.
      * apply guarded_msubst_decorate;
          [ exact Hlcρ | exact Hlcψ | assumption ].
      * assumption.
      * eapply a_consistag_decoration_var;
          [ eassumption | exact Hlcρ | eassumption
          | exact Hwf | exact HlcT | exact HwfP0 | exact HwfT
          | apply rig_empty | apply no_flex_dep_empty | apply faf_empty ].
    +
      match goal with Hg : guarded_pskl (pskl_all_syn _) |- _ =>
        inversion Hg end.
  -
    match goal with
    | Hfr : ?a `notin` union (dom (?Ξx ++ ?Θx)) _ |- _ =>
        rewrite dom_app in Hfr
    end.
    eapply a_subtag__forall_r with (α := α) (Ξ := Ξ);
      [ assumption | assumption | assumption | | ].
    {
      assert (Heqf : ⌊ msubst_uskl ρ ψf ⌋ˢ = ⌊ R ⌋ˢ)
        by (apply erase_swap; rewrite HeqT; reflexivity).
      pose proof (ftvar_in_pskl_uskl_to_pskl (msubst_uskl ρ ψf)) as Hf1.
      pose proof (ftvar_in_pskl_uskl_to_pskl R) as Hf2.
      rewrite Heqf in Hf1. rewrite dom_app.
      match goal with
      | Hfr : α `notin` _ |- _ => clear - Hfr Hf1 Hf2; fsetdec
      end. }
    match goal with
    | IH : forall _ : uskl, _ |- _ =>
        solve
          [ eapply IH;
            [ exact HeqT
            | apply a_solvetag_sub_all_syn_open; exact Hst
            | exact Hlcρ
            | exact Hlcψ
            | apply a_wf_aenv__tvar;
                [ match goal with
                  | Hfr : α `notin` _ |- _ => clear - Hfr; fsetdec
                  end
                | exact Hwf ]
            | exact HlcT
            | eapply a_wf_pskl_all_syn_open_tvar;
                [ exact HwfP0
                | match goal with
                  | Hfr : α `notin` _ |- _ => clear - Hfr; fsetdec
                  end ]
            | eapply a_wf_pskl_weaken;
                [ intros x b0 Hb0; unfold binds; simpl; right; exact Hb0
                | exact HwfT ]
            | intros Hsk; discriminate Hsk ] ]
    end.
  -
    assert (Hemp : Ψa [=] empty)
      by (eapply a_solvetag_sub_ghost_empty; eauto).
    eapply a_subtag_psi_cong with (Ψ := Ψ);
      [ | clear - Hemp; fsetdec ].
    rewrite HeqT. rewrite uskl_to_pskl_msubst_strip.
    apply a_subtag__univ_ghost_r;
      [ apply guarded_msubst_decorate;
          [ exact Hlcρ | exact Hlcψ | rewrite <- HeqT; assumption ]
      | assumption ].
  -
    inversion Hst; subst.
    +
      simpl in HeqT.
      eapply a_subtag_psi_cong with (Ψ := Ψ);
        [ | fsetdec_empty ].
      rewrite <- HeqT.
      eapply a_subtag__arrow; eassumption.
    +
      simpl in HeqT. rewrite msubst_uskl_all_syn in HeqT. discriminate HeqT.
    +
      simpl in HeqT. rewrite msubst_uskl_univ_ghost in HeqT. discriminate HeqT.
    +
      simpl in HeqT. rewrite msubst_uskl_arrow in HeqT.
      inversion HeqT; subst. clear HeqT.
      inversion Hlcψ; subst.
      apply lc_uskl_arrow_inv in HlcT as [HlcT1 HlcT2].
      simpl in HwfT.
      apply a_wf_pskl_arrow_inv in HwfT as [HwfT1 HwfT2].
      apply a_wf_pskl_arrow_inv in HwfP0 as [HwfP0a HwfP0b].
      rewrite msubst_uskl_arrow.
      match goal with
      | Hc1 : {{ _ ⊢[ _ | _ | ?P0a | ?Ψ1 ] _ ∼ ?Q1 ⊣ ?Θm }}da,
        Hs2 : {{ ?Θm ⊢[ _ | _ | ?P0b | ?Ψ2 ] _ ⩽ ?Q2 ⊣ _ }}da,
        HΨ : _ [=] union ?Ψ1 ?Ψ2,
        Hst1 : {{ _ ∼ ?P0a ⤳ ?Ψa1 }}da,
        Hst2 : {{ _ ≼[ _ ] ?P0b ⤳ ?Ψa2 }}da,
        HΨa : Ψa [=] union ?Ψa1 ?Ψa2 |- _ =>
          destruct (a_consistag_sound_aux Hc1 Hwf HlcT1 HwfP0a HwfT1
                      (@rig_empty _) (@no_flex_dep_empty _) (@faf_empty _))
            as [Hle [HwfΘm _]];
          eapply a_subtag__arrow
            with (Ψ1 := Ψ1 `union` Ψa1) (Ψ2 := Ψ2 `union` Ψa2) (Θ1 := Θm);
          [ eapply a_consistag_decoration_var;
              [ exact Hst1 | exact Hlcρ | exact Hc1 | exact Hwf | exact HlcT1
              | exact HwfP0a | exact HwfT1
              | apply rig_empty | apply no_flex_dep_empty | apply faf_empty ]
          | match goal with
            | IH : forall ψ : uskl, _ |- _ =>
                eapply IH;
                [ reflexivity | exact Hst2 | exact Hlcρ | assumption
                | exact HwfΘm | exact HlcT2
                | eapply a_wf_pskl_isub; [ exact HwfP0b | exact Hle ]
                | eapply a_wf_pskl_isub; [ exact HwfT2 | exact Hle ]
                | intros Hsk; specialize (Hmod Hsk); simpl in Hmod;
                  inversion Hmod; subst; assumption ]
            end
          | clear - HΨ HΨa; fsetdec ]
      end.
  -
    destruct ψf; simpl in HeqT; strip_shape_cases HeqT Hlcψ.

    assert (Hemp : Ψa [=] empty) by (tagfree_solves_nothing Hst).
    eapply a_subtag_psi_cong with (Ψ := Ψ);
      [ | clear - Hemp; fsetdec ].
    rewrite <- HeqT.
    eapply a_subtag__forall_l_tagged with (L := L) (Ξ := Ξ) (P1 := P1);
      eassumption.
  -
    destruct ψf; simpl in HeqT; strip_shape_cases HeqT Hlcψ.
    +
      assert (Hemp : Ψa [=] empty) by (tagfree_solves_nothing Hst).
      eapply a_subtag_psi_cong with (Ψ := Ψ);
        [ | clear - Hemp; fsetdec ].
      rewrite <- HeqT.
      eapply a_subtag__forall_l_untagged with (L := L) (Ξ := Ξ) (P1 := P1);
        eassumption.
    +
      inversion Hst; subst.
      *
        assert (Hnode : {{ Θ0 ⊢[ NM | M | pskl_ghost | Ψ ]
                          (uskl_all_syn R) ⩽ Q ⊣ Θ1 }}da)
          by (eapply a_subtag__forall_l_untagged
                with (L := L) (Ξ := Ξ) (P1 := P1); eassumption).
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ | fsetdec_empty ].
        eapply a_subtag_vacuous_erasure;
          [ exact Hnode | reflexivity
          | apply msubst_uskl_lc; assumption
          | apply erase_swap; rewrite HeqT; simpl;
            rewrite msubst_uskl_all_syn; reflexivity ].
      *
        match goal with Hg : guarded_uskl _ |- _ => inversion Hg end.
      *
        match goal with
        | Ho : guarded_pskl (pskl_all_syn _) \/ _ |- _ =>
            destruct Ho as [Hg | Hd]; [ inversion Hg | discriminate Hd ]
        end.
    +
      inversion HeqT; subst; clear HeqT.
      inversion Hlcψ; subst.
      inversion Hst; subst.
      *
        rewrite msubst_uskl_all_tag.
        match goal with
        | Hstb : forall b : atom, b `notin` ?L1 -> {{ _ ≼[ _ ] _ ⤳ _ }}da |- _ =>
            rename Hstb into Hstbody; rename L1 into Lst
        end.
        eapply a_subtag__forall_l_tagged with (L := L) (Ξ := Ξ) (P1 := P1);
          [ assumption | assumption | | assumption | assumption | ].
        {
          intros α Hα.
          replace (⌊ open_uskl_wrt_uskl (msubst_uskl ρ ψf) (uskl_var_f α) ⌋ˢ)
            with (⌊ open_uskl_wrt_uskl
                      (msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψf)))
                      (uskl_var_f α) ⌋ˢ)
            by (rewrite ! uskl_to_pskl_open;
                rewrite uskl_to_pskl_msubst_strip; reflexivity).
          auto. }

        intros Ψg ψg Hfr Hsort Hera.
        assert (Hlcg : lc_uskl ψg)
          by (apply is_dskl_lc; inversion Hsort; assumption).
        destruct (atom_fresh
                    (Lst `union` dom ρ `union` msubst_ftv ρ
                     `union` ftvar_in_uskl ψf
                     `union` ftvar_in_uskl
                         (msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψf)))
                     `union` ftvar_in_uskl (msubst_uskl ρ ψf)))
          as [β Hβ].
        assert (Hβρ : β `notin` dom ρ) by (clear - Hβ; fsetdec).
        assert (Hβf : forall α1 ψg0, binds α1 ψg0 ρ ->
                        β `notin` ftvar_in_uskl ψg0).
        { intros α1 ψg0 Hb. pose proof (msubst_ftv_binds _ _ _ Hb) as Hsc.
          clear - Hβ Hsc. fsetdec. }
        assert (Hlcρ' : rsubst_lc ((β, ψg) :: ρ)).
        { intros α1 ψg0 Hb. unfold binds in Hb. simpl in Hb.
          destruct Hb as [Hb | Hb];
            [ inversion Hb; subst; exact Hlcg | eapply Hlcρ; exact Hb ]. }
        assert (Hsubject :
            msubst_uskl ((β, ψg) :: ρ)
              (pskl_to_uskl (uskl_to_pskl (open_uskl_wrt_uskl ψf (uskl_var_f β))))
            = open_uskl_wrt_uskl
                (msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψf))) ψg).
        { simpl. rewrite strip_uskl_open.
          rewrite (@msubst_uskl_open_comm ρ _ β Hlcρ Hβρ Hβf).
          rewrite <- subst_uskl_in_uskl_intro;
            [ reflexivity | clear - Hβ; fsetdec ]. }
        assert (Hresult :
            msubst_uskl ((β, ψg) :: ρ) (open_uskl_wrt_uskl ψf (uskl_var_f β))
            = open_uskl_wrt_uskl (msubst_uskl ρ ψf) ψg).
        { simpl.
          rewrite (@msubst_uskl_open_comm ρ ψf β Hlcρ Hβρ Hβf).
          rewrite <- subst_uskl_in_uskl_intro;
            [ reflexivity | clear - Hβ; fsetdec ]. }

        destruct (atom_fresh L) as [α0 Hα0].
        assert (Hdecls : a_decls Ξ)
          by (eapply a_extract_decls; eauto).
        assert (HwfΞΘ : {{ ⊢ (Ξ ++ Θ0) }}a).
        { apply a_wf_aenv_prepend_decls; auto.
          - match goal with Hu : uniq (Ξ ++ Θ0) |- _ =>
              clear - Hu; solve_uniq end.
          - intros α1 Hα1.
            match goal with Hu : uniq (Ξ ++ Θ0) |- _ =>
              clear - Hu Hα1; destruct_uniq;
              unfold disjoint in *; fsetdec end. }
        assert (Hmono : forall x (b : abind),
                   binds x b Θ0 -> binds x b (Ξ ++ Θ0))
          by (intros x b Hb; unfold binds in *; apply in_or_app; auto).
        assert (HwfP0' : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a)
          by (eapply a_wf_pskl_weaken; [ exact Hmono | exact HwfP0 ]).
        assert (HlcSψ : lc_uskl (open_uskl_wrt_uskl
                          (msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψf))) ψg)).
        { apply lc_body_uskl_wrt_uskl; [ | exact Hlcg ].
          eapply lc_body_uskl_all_syn_1. exact HlcT. }
        assert (HwfSψ : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ
                  ⌊ open_uskl_wrt_uskl
                      (msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψf))) ψg ⌋ˢ }}a).
        { unfold open_uskl_wrt_uskl. rewrite uskl_to_pskl_open_rec.
          rewrite Hera.
          change (open_pskl_wrt_pskl_rec 0 P1
                    ⌊ msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψf)) ⌋ˢ)
            with (open_pskl_wrt_pskl
                    ⌊ msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψf)) ⌋ˢ P1).
          simpl in HwfT.
          inversion HwfT; subst.
          match goal with
          | Hbody : forall α, α `notin` ?L0 -> {{ _ ⨟ _ ⊢ₚₛ _ }}a |- _ =>
              apply a_wf_pskl_open with (L := L0);
                [ intros α Hα;
                  apply a_wf_pskl_weaken with (Θ := (α ~ abind_tvar) ++ Θ0);
                    [ intros x b Hb; unfold binds in Hb |- *; simpl in Hb |- *;
                      destruct Hb as [Hb | Hb];
                        [ left; exact Hb | right; apply Hmono; exact Hb ]
                    | apply Hbody; auto ]
                | assumption ]
          end. }
        rewrite <- Hresult.
        eapply a_subtag_psi_cong;
          [ eapply (H5 Ψg ψg Hfr Hsort Hera
                      (open_uskl_wrt_uskl ψf (uskl_var_f β)) Ψa
                      ((β, ψg) :: ρ))
          | clear; fsetdec ].
        all: try solve [ rewrite Hsubject; reflexivity ].
        all: try solve [ apply Hstbody; clear - Hβ; fsetdec ].
        all: try solve [ exact Hlcρ' ].
        all: try solve [ apply lc_body_uskl_wrt_uskl;
                         [ eapply lc_body_uskl_all_tag_2; eassumption
                         | constructor ] ].
        all: try solve [ exact HwfΞΘ ].
        all: try solve [ exact HlcSψ ].
        all: try solve [ exact HwfP0' ].
        all: try solve [ exact HwfSψ ].
        all: solve [ exact Hmod ].
      *
        assert (Hnode : {{ Θ0 ⊢[ NM | M | pskl_ghost | Ψ ]
                          (uskl_all_syn
                             (msubst_uskl ρ (pskl_to_uskl ⌊ ψf ⌋ˢ))) ⩽ Q ⊣ Θ1 }}da)
          by (eapply a_subtag__forall_l_untagged
                with (L := L) (Ξ := Ξ) (P1 := P1); eassumption).
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ | fsetdec_empty ].
        eapply a_subtag_vacuous_erasure;
          [ exact Hnode | reflexivity
          | apply msubst_uskl_lc; assumption
          | apply erase_swap; simpl;
            rewrite msubst_uskl_all_syn; reflexivity ].
      *
        match goal with Hg : guarded_uskl _ |- _ => inversion Hg end.
      *
        match goal with
        | Ho : guarded_pskl (pskl_all_syn _) \/ _ |- _ =>
            destruct Ho as [Hg | Hd]; [ inversion Hg | discriminate Hd ]
        end.
  -
    destruct ψf; simpl in HeqT; strip_shape_cases HeqT Hlcψ.
    +
      assert (Hemp : Ψa [=] empty) by (tagfree_solves_nothing Hst).
      eapply a_subtag_psi_cong with (Ψ := Ψ);
        [ | clear - Hemp; fsetdec ].
      rewrite <- HeqT. apply a_subtag__ghost; assumption.
    +
      assert (Hemp : Ψa [=] empty) by (tagfree_solves_nothing Hst).
      rewrite msubst_uskl_ghost.
      eapply a_subtag_psi_cong with (Ψ := Ψ);
        [ apply a_subtag__ghost; assumption | clear - Hemp; fsetdec ].
    +
      inversion Hst; subst.
      *
        rewrite msubst_uskl_dot_ghost.
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ apply a_subtag__ghostg; assumption
          | fsetdec_empty ].
      *
        match goal with Hg : guarded_uskl uskl_dot_ghost |- _ =>
          inversion Hg end.
      *
        specialize (Hmod eq_refl). simpl in Hmod.
        inversion Hmod; subst.
        match goal with Hs : is_sskl (bskl_all_inh _) |- _ =>
          inversion Hs end.
  -
    destruct ψf; simpl in HeqT; strip_shape_cases HeqT Hlcψ.
    assert (Hemp : Ψa [=] empty) by (tagfree_solves_nothing Hst).
    eapply a_subtag_psi_cong with (Ψ := Ψ);
      [ | clear - Hemp; fsetdec ].
    rewrite <- HeqT. apply a_subtag__ghostg; assumption.
  -
    destruct ψf; simpl in HeqT; strip_shape_cases HeqT Hlcψ.
    +
      assert (Hemp : Ψa [=] empty) by (tagfree_solves_nothing Hst).
      eapply a_subtag_psi_cong with (Ψ := Ψ);
        [ | clear - Hemp; fsetdec ].
      rewrite <- HeqT. apply a_subtag__univ_ghost_l; assumption.
    +
      inversion HeqT; subst; clear HeqT.
      inversion Hlcψ; subst.
      inversion Hst; subst.
      *
        assert (Hnode : {{ Θ0 ⊢[ a_sub_mode_sk | M | pskl_ghost | Ψ ]
                          (uskl_univ_ghost
                             (msubst_uskl ρ (pskl_to_uskl ⌊ ψf ⌋ˢ))) ⩽ Q ⊣ Θ1 }}da)
          by (apply a_subtag__univ_ghost_l; assumption).
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ | fsetdec_empty ].
        eapply a_subtag_vacuous_erasure;
          [ exact Hnode | reflexivity
          | apply msubst_uskl_lc; assumption
          | apply erase_swap; simpl;
            rewrite msubst_uskl_univ_ghost; reflexivity ].
      *
        match goal with Hg : guarded_uskl (uskl_univ_ghost _) |- _ =>
          inversion Hg end.
      *
        specialize (Hmod eq_refl). simpl in Hmod.
        inversion Hmod; subst.
        match goal with Hs : is_sskl (bskl_all_inh _) |- _ =>
          inversion Hs end.
    +
      inversion HeqT; subst; clear HeqT.
      inversion Hlcψ; subst.
      inversion Hst; subst.
      *
        rewrite msubst_uskl_dot_univ_ghost.
        apply a_subtag__univ_ghost_lg; [ assumption | ].
        match goal with
        | IH : forall ψ : uskl, _ |- _ =>
            eapply IH;
              [ reflexivity | eassumption | exact Hlcρ | assumption
              | exact Hwf
              | apply lc_uskl_univ_ghost_inv; exact HlcT
              | exact HwfP0
              | simpl in HwfT; apply a_wf_pskl_univ_ghost_inv in HwfT as [_ HwfT];
                exact HwfT
              | exact Hmod ]
        end.
      *
        assert (Hnode : {{ Θ0 ⊢[ a_sub_mode_sk | M | pskl_ghost | Ψ ]
                          (uskl_univ_ghost
                             (msubst_uskl ρ (pskl_to_uskl ⌊ ψf ⌋ˢ))) ⩽ Q ⊣ Θ1 }}da)
          by (apply a_subtag__univ_ghost_l; assumption).
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ | fsetdec_empty ].
        eapply a_subtag_vacuous_erasure;
          [ exact Hnode | reflexivity
          | apply msubst_uskl_lc; assumption
          | apply erase_swap; simpl;
            rewrite msubst_uskl_univ_ghost; reflexivity ].
      *
        match goal with Hg : guarded_uskl (uskl_dot_univ_ghost _) |- _ =>
          inversion Hg end.
      *
        specialize (Hmod eq_refl). simpl in Hmod.
        inversion Hmod; subst.
        match goal with Hs : is_sskl (bskl_all_inh _) |- _ =>
          inversion Hs end.
  -
    destruct ψf; simpl in HeqT; strip_shape_cases HeqT Hlcψ.
    assert (Hemp : Ψa [=] empty) by (tagfree_solves_nothing Hst).
    eapply a_subtag_psi_cong with (Ψ := Ψ);
      [ | clear - Hemp; fsetdec ].
    rewrite <- HeqT. apply a_subtag__univ_ghost_lg; assumption.
  -
    destruct ψf; simpl in HeqT; strip_shape_cases HeqT Hlcψ.
    assert (Hemp : Ψa [=] empty) by (tagfree_solves_nothing Hst).
    eapply a_subtag_psi_cong with (Ψ := Ψ);
      [ | clear - Hemp; fsetdec ].
    rewrite <- HeqT. apply a_subtag__flex_mono; assumption.
Qed.

Lemma strip_id_ghost_free_no_all_syn : forall ψ,
  uskl_ghost_free ψ ->
  no_all_syn_uskl (pskl_to_uskl (uskl_to_pskl ψ)) ->
  pskl_to_uskl (uskl_to_pskl ψ) = ψ.
Proof.
  intros ψ Hgf; induction Hgf; intros Hnas; simpl in *.
  - reflexivity.
  - reflexivity.
  - inversion Hnas; subst. rewrite IHHgf1, IHHgf2; auto.
  - inversion Hnas.
  - inversion Hnas.
Qed.

Lemma no_all_syn_subst_inv : forall R' R0 β,
  β `in` ftvar_in_uskl R' ->
  no_all_syn_uskl (subst_uskl_in_uskl R0 β R') ->
  no_all_syn_uskl R0.
Proof.
  induction R'; intros R0 β Hin Hnas; simpl in *;
    try solve [ exfalso; fsetdec ];
    try solve [ inversion Hnas ].
  -
    revert Hnas.
    destruct_if as [-> | Hne]; intro Hnas; [ exact Hnas | exfalso; fsetdec ].
  -
    inversion Hnas; subst.
    destruct (union_1 Hin);
      [ eapply IHR'1 | eapply IHR'2 ]; eauto.
  -
    inversion Hnas; subst. eapply IHR'; eauto.
  -
    inversion Hnas; subst. eapply IHR'; eauto.
Qed.

Lemma flexvar_decoration_swap : forall Θ α P α0 Ξ 𝒞,
  {{ Θ ⊢ P ∼[ α ] (pskl_var_f α0) ⤳ Ξ ⨾ 𝒞 }}a ->
  forall R ψa Ψa,
    ⌊ R ⌋ˢ = P ->
    {{ 𝒞 ⊩ ψa ⤳ Ψa }}da ->
    no_all_syn_uskl
      (subst_uskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa)) α R) ->
    Ψa [=] empty /\
    subst_uskl_in_uskl ψa α R
    = subst_uskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa)) α R.
Proof.
  intros Θ α P α0 Ξ 𝒞 Hlk.
  remember (pskl_var_f α0) as Ptgt eqn:HPt.
  induction Hlk; intros R0 ψa Ψa HeS Hst Hnas; try discriminate HPt.
  -
    assert (HR : R0 = uskl_var_f α).
    { destruct R0; simpl in HeS; try discriminate; congruence. }
    subst R0. simpl in Hnas |- *.
    revert Hnas.
    destruct_if as [_ | Hne];
        [ | exfalso; congruence ].
    intro Hnas.
    inversion Hst; subst.
    match goal with
    | Hone : {{ ψa ∼ _ ⤳ _ }}da |- _ => inversion Hone; subst
    end.
    all: match goal with
         | Hnil : {{ nil ⊩ _ ⤳ _ }}da |- _ => inversion Hnil; subst
         end.
    all: split.
    all: try solve [ match goal with
                     | He1 : ?A0 [=] empty, He2 : ?B0 [=] empty,
                       HU : _ [=] union ?A0 ?B0 |- _ =>
                         clear - He1 He2 HU; fsetdec
                     end ].
    all: try solve [ simpl; reflexivity ].
    all: match goal with
         | Hgf : uskl_ghost_free _ |- _ =>
             rewrite (strip_id_ghost_free_no_all_syn Hgf Hnas); reflexivity
         end.
  -
    assert (HαR : α `notin` ftvar_in_uskl R0).
    { rewrite <- (ftvar_in_pskl_uskl_to_pskl R0). rewrite HeS. assumption. }
    inversion Hst; subst.
    split; [ assumption | ].
    rewrite ! subst_uskl_in_uskl_fresh_eq; auto.
  -
    assert (HαR : α `in` ftvar_in_uskl R0).
    { rewrite <- (ftvar_in_pskl_uskl_to_pskl R0). rewrite HeS. assumption. }
    inversion Hst; subst.
    match goal with
    | Hone : {{ ψa ∼ _ ⤳ _ }}da |- _ => inversion Hone; subst
    end.
    all: match goal with
         | Hnil : {{ nil ⊩ _ ⤳ _ }}da |- _ => inversion Hnil; subst
         end.
    all: split.
    all: try solve [ match goal with
                     | He1 : ?A0 [=] empty, He2 : ?B0 [=] empty,
                       HU : _ [=] union ?A0 ?B0 |- _ =>
                         clear - He1 He2 HU; fsetdec
                     end ].
    all: try solve [ simpl; reflexivity ].
    all: pose proof (@no_all_syn_subst_inv R0
                       (pskl_to_uskl (uskl_to_pskl ψa)) α HαR Hnas) as Hnas'.
    all: match goal with
         | Hgf : uskl_ghost_free _ |- _ =>
             pose proof (strip_id_ghost_free_no_all_syn Hgf Hnas') as Hid
         end.
    all: rewrite Hid; reflexivity.
  -
    destruct R0; simpl in HeS; try discriminate HeS;
      inversion HeS; subst;
      simpl in Hnas; inversion Hnas; subst;
      match goal with
      | Hin : no_all_syn_uskl (subst_uskl_in_uskl _ _ ?R1) |- _ =>
          destruct (IHHlk eq_refl R1 ψa Ψa ltac:(reflexivity) Hst Hin)
            as [HΨ Heq]
      end;
      (split; [ exact HΨ | simpl; rewrite Heq; reflexivity ]).
Qed.

Local Ltac consistag_forall_open IHn n β Hβ α Hcbody HlcSbody Hlcstrip
    mv Hp Hfr0 HwfP0β HbodyS Hrig Δ1 Δ2 :=
  rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
    [ | clear - Hβ; fsetdec | assumption ];
  let HcI := fresh "HcI" in
  pose proof (Hcbody β ltac:(clear - Hβ; solve_notin_auto)) as HcI;
  rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var in HcI;
    [ | clear - Hβ; fsetdec | exact Hlcstrip ];
  let Hβα := fresh "Hβα" in
  assert (Hβα : β <> α)
    by (apply notin_singleton_1; clear - Hβ; solve_notin);
  let Hlk := fresh "Hlk" in
  pose proof (mv _ _ _ _ _ _ _ _ Hp Hfr0 Hβα
                ltac:(clear - Hβ; solve_notin)) as Hlk;
  let Hszb := fresh "Hszb" in
  match type of Hlk with
  | {{ _ ⊢ ?Ps ∼[ _ ] ?Pt ⤳ _ ⨾ _ }}a =>
      assert (Hszb : size_pskl Ps + size_pskl Pt <= n)
        by (rewrite ! size_pskl_open_pskl_wrt_pskl_var; cbn; lia)
  end;
  eapply (IHn _ _ _ _ _ _ Hszb Hlk);
    [ apply a_solvetag_subst_cstrs; assumption
    | apply uskl_to_pskl_open
    | assumption
    | assumption
    | apply HlcSbody
    | exact HcI
    | apply a_wf_aenv__tvar; [ clear - Hβ; fsetdec | assumption ]
    | eapply a_wf_pskl_delta_mono;
        [ apply HwfP0β
        | let Hx := fresh in intros ? _ Hx; clear - Hx; fsetdec ]
    | rewrite <- subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
        [ | clear - Hβ; fsetdec | exact Hlcstrip ];
      rewrite uskl_to_pskl_open;
      eapply a_wf_pskl_delta_mono;
        [ exact (HbodyS β ltac:(clear - Hβ; solve_notin_auto))
        | let Hx := fresh in intros ? _ Hx; clear - Hx; fsetdec ]
    | delta_open_goal β Hβ Hrig Δ1 Δ2
    | delta_open_goal β Hβ Hrig Δ1 Δ2
    | delta_open_goal β Hβ Hrig Δ1 Δ2 ].

Lemma a_consistag_decoration_size : forall n Θ α P P0 Ξc 𝒞,
  size_pskl P + size_pskl P0 <= n ->
  {{ Θ ⊢ P ∼[ α ] P0 ⤳ Ξc ⨾ 𝒞 }}a ->
  forall R' ψa Ψa Δ1 Δ2 Ψ Θ0 P' Θ1,
    {{ 𝒞 ⊩ ψa ⤳ Ψa }}da ->
    ⌊ R' ⌋ˢ = P ->
    α `notin` ftvar_in_uskl ψa ->
    lc_uskl ψa ->
    lc_uskl R' ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | P0 | Ψ ]
      (subst_uskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa)) α R') ∼ P' ⊣ Θ1 }}da ->
    {{ ⊢ Θ0 }}a ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
    {{ Θ0 ⨟ empty
      ⊢ₚₛ ⌊ subst_uskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa)) α R' ⌋ˢ }}a ->
    (forall α0, α0 `in` (Δ1 `union` Δ2) -> binds α0 abind_tvar Θ0) ->
    no_flex_dep (Δ1 `union` Δ2) Θ0 ->
    flex_above_free (Δ1 `union` Δ2) Θ0 ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | P0 | (Ψ `union` Ψa) ]
      (subst_uskl_in_uskl ψa α R') ∼ P' ⊣ Θ1 }}da.
Proof.
  induction n as [ | n IHn ];
    [ intros Θ α P P0 Ξc 𝒞 Hsz Hlook; exfalso;
      pose proof (size_pskl_min P); pose proof (size_pskl_min P0); lia | ].
  intros Θ α P P0 Ξc 𝒞 Hsz Hlook.
  destruct Hlook as
    [ Θ α P
    | Θ α P P' Hnf
    | Θ α P
    | Θ α P β α1 Hfr0 Hflx0 Hne0 Hin0
    | Θ α P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 Hg1 Hg2 Hp1 Hp2
    | Θ α P P' Ξ C b Hfr0 Hocc0 Hp
    | Θ α P P' Ξ C b Hfr0 Hocc0 Hp
    | Θ α P P' Ξ C Hp
    | Θ α P P' Ξ C b Hfr0 Hocc0 Hp
    | Θ α P P' Ξ C Hg0 Hfx0 Hp
    | Θ α P P' Ξ C Hne0 Hg0 Hp ];
    intros R ψa Ψa Δ1 Δ2 Ψc Θ0 Qc Θ1
      Hst HeS Hαψ Hlcψ HlcS Hcons Hwf HwfP0 HwfSub Hrig Hnfd Hfaf;
    cbn in Hsz.
  -
    destruct R; simpl in HeS; inversion HeS; subst;
      try solve [ inversion HlcS ].
    simpl in Hcons, HwfSub |- *.
    revert Hcons HwfSub.
    destruct_if as [_ | Hne];
        [ | exfalso; congruence ].
    intros Hcons HwfSub.
    inversion Hst; subst.
    match goal with
    | Hone : {{ ψa ∼ P ⤳ ?Ψ1x }}da, Hnil : {{ nil ⊩ ψa ⤳ ?Ψ2x }}da,
      HΨs : Ψa [=] union ?Ψ1x ?Ψ2x |- _ =>
        inversion Hnil; subst;
        eapply a_consistag_psi_cong with (Ψ := Ψc `union` Ψ1x);
        [ | match goal with He2 : ?Ψ2x [=] empty |- _ =>
              clear - HΨs He2; fsetdec end ]
    end.
    change ψa with (msubst_uskl nil ψa).
    eapply a_consistag_decoration_var;
      [ eassumption
      | intros α1 g Hb; inversion Hb
      | simpl; exact Hcons
      | exact Hwf
      | simpl;
        apply pskl_to_uskl_lc; apply lc_uskl_to_pskl; exact Hlcψ
      | exact HwfP0
      | simpl; exact HwfSub
      | exact Hrig | exact Hnfd | exact Hfaf ].
  -
    assert (HαR : α `notin` ftvar_in_uskl R).
    { rewrite <- (ftvar_in_pskl_uskl_to_pskl R). rewrite HeS. assumption. }
    rewrite subst_uskl_in_uskl_fresh_eq in Hcons; [ | exact HαR ].
    rewrite subst_uskl_in_uskl_fresh_eq; [ | exact HαR ].
    inversion Hst; subst.
    eapply a_consistag_psi_cong; [ exact Hcons | ].
    fsetdec_empty.
  -
    inversion Hst; subst.
    eapply a_consistag_psi_cong with (Ψ := Ψc);
      [ | fsetdec_empty ].
    eapply a_consistag_vacuous_erasure;
      [ exact Hcons | reflexivity
      | rewrite ! uskl_to_pskl_subst;
        rewrite uskl_to_pskl_pskl_to_uskl; reflexivity ].
  -
    inversion Hst; subst.
    match goal with
    | Hone : {{ ψa ∼ _ ⤳ ?Ψ1x }}da, Hnil : {{ nil ⊩ ψa ⤳ ?Ψ2x }}da,
      HΨs : Ψa [=] union ?Ψ1x ?Ψ2x |- _ =>
        inversion Hnil; subst;
        inversion Hone; subst
    end.
    +
      simpl in Hcons |- *.
      eapply a_consistag_psi_cong; [ exact Hcons | ].
      match goal with
      | He1 : ?A [=] empty, He2 : ?B [=] empty, HΨs : Ψa [=] union ?A ?B |- _ =>
          clear - He1 He2 HΨs; fsetdec
      end.
    +
      assert (Hnas : no_all_syn_uskl
                       (subst_uskl_in_uskl
                          (pskl_to_uskl (uskl_to_pskl ψa)) α R)).
      { eapply a_consistag_flexvar_subject_no_all_syn;
          [ exact Hcons | exact Hwf | exact HwfSub ]. }
      assert (Hid : pskl_to_uskl (uskl_to_pskl ψa) = ψa).
      { apply strip_id_ghost_free_no_all_syn; [ assumption | ].
        eapply no_all_syn_subst_inv; [ | exact Hnas ].
        rewrite <- (ftvar_in_pskl_uskl_to_pskl R).
        assumption. }
      rewrite Hid in Hcons.
      eapply a_consistag_psi_cong; [ exact Hcons | ].
      match goal with
      | He1 : ?A [=] empty, He2 : ?B [=] empty, HΨs : Ψa [=] union ?A ?B |- _ =>
          clear - He1 He2 HΨs; fsetdec
      end.
  -
    assert (Hsz1 : size_pskl P1 + size_pskl P1' <= n) by lia.
    assert (Hsz2 : size_pskl P2 + size_pskl P2' <= n) by lia.
    destruct R; simpl in HeS; inversion HeS; subst;
      try solve [ inversion HlcS ].
    simpl in Hcons |- *.
    inversion HlcS; subst.
    destruct (a_solvetag_split _ _ Hst) as [Ψa1 [Ψa2 [Hst1 [Hst2 HΨs]]]].
    simpl in HwfSub.
    apply a_wf_pskl_arrow_inv in HwfSub as [HwfSub1 HwfSub2].
    inversion Hcons; subst.
    match goal with
    | Hc1 : {{ _ ⊢[ _ | _ | ?P0a | ?Ψ1 ] _ ∼ _ ⊣ ?Θm }}da,
      Hc2 : {{ ?Θm ⊢[ _ | _ | ?P0b | ?Ψ2 ] _ ∼ _ ⊣ _ }}da,
      HΨc : _ [=] union ?Ψ1 ?Ψ2 |- _ =>
        apply a_wf_pskl_arrow_inv in HwfP0 as [HwfP0a HwfP0b];
        destruct (a_consistag_sound_aux Hc1 Hwf
                    ltac:(apply subst_uskl_in_uskl_lc_uskl;
                          [ assumption
                          | apply pskl_to_uskl_lc;
                            apply lc_uskl_to_pskl; assumption ])
                    HwfP0a HwfSub1 Hrig Hnfd Hfaf)
          as [Hle [HwfΘm [HnfdΘm [HfafΘm _]]]];
        eapply a_consistag__arrow
          with (Ψ1 := Ψ1 `union` Ψa1) (Ψ2 := Ψ2 `union` Ψa2) (Θ1 := Θm);
        [ eapply (IHn _ _ _ _ _ _ Hsz1 Hp1);
          [ exact Hst1 | reflexivity | exact Hαψ | exact Hlcψ | assumption
          | exact Hc1 | exact Hwf | exact HwfP0a | exact HwfSub1
          | exact Hrig | exact Hnfd | exact Hfaf ]
        | eapply (IHn _ _ _ _ _ _ Hsz2 Hp2);
          [ exact Hst2 | reflexivity | exact Hαψ | exact Hlcψ | assumption
          | exact Hc2 | exact HwfΘm
          | eapply a_wf_pskl_isub; [ exact HwfP0b | exact Hle ]
          | eapply a_wf_pskl_isub; [ exact HwfSub2 | exact Hle ]
          | intros α0 Hα0; eapply a_isub_binds_tvar;
              [ exact Hle | apply Hrig; exact Hα0 ]
          | exact HnfdΘm | exact HfafΘm ]
        | match goal with HΨc2 : _ [=] union _ _ |- _ =>
            clear - HΨc HΨs; fsetdec end ]
    end.
  -
    assert (Hbα : b <> α) by (clear - Hfr0; fsetdec).
    assert (HbΘ : b `notin` ftvar_in_aenv Θ) by (clear - Hfr0; fsetdec).
    assert (HbP : b `notin` ftvar_in_pskl P) by (clear - Hfr0; fsetdec).
    assert (HbP' : b `notin` ftvar_in_pskl P') by (clear - Hfr0; fsetdec).
    assert (HbΞ : b `notin` ftvar_in_aenv Ξ)
      by (eapply a_lookeq_binder_not_generated; exact Hp).
    assert (Hlcstrip : lc_uskl (pskl_to_uskl (uskl_to_pskl ψa)))
      by (apply pskl_to_uskl_lc; apply lc_uskl_to_pskl; exact Hlcψ).
    destruct R; simpl in HeS; inversion HeS; subst;
      try solve [ inversion HlcS ].
    +
      simpl in Hcons |- *.
      inversion HlcS; subst.
      match goal with
      | Hb : forall α0 : usklvar, lc_uskl _ |- _ => rename Hb into HlcSbody
      end.
      simpl in HwfSub.
      inversion HwfSub as [ | | | LS ΘR ΔR SbS HbodyS HeqS' | | ]; subst.
      inversion HwfP0 as [ | | | LP ΘP ΔP P0b HbodyP HeqP' | | ]; subst.
      inversion Hcons; subst.
      match goal with
      | Hcb : forall a, a `notin` ?L1 -> {{ _ ⊢[ _ | _ | _ | _ ] _ ∼ _ ⊣ _ }}da |- _ =>
          rename Hcb into Hcbody; rename L1 into Lc
      end.
      match type of Hp with
      | {{ _ ⊢ ?Ps ∼[ _ ] ?Pt ⤳ _ ⨾ _ }}a =>
          eapply a_consistag__forall_inh_untagged
            with (L := Lc `union` LS `union` LP
                       `union` singleton α `union` singleton b
                       `union` ftvar_in_uskl ψa
                       `union` ftvar_in_uskl (pskl_to_uskl (uskl_to_pskl ψa))
                       `union` dom Θ0
                       `union` ftvar_in_aenv Θ `union` ftvar_in_pskl Ps
                       `union` ftvar_in_pskl Pt `union` dom Ξ
                       `union` ftvar_in_a_cstrs C)
      end.
      intros β Hβ.
      consistag_forall_open IHn n β Hβ α Hcbody HlcSbody Hlcstrip
        (@a_lookeq_forall_move) Hp Hfr0
        (HbodyP β ltac:(clear - Hβ; solve_notin_auto))
        HbodyS Hrig Δ1 Δ2.
    +
      simpl in Hcons |- *.
      inversion HlcS; subst.
      match goal with
      | Hb : forall α0 : usklvar, lc_uskl _ |- _ => rename Hb into HlcSbody
      end.
      simpl in HwfSub.
      inversion HwfSub as [ | | | LS ΘR ΔR SbS HbodyS HeqS' | | ]; subst.
      inversion HwfP0 as [ | | | LP ΘP ΔP P0b HbodyP HeqP' | | ]; subst.
      inversion Hcons; subst.
      match goal with
      | Hcb : forall a, a `notin` ?L1 -> {{ _ ⊢[ _ | _ | _ | _ ] _ ∼ _ ⊣ _ }}da |- _ =>
          rename Hcb into Hcbody; rename L1 into Lc
      end.
      match goal with
      | HΨe : Ψc [=] add ?εx ?Ψ0x |- _ => rename HΨe into HΨc
      end.
      match type of Hp with
      | {{ _ ⊢ ?Ps ∼[ _ ] ?Pt ⤳ _ ⨾ _ }}a =>
          eapply a_consistag__forall_inh_tagged
            with (Ψ0 := Ψ0 `union` Ψa)
                 (L := Lc `union` LS `union` LP
                       `union` singleton α `union` singleton b
                       `union` ftvar_in_uskl ψa
                       `union` ftvar_in_uskl (pskl_to_uskl (uskl_to_pskl ψa))
                       `union` dom Θ0
                       `union` ftvar_in_aenv Θ `union` ftvar_in_pskl Ps
                       `union` ftvar_in_pskl Pt `union` dom Ξ
                       `union` ftvar_in_a_cstrs C)
      end;
        [ intros β Hβ | clear - HΨc; fsetdec ].
      consistag_forall_open IHn n β Hβ α Hcbody HlcSbody Hlcstrip
        (@a_lookeq_forall_move) Hp Hfr0
        (HbodyP β ltac:(clear - Hβ; solve_notin_auto))
        HbodyS Hrig Δ1 Δ2.
  -
    assert (Hlcstrip : lc_uskl (pskl_to_uskl (uskl_to_pskl ψa)))
      by (apply pskl_to_uskl_lc; apply lc_uskl_to_pskl; exact Hlcψ).
    destruct R; simpl in HeS; inversion HeS; subst;
      try solve [ inversion HlcS ].
    +
      simpl in Hcons |- *.
      inversion HlcS; subst.
      match goal with
      | Hb : forall α0 : usklvar, lc_uskl _ |- _ => rename Hb into HlcSbody
      end.
      simpl in HwfSub.
      inversion HwfSub as [ | | | LS ΘR ΔR SbS HbodyS HeqS' | | ]; subst.
      inversion Hcons; subst;
        try (match goal with Hg : guarded_uskl (uskl_all_syn _) |- _ =>
               solve [ inversion Hg ] end);
        try (match goal with Hg : guarded_uskl (uskl_all_tag _ _) |- _ =>
               solve [ inversion Hg ] end).
      match goal with
      | Hcb : forall a, a `notin` ?L1 -> {{ _ ⊢[ _ | _ | _ | _ ] _ ∼ _ ⊣ _ }}da |- _ =>
          rename Hcb into Hcbody; rename L1 into Lc
      end.
      match type of Hp with
      | {{ _ ⊢ ?Ps ∼[ _ ] ?Pt ⤳ _ ⨾ _ }}a =>
          eapply a_consistag__forall_syn_untagged
            with (L := Lc `union` LS
                       `union` singleton α `union` singleton b
                       `union` ftvar_in_uskl ψa
                       `union` ftvar_in_uskl (pskl_to_uskl (uskl_to_pskl ψa))
                       `union` dom Θ0
                       `union` ftvar_in_aenv Θ `union` ftvar_in_pskl Ps
                       `union` ftvar_in_pskl Pt `union` dom Ξ
                       `union` ftvar_in_a_cstrs C)
      end.
      intros β Hβ.
      consistag_forall_open IHn n β Hβ α Hcbody HlcSbody Hlcstrip
        (@a_lookeq_forall_move_l) Hp Hfr0
        (a_wf_pskl_reassoc HwfP0 β)
        HbodyS Hrig Δ1 Δ2.
    +
      simpl in Hcons |- *.
      inversion HlcS; subst.
      match goal with
      | Hb : forall α0 : usklvar, lc_uskl _ |- _ => rename Hb into HlcSbody
      end.
      simpl in HwfSub.
      inversion HwfSub as [ | | | LS ΘR ΔR SbS HbodyS HeqS' | | ]; subst.
      inversion Hcons; subst;
        try (match goal with Hg : guarded_uskl (uskl_all_tag _ _) |- _ =>
               solve [ inversion Hg ] end).
      match goal with
      | Hcb : forall a, a `notin` ?L1 -> {{ _ ⊢[ _ | _ | _ | _ ] _ ∼ _ ⊣ _ }}da |- _ =>
          rename Hcb into Hcbody; rename L1 into Lc
      end.
      match type of Hp with
      | {{ _ ⊢ ?Ps ∼[ _ ] ?Pt ⤳ _ ⨾ _ }}a =>
          eapply a_consistag__forall_syn_tagged
            with (L := Lc `union` LS
                       `union` singleton α `union` singleton b
                       `union` ftvar_in_uskl ψa
                       `union` ftvar_in_uskl (pskl_to_uskl (uskl_to_pskl ψa))
                       `union` dom Θ0
                       `union` ftvar_in_aenv Θ `union` ftvar_in_pskl Ps
                       `union` ftvar_in_pskl Pt `union` dom Ξ
                       `union` ftvar_in_a_cstrs C)
      end.
      intros β Hβ.
      consistag_forall_open IHn n β Hβ α Hcbody HlcSbody Hlcstrip
        (@a_lookeq_forall_move_l) Hp Hfr0
        (a_wf_pskl_reassoc HwfP0 β)
        HbodyS Hrig Δ1 Δ2.
  -
    destruct R; simpl in HeS; inversion HeS; subst;
      try solve [ inversion HlcS ];
      simpl in Hcons |- *; inversion HlcS; subst; simpl in HwfSub;
      apply a_wf_pskl_univ_ghost_inv in HwfSub as [_ HwfSub];
      apply a_wf_pskl_univ_ghost_inv in HwfP0 as [_ HwfP0];
      inversion Hcons; subst;
      try (match goal with Hg : guarded_pskl (pskl_univ_ghost _) |- _ =>
             solve [ inversion Hg ] end);
      try (match goal with Hg : guarded_uskl (uskl_univ_ghost _) |- _ =>
             solve [ inversion Hg ] end);
      try (match goal with Hg : guarded_uskl (uskl_dot_univ_ghost _) |- _ =>
             solve [ inversion Hg ] end);
      first [ apply a_consistag__univ_ghost | apply a_consistag__univ_ghostg ];
      match type of Hp with
      | {{ _ ⊢ ?Ps ∼[ _ ] ?Pt ⤳ _ ⨾ _ }}a =>
          assert (Hszb : size_pskl Ps + size_pskl Pt <= n) by (cbn in Hsz |- *; lia)
      end;
      (eapply (IHn _ _ _ _ _ _ Hszb Hp);
        [ exact Hst | reflexivity | exact Hαψ | exact Hlcψ | assumption
        | eassumption | exact Hwf | exact HwfP0 | exact HwfSub
        | exact Hrig | exact Hnfd | exact Hfaf ]).
  -
    assert (HbΞ : b `notin` ftvar_in_aenv Ξ)
      by (eapply a_lookeq_binder_not_generated; exact Hp).
    destruct R; simpl in HeS; inversion HeS; subst;
      try solve [ inversion HlcS ].
    +
      simpl in Hcons |- *.
      inversion HlcS; subst.
      simpl in HwfSub.
      inversion HwfP0 as [ | | | LP ΘP ΔP P0b HbodyP HeqP' | | ]; subst.
      inversion Hcons; subst;
        try (match goal with Hg : guarded_uskl (uskl_univ_ghost _) |- _ =>
               solve [ inversion Hg ] end);
        try (match goal with Hg : guarded_pskl (pskl_all_syn _) |- _ =>
               solve [ inversion Hg ] end).
      match goal with
      | Hcb : forall a, a `notin` ?L1 -> {{ _ ⊢[ _ | _ | _ | _ ] _ ∼ _ ⊣ _ }}da |- _ =>
          rename Hcb into Hcbody; rename L1 into Lc
      end.
      match type of Hp with
      | {{ _ ⊢ ?Ps ∼[ _ ] ?Pt ⤳ _ ⨾ _ }}a =>
          eapply a_consistag__univ_ghost1
            with (L := Lc `union` LP
                       `union` singleton α `union` singleton b
                       `union` ftvar_in_uskl ψa
                       `union` ftvar_in_uskl (pskl_to_uskl (uskl_to_pskl ψa))
                       `union` dom Θ0
                       `union` ftvar_in_aenv Θ `union` ftvar_in_pskl Ps
                       `union` ftvar_in_pskl Pt `union` dom Ξ
                       `union` ftvar_in_a_cstrs C)
      end.
      intros β Hβ.
      pose proof (Hcbody β ltac:(clear - Hβ; solve_notin_auto)) as HcI.
      change (uskl_univ_ghost (subst_uskl_in_uskl ψa α R))
        with (subst_uskl_in_uskl ψa α (uskl_univ_ghost R)).
      assert (Hβα : β <> α)
        by (apply notin_singleton_1; clear - Hβ; solve_notin).
      pose proof (@a_lookeq_forall_move_r _ _ _ _ _ _ _ _ Hp Hfr0 Hβα
                    ltac:(clear - Hβ; solve_notin)) as Hlk.
      match type of Hlk with
      | {{ _ ⊢ ?Ps ∼[ _ ] ?Pt ⤳ _ ⨾ _ }}a =>
          assert (Hszb : size_pskl Ps + size_pskl Pt <= n)
            by (rewrite ! size_pskl_open_pskl_wrt_pskl_var; cbn; lia)
      end.
      eapply (IHn _ _ _ _ _ _ Hszb Hlk).
      { apply a_solvetag_subst_cstrs; exact Hst. }
      { reflexivity. }
      { exact Hαψ. }
      { exact Hlcψ. }
      { assumption. }
      { exact HcI. }
      { apply a_wf_aenv__tvar; [ clear - Hβ; fsetdec | exact Hwf ]. }
      { eapply a_wf_pskl_delta_mono;
          [ exact (HbodyP β ltac:(clear - Hβ; solve_notin_auto))
          | let Hx := fresh in intros ? _ Hx; clear - Hx; fsetdec ]. }
      { eapply a_wf_pskl_weaken;
          [ intros x b0 Hb0; unfold binds; simpl; right; exact Hb0
          | exact HwfSub ]. }
      all: delta_open_goal β Hβ Hrig Δ1 Δ2.
    +
      simpl in Hcons.
      inversion Hcons.
  -
    destruct R; simpl in HeS; inversion HeS; subst;
      try solve [ inversion HlcS ].
    +
      simpl in Hcons |- *.
      inversion HlcS; subst.
      simpl in HwfSub.
      pose proof HwfSub as HwfSubT.
      apply a_wf_pskl_univ_ghost_inv in HwfSub as [_ HwfSub].
      pose proof Hcons as HconsSaved.
      inversion Hcons; subst;
        try (match goal with
             | Hg : guarded_pskl (pskl_univ_ghost _) |- _ =>
                 solve [ inversion Hg ] end);
        try (match goal with
             | Hg : guarded_pskl (pskl_all_syn _) |- _ =>
                 solve [ inversion Hg ] end);
        try (match goal with
             | Hg : guarded_pskl pskl_ghost |- _ =>
                 solve [ inversion Hg ] end);
        try (match goal with
             | Hg : guarded_uskl (uskl_univ_ghost _) |- _ =>
                 solve [ inversion Hg ] end).
      *
        assert (Hnas : no_all_syn_uskl
                         (uskl_univ_ghost
                            (subst_uskl_in_uskl
                               (pskl_to_uskl (uskl_to_pskl ψa)) α R)))
          by (eapply a_consistag_flexvar_subject_no_all_syn;
                [ exact HconsSaved | exact Hwf | exact HwfSubT ]).
        assert (Hnas' : no_all_syn_uskl
                          (subst_uskl_in_uskl
                             (pskl_to_uskl (uskl_to_pskl ψa)) α R))
          by (inversion Hnas; assumption).
        destruct (flexvar_decoration_swap Hp R eq_refl Hst Hnas')
          as [HΨa Heqs].
        rewrite Heqs.
        eapply a_consistag_psi_cong; [ exact HconsSaved | ].
        clear - HΨa. fsetdec.
      *
        apply a_consistag__univ_ghost2; [ assumption | assumption | ].
        match type of Hp with
        | {{ _ ⊢ ?Ps ∼[ _ ] ?Pt ⤳ _ ⨾ _ }}a =>
            assert (Hszb : size_pskl Ps + size_pskl Pt <= n) by (cbn in Hsz |- *; lia)
        end.
        eapply (IHn _ _ _ _ _ _ Hszb Hp);
          [ exact Hst | reflexivity | exact Hαψ | exact Hlcψ | assumption
          | eassumption | exact Hwf | exact HwfP0 | exact HwfSub
          | exact Hrig | exact Hnfd | exact Hfaf ].
    +
      simpl in Hcons.
      inversion Hcons; subst;
        try (match goal with
             | Hg : guarded_pskl (pskl_univ_ghost _) |- _ =>
                 solve [ inversion Hg ] end);
        try (match goal with
             | Hg : guarded_pskl (pskl_all_syn _) |- _ =>
                 solve [ inversion Hg ] end);
        try (match goal with
             | Hg : guarded_pskl pskl_ghost |- _ =>
                 solve [ inversion Hg ] end);
        try (match goal with
             | He : pskl_to_uskl ?Px = uskl_dot_univ_ghost _ |- _ =>
                 solve [ destruct Px; simpl in He; discriminate He ] end).
  -
    destruct R; simpl in HeS; inversion HeS; subst;
      try solve [ inversion HlcS ];
      try solve [ match goal with Hg : guarded_pskl _ |- _ =>
                    inversion Hg end ].
    +
      match goal with
      | Hl : {{ _ ⊢ _ ∼[ _ ] _ ⤳ _ ⨾ _ }}a |- _ =>
          destruct ((proj2 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ Hl)
            as [-> ->]; [ simpl; clear; fsetdec | ]
      end.
      inversion Hst; subst.
      eapply a_consistag_psi_cong; [ exact Hcons | ].
      fsetdec_empty.
    +
      match goal with
      | Hne : pskl_var_f ?α0 <> pskl_var_f α |- _ =>
          assert (Hαα0 : α `notin` ftvar_in_uskl (uskl_var_f α0))
            by (simpl; intro Hin; apply Hne; f_equal; fsetdec)
      end.
      match goal with
      | Hl : {{ _ ⊢ _ ∼[ _ ] _ ⤳ _ ⨾ _ }}a |- _ =>
          destruct ((proj2 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ Hl)
            as [-> ->];
          [ simpl in Hαα0 |- *; clear - Hαα0; fsetdec | ]
      end.
      inversion Hst; subst.
      rewrite subst_uskl_in_uskl_fresh_eq; [ | exact Hαα0 ].
      rewrite subst_uskl_in_uskl_fresh_eq in Hcons; [ | exact Hαα0 ].
      eapply a_consistag_psi_cong; [ exact Hcons | ].
      fsetdec_empty.
    +
      simpl in Hcons |- *.
      inversion HlcS; subst.
      simpl in HwfSub.
      inversion Hcons; subst;
        try (match goal with
             | Hnf : a_non_flex _ (pskl_univ_ghost _) |- _ =>
                 solve [ destruct Hnf as [_ Hnf]; exfalso; apply Hnf;
                         constructor ] end).
      match goal with
      | Hin : {{ _ ⊢[ _ | _ | _ | _ ]
                (uskl_arrow (subst_uskl_in_uskl _ _ _)
                            (subst_uskl_in_uskl _ _ _)) ∼ _ ⊣ _ }}da |- _ =>
          idtac
      end.
      apply a_consistag__univ_ghost_r.
      * constructor;
          apply subst_uskl_in_uskl_lc_uskl; assumption.
      * simpl. unfold a_non_flex. split.
        -- constructor; apply lc_uskl_to_pskl;
             apply subst_uskl_in_uskl_lc_uskl; assumption.
        -- intro Hf; inversion Hf.
      * change (uskl_arrow (subst_uskl_in_uskl ψa α R1)
                           (subst_uskl_in_uskl ψa α R2))
          with (subst_uskl_in_uskl ψa α (uskl_arrow R1 R2)).
        apply a_wf_pskl_univ_ghost_inv in HwfP0 as [_ HwfP0].
        match type of Hp with
        | {{ _ ⊢ ?Ps ∼[ _ ] ?Pt ⤳ _ ⨾ _ }}a =>
            assert (Hszb : size_pskl Ps + size_pskl Pt <= n) by (cbn in Hsz |- *; lia)
        end.
        eapply (IHn _ _ _ _ _ _ Hszb Hp);
          [ exact Hst | reflexivity | exact Hαψ | exact Hlcψ | exact HlcS
          | simpl; eassumption | exact Hwf | exact HwfP0
          | simpl; exact HwfSub
          | exact Hrig | exact Hnfd | exact Hfaf ].
Qed.

Lemma a_consistag_decoration : forall Θ α P P0 Ξc 𝒞,
  {{ Θ ⊢ P ∼[ α ] P0 ⤳ Ξc ⨾ 𝒞 }}a ->
  forall R' ψa Ψa Δ1 Δ2 Ψ Θ0 P' Θ1,
    {{ 𝒞 ⊩ ψa ⤳ Ψa }}da ->
    ⌊ R' ⌋ˢ = P ->
    α `notin` ftvar_in_uskl ψa ->
    lc_uskl ψa ->
    lc_uskl R' ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | P0 | Ψ ]
      (subst_uskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa)) α R') ∼ P' ⊣ Θ1 }}da ->
    {{ ⊢ Θ0 }}a ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
    {{ Θ0 ⨟ empty
      ⊢ₚₛ ⌊ subst_uskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa)) α R' ⌋ˢ }}a ->
    (forall α0, α0 `in` (Δ1 `union` Δ2) -> binds α0 abind_tvar Θ0) ->
    no_flex_dep (Δ1 `union` Δ2) Θ0 ->
    flex_above_free (Δ1 `union` Δ2) Θ0 ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | P0 | (Ψ `union` Ψa) ]
      (subst_uskl_in_uskl ψa α R') ∼ P' ⊣ Θ1 }}da.
Proof.
  intros Θ α P P0 Ξc 𝒞 Hlk.
  eapply (@a_consistag_decoration_size (size_pskl P + size_pskl P0));
    solve [ lia | eassumption ].
Qed.

Lemma a_looksub_open_target_at : forall Θ P' P0 α Ξ 𝒞 ψa Ψa,
  pskl_ghost_free (pskl_all_syn P0) ->
  {{ Θ ⊢ P' ≼[ α , mode_tc ] (pskl_all_syn P0) ⤳ Ξ ⨾ 𝒞 }}a ->
  {{ 𝒞 ⊩ ψa ⤳ Ψa }}da ->
  forall β, β <> α ->
  β `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl P' `union` ftvar_in_pskl P0
            `union` dom Ξ `union` ftvar_in_a_cstrs 𝒞 ->
  exists C',
    {{ ((β ~ abind_tvar) ++ Θ) ⊢ P' ≼[ α , mode_tc ]
      (open_pskl_wrt_pskl P0 (pskl_var_f β)) ⤳ Ξ ⨾ C' }}a /\
    {{ C' ⊩ ψa ⤳ Ψa }}da.
Proof.
  intros Θ P' B0 α Ξ 𝒞 ψa Ψa Hgft Hd.
  revert Hgft.
  remember (pskl_all_syn B0) as T eqn:HT.
  remember mode_tc as M eqn:HM.
  destruct Hd as
    [ Θ α m Q
    | Θ α m Q Q' Hnf
    | Θ α m Q Hnv0
    | Θ α A B Ξ0 C0 Hgf0 Hne Hg Hg0 Hp
    | Θ α A B Ξ0 C0 b Hgf0 Hfr0 Hocc0 Hnv0 Hp
    | Θ α m P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 Hg1 Hg2 Hp1 Hp2
    | Θ α m Q Q' Ξ0 C0 b Hfr0 Hocc0 Hnh0 Hfr3 Hp
    | Θ α m Q Q' Ξ0 C0 Hnh0 Hfr3 Hp ];
    intros Hgft Hst β Hβα Hβ; try discriminate HT; try discriminate HM;
    cbn in Hβ.
  -
    subst. inversion Hst; subst.
    exists (a_cstr_sub mode_tc (open_pskl_wrt_pskl B0 (pskl_var_f β)) :: nil).
    split; [ apply a_looksub__var | ].
    apply a_solvetag__sub. apply a_solvetag_sub_all_syn_open. assumption.
  -
    exists nil. split; [ apply a_looksub__absent; exact Hnf | exact Hst ].
  -
    subst. inversion Hg0.
  -
    injection HT as HT; subst B.
    assert (Hbα : b <> α) by (clear - Hfr0; fsetdec).
    assert (HbΘ : b `notin` ftvar_in_aenv Θ) by (clear - Hfr0; fsetdec).
    assert (HbA : b `notin` ftvar_in_pskl A) by (clear - Hfr0; fsetdec).
    assert (HbB : b `notin` ftvar_in_pskl B0) by (clear - Hfr0; fsetdec).
    destruct (β == b) as [-> | Hβb].
    +
      exists C0. split; [ exact Hp | exact Hst ].
    + exists (subst_cstrs β b C0).
      split; [ | apply a_solvetag_subst_cstrs; exact Hst ].
      pose proof (a_looksub_move_binder Hp Hbα HbΘ Hβα Hβb ltac:(look_fresh)) as Hr.
      rewrite (subst_pskl_in_pskl_fresh_eq A) in Hr by exact HbA.
      rewrite <- (subst_pskl_in_pskl_intro b B0 (pskl_var_f β)) in Hr
        by exact HbB.
      exact Hr.
  -
    exfalso. subst. exact (Hfr3 _ eq_refl eq_refl Hgft).
  -
    exfalso. subst. exact (Hfr3 _ eq_refl eq_refl Hgft).
Qed.

Lemma a_looksub_lookeq_ghost_cstrs :
  (forall Θ α m P P' Ξ 𝒞, {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a -> P' = pskl_ghost ->
     forall ψa Ψa, {{ 𝒞 ⊩ ψa ⤳ Ψa }}da -> Ψa [=] empty) /\
  (forall Θ α P P' Ξ 𝒞, {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a -> P' = pskl_ghost ->
     forall ψa Ψa, {{ 𝒞 ⊩ ψa ⤳ Ψa }}da -> Ψa [=] empty).
Proof.
  apply a_looksub_lookeq_mutind;
    intros; subst; try discriminate;

    try solve [ match goal with
                | Hst : {{ nil ⊩ _ ⤳ _ }}da |- _ => inversion Hst; subst; assumption
                end ];

    try solve [ inv_guarded_ghost ];

    try solve [ match goal with
                | Hst : {{ (a_cstr_sub _ pskl_ghost :: nil) ⊩ _ ⤳ _ }}da |- _ =>
                    inversion Hst; subst;
                    eapply a_solvetag_sub_ghost_empty; eassumption
                end ];

    try solve [ match goal with
                | Hst : {{ (a_cstr_eq pskl_ghost :: nil) ⊩ _ ⤳ _ }}da |- _ =>
                    inversion Hst; subst;
                    match goal with
                    | Hnil : {{ nil ⊩ _ ⤳ ?B }}da, Hone : {{ _ ∼ pskl_ghost ⤳ ?A }}da,
                      HU : _ [=] union ?A ?B |- _ =>
                        inversion Hnil; subst;
                        pose proof ((proj2 a_solvetag_sub_eq_ghost_empty)
                                      _ _ _ Hone eq_refl) as He1;
                        match goal with
                        | He2 : ?B0 [=] empty |- _ =>
                            clear - He1 He2 HU; fsetdec
                        end
                    end
                end ];

    try solve [ match goal with
                | IH : forall β, β `notin` ?L -> _ |- _ =>
                    destruct (atom_fresh L) as [β0 Hβ0];
                    eapply (IH β0 Hβ0 eq_refl); eassumption
                end ];

    try solve [ match goal with
                | IH : ?P = pskl_ghost -> _ |- _ =>
                    eapply IH; [ reflexivity | eassumption ]
                end ].
Qed.

Lemma a_looksub_ghost_solvetag_empty : forall Θ α m P Ξ 𝒞 ψa Ψa,
  {{ Θ ⊢ P ≼[ α , m ] pskl_ghost ⤳ Ξ ⨾ 𝒞 }}a ->
  {{ 𝒞 ⊩ ψa ⤳ Ψa }}da ->
  Ψa [=] empty.
Proof.
  intros; eapply (proj1 a_looksub_lookeq_ghost_cstrs); eauto.
Qed.

Lemma erase_swap_subst : forall ψa α R,
  ⌊ subst_uskl_in_uskl ψa α R ⌋ˢ
  = ⌊ subst_uskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa)) α R ⌋ˢ.
Proof.
  intros. rewrite ! uskl_to_pskl_subst.
  rewrite uskl_to_pskl_pskl_to_uskl. reflexivity.
Qed.

Lemma guarded_subst_decorate : forall ψa α R',
  lc_uskl ψa ->
  lc_uskl R' ->
  guarded_uskl (subst_uskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa)) α R') ->
  guarded_uskl (subst_uskl_in_uskl ψa α R').
Proof.
  intros ψa α R' Hlcψ HlcS Hg. destruct R'; simpl in Hg |- *;
    try exact Hg; try solve [ inversion Hg ].
  -
    revert Hg.
    destruct_if as [-> | Hne]; intro Hg; [ | exact Hg ].
    apply guarded_uskl_of_uskl_to_pskl.
    apply guarded_pskl_uskl_to_pskl in Hg.
    rewrite uskl_to_pskl_pskl_to_uskl in Hg. exact Hg.
  -
    inversion HlcS; subst.
    constructor; apply subst_uskl_in_uskl_lc_uskl; assumption.
Qed.

Lemma a_solvetag_join : forall C1 C2 ψ Ψ1 Ψ2,
  Forall (fun c => exists Q, c = a_cstr_eq Q) C1 ->
  {{ C1 ⊩ ψ ⤳ Ψ1 }}da ->
  {{ C2 ⊩ ψ ⤳ Ψ2 }}da ->
  {{ (C1 ++ C2) ⊩ ψ ⤳ (Ψ1 `union` Ψ2) }}da.
Proof.
  induction C1 as [ | c C1' IH ]; intros C2 ψ Ψ1 Ψ2 Hall Hs1 Hs2; cbn.
  - inversion Hs1; subst.
    eapply a_solvetag_psi_cong; [ exact Hs2 | fsetdec ].
  - inversion Hall as [ | c0 cs Hc Htl ]; subst.
    destruct Hc as [Q ->].
    inversion Hs1 as [ | | Q0 C0 ψ0 Ψall Ψa Ψb Heqp Hrest HΨ ]; subst.
    eapply a_solvetag__eq;
      [ exact Heqp | apply IH; [ exact Htl | exact Hrest | exact Hs2 ]
      | clear - HΨ; fsetdec ].
Qed.

Local Ltac subst_gen_nil := split; simpl; clear; fsetdec.
Local Ltac subst_gen_ih := split; [ assumption | split; assumption ].

Lemma subst_gen_arrow_halves :
  forall (J1 J2 : aenv -> list a_cstr -> Prop) C1 C2 P0 ψa Ψ Ψ1 Ψ2 L,
  (forall Ξ' C', J1 Ξ' C' -> Forall (fun c => exists Q, c = a_cstr_eq Q) C') ->
  (forall L', exists Ξ' C', J1 Ξ' C' /\ {{ C' ⊩ ψa ⤳ Ψ1 }}da /\
     dom Ξ' ∩ L' [=] empty /\
     ftvar_in_a_cstrs C' ∩ L' [<=] ftvar_in_a_cstrs C1 ∪ ftvar_in_pskl P0) ->
  (forall L', exists Ξ' C', J2 Ξ' C' /\ {{ C' ⊩ ψa ⤳ Ψ2 }}da /\
     dom Ξ' ∩ L' [=] empty /\
     ftvar_in_a_cstrs C' ∩ L' [<=] ftvar_in_a_cstrs C2 ∪ ftvar_in_pskl P0) ->
  Ψ [=] Ψ1 ∪ Ψ2 ->
  exists Ξ1' C1' Ξ2' C2',
    J1 Ξ1' C1' /\ J2 Ξ2' C2' /\
    ftvar_in_a_cstrs C1' ∩ dom Ξ2' [=] empty /\
    ftvar_in_a_cstrs C2' ∩ dom Ξ1' [=] empty /\
    {{ (C1' ++ C2') ⊩ ψa ⤳ Ψ }}da /\
    dom (Ξ1' ++ Ξ2') ∩ L [=] empty /\
    ftvar_in_a_cstrs (C1' ++ C2') ∩ L
      [<=] ftvar_in_a_cstrs (C1 ++ C2) ∪ ftvar_in_pskl P0.
Proof.
  intros J1 J2 C1 C2 P0 ψa Ψ Ψ1 Ψ2 L Heq IH1 IH2 HΨ.
  remember (L ∪ ftvar_in_a_cstrs C1 ∪ ftvar_in_pskl P0) as L2 eqn:HL2.
  assert (HcC1 : ftvar_in_a_cstrs C1 [<=] L2)
    by (rewrite HL2; clear; fsetdec).
  assert (HcP0 : ftvar_in_pskl P0 [<=] L2) by (rewrite HL2; clear; fsetdec).
  assert (HLL2 : L [<=] L2) by (rewrite HL2; clear; fsetdec).
  destruct (IH2 L2) as (Ξ2' & C2' & Hlk2 & Hstn2 & Hdm2 & Hfv2).
  remember (L ∪ ftvar_in_a_cstrs C2' ∪ dom Ξ2') as L1 eqn:HL1.
  assert (HcC2' : ftvar_in_a_cstrs C2' [<=] L1)
    by (rewrite HL1; clear; fsetdec).
  assert (HdΞ2' : dom Ξ2' [<=] L1) by (rewrite HL1; clear; fsetdec).
  assert (HLL1 : L [<=] L1) by (rewrite HL1; clear; fsetdec).
  destruct (IH1 L1) as (Ξ1' & C1' & Hlk1 & Hstn1 & Hdm1 & Hfv1).
  exists Ξ1', C1', Ξ2', C2'.
  split; [ exact Hlk1 | split; [ exact Hlk2 | ] ].
  split.
  { assert (Hin : ftvar_in_a_cstrs C1' ∩ dom Ξ2'
                  [<=] ftvar_in_a_cstrs C1 ∪ ftvar_in_pskl P0)
      by (clear - Hfv1 HdΞ2'; fsetdec).
    clear - Hin Hdm2 HcC1 HcP0. fsetdec. }
  split; [ clear - Hdm1 HcC2'; fsetdec | ].
  split.
  { eapply a_solvetag_psi_cong;
      [ apply a_solvetag_join; [ eapply Heq; exact Hlk1 | exact Hstn1 | exact Hstn2 ]
      | clear - HΨ; fsetdec ]. }
  assert (Ha : dom Ξ1' ∩ L [=] empty) by (clear - Hdm1 HLL1; fsetdec).
  assert (Hb : dom Ξ2' ∩ L [=] empty) by (clear - Hdm2 HLL2; fsetdec).
  assert (Ha' : ftvar_in_a_cstrs C1' ∩ L
                [<=] ftvar_in_a_cstrs C1 ∪ ftvar_in_pskl P0)
    by (clear - Hfv1 HLL1; fsetdec).
  assert (Hb' : ftvar_in_a_cstrs C2' ∩ L
                [<=] ftvar_in_a_cstrs C2 ∪ ftvar_in_pskl P0)
    by (clear - Hfv2 HLL2; fsetdec).
  split.
  { rewrite ! dom_app. clear - Ha Hb. fsetdec. }
  { rewrite ! ftvar_in_a_cstrs_app. clear - Ha' Hb'. fsetdec. }
Qed.

Lemma notin_ftvar_subst_pskl : forall {δ P0} β {Q},
  δ `notin` ftvar_in_pskl P0 -> δ `notin` ftvar_in_pskl Q ->
  δ `notin` ftvar_in_pskl (subst_pskl_in_pskl P0 β Q).
Proof.
  intros * HP0 HQ.
  pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper Q P0 β) as Hup.
  clear - Hup HP0 HQ; fsetdec.
Qed.

Lemma a_cstrs_inter_subst_bound : forall {𝒞' L δ b 𝒞 P0},
  ftvar_in_a_cstrs 𝒞' ∩ L [<=] ftvar_in_a_cstrs (subst_cstrs δ b 𝒞) ∪ ftvar_in_pskl P0 ->
  δ `notin` L ->
  ftvar_in_a_cstrs 𝒞' ∩ L [<=] ftvar_in_a_cstrs 𝒞 ∪ ftvar_in_pskl P0.
Proof.
  intros * Hfv HδL.
  pose proof (ftvar_in_a_cstrs_subst_upper δ b 𝒞) as Hupc.
  clear - Hfv Hupc HδL. fsetdec.
Qed.

Lemma a_looksub_lookeq_subst_gen_size : forall n,
  (forall Θ α m P P' Ξ 𝒞,
     2 * (size_pskl P + size_pskl P') + 1 <= n ->
     {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
     forall β P0 ψa Ψa (L : atoms),
     β <> α -> α `notin` ftvar_in_pskl P0 -> lc_pskl P0 ->
     {{ 𝒞 ⊩ ψa ⤳ Ψa }}da ->
     exists Ξ' 𝒞',
       {{ Θ ⊢ (subst_pskl_in_pskl P0 β P) ≼[ α , m ] P' ⤳ Ξ' ⨾ 𝒞' }}a /\
       {{ 𝒞' ⊩ ψa ⤳ Ψa }}da /\
       dom Ξ' ∩ L [=] empty /\
       ftvar_in_a_cstrs 𝒞' ∩ L
         [<=] ftvar_in_a_cstrs 𝒞 ∪ ftvar_in_pskl P0) /\
  (forall Θ α P P' Ξ 𝒞,
     2 * (size_pskl P + size_pskl P') <= n ->
     {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
     forall β P0 ψa Ψa (L : atoms),
     β <> α -> α `notin` ftvar_in_pskl P0 -> lc_pskl P0 ->
     {{ 𝒞 ⊩ ψa ⤳ Ψa }}da ->
     exists Ξ' 𝒞',
       {{ Θ ⊢ (subst_pskl_in_pskl P0 β P) ∼[ α ] P' ⤳ Ξ' ⨾ 𝒞' }}a /\
       {{ 𝒞' ⊩ ψa ⤳ Ψa }}da /\
       dom Ξ' ∩ L [=] empty /\
       ftvar_in_a_cstrs 𝒞' ∩ L
         [<=] ftvar_in_a_cstrs 𝒞 ∪ ftvar_in_pskl P0).
Proof.
  induction n as [ | n IHn ].
  { split;
      [ intros Θ α m P P' Ξ 𝒞 Hn Hd | intros Θ α P P' Ξ 𝒞 Hn Hd ];
      exfalso; pose proof (size_pskl_min P); pose proof (size_pskl_min P'); lia. }
  destruct IHn as [IHs IHe].
  split.

  { intros Θ α m P P' Ξ 𝒞 Hn Hd β P0 ψa Ψa L Hβα HαP0 HlcP0 Hst.
    destruct Hd as
      [ Θ α m Q
      | Θ α m Q Q' Hnf
      | Θ α m Q Hnv0
      | Θ α A B Ξ0 C0 Hgf0 Hne Hg Hg0 Hp
      | Θ α A B Ξ0 C0 b Hgf0 Hfr0 Hocc0 Hnv0 Hp
      | Θ α m P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 Hg1 Hg2 Hp1 Hp2
      | Θ α m Q Q' Ξ0 C0 b Hfr0 Hocc0 Hnh0 Hfr3 Hp
      | Θ α m Q Q' Ξ0 C0 Hnh0 Hfr3 Hp ];
      cbn [size_pskl] in Hn.
    -
      exists nil, (a_cstr_sub m Q :: nil). cbn.
      destruct_if; [ exfalso; congruence | ].
      split; [ apply a_looksub__var | split; [ exact Hst | subst_gen_nil ] ].
    -
      exists nil, nil. split; [ | split; [ exact Hst | subst_gen_nil ] ].
      apply a_looksub__absent.
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper Q P0 β) as Hup.
      clear - Hup Hnf HαP0; fsetdec.
    -
      exists nil, nil. split;
        [ apply a_looksub__vacuous; apply subst_neq_var_keep; assumption
        | split; [ exact Hst | subst_gen_nil ] ].
    -
      assert (Hsz : 2 * (size_pskl A + size_pskl B) <= n) by lia.
      inversion Hg; subst; cbn [subst_pskl_in_pskl].
      +
        destruct (IHe _ _ _ _ _ _ Hsz Hp β P0 ψa Ψa L Hβα HαP0 HlcP0 Hst)
          as (Ξ' & C' & Hlk' & Hst' & Hdm' & Hfv').
        exists Ξ', C'. split; [ | subst_gen_ih ].
        apply a_looksub__check;
          [ exact Hgf0 | intro Hc; discriminate Hc | constructor | exact Hg0
          | cbn [subst_pskl_in_pskl] in Hlk'; exact Hlk' ].
      +
        destruct_if as [-> | Hne0].
        * destruct ((proj2 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ Hp)
            as [-> ->]; [ cbn; clear - Hβα; fsetdec | ].
          exists nil, nil. split; [ | split; [ exact Hst | subst_gen_nil ] ].
          apply a_looksub__absent; exact HαP0.
        * destruct (IHe _ _ _ _ _ _ Hsz Hp β P0 ψa Ψa L Hβα HαP0 HlcP0 Hst)
            as (Ξ' & C' & Hlk' & Hst' & Hdm' & Hfv').
          exists Ξ', C'. split; [ | subst_gen_ih ].
          rewrite (subst_pskl_in_pskl_fresh_eq (pskl_var_f α0)) in Hlk'
            by (simpl; clear - Hne0; fsetdec).
          apply a_looksub__check;
            [ exact Hgf0 | exact Hne | constructor | exact Hg0 | exact Hlk' ].
      +
        destruct (IHe _ _ _ _ _ _ Hsz Hp β P0 ψa Ψa L Hβα HαP0 HlcP0 Hst)
          as (Ξ' & C' & Hlk' & Hst' & Hdm' & Hfv').
        exists Ξ', C'. split; [ | subst_gen_ih ].
        apply a_looksub__check;
          [ exact Hgf0
          | intro Hc; discriminate Hc
          | constructor; apply subst_pskl_in_pskl_lc_pskl; assumption
          | exact Hg0
          | cbn [subst_pskl_in_pskl] in Hlk'; exact Hlk' ].
    -
      assert (Hbα : b <> α) by (clear - Hfr0; fsetdec).
      assert (HbΘ : b `notin` ftvar_in_aenv Θ) by (clear - Hfr0; fsetdec).
      assert (HbA : b `notin` ftvar_in_pskl A) by (clear - Hfr0; fsetdec).
      assert (HbB : b `notin` ftvar_in_pskl B) by (clear - Hfr0; fsetdec).
      clear Hfr0.
      pick fresh δ for
        (add α (add β (add b (ftvar_in_aenv Θ `union` ftvar_in_pskl A
           `union` ftvar_in_pskl B `union` ftvar_in_pskl P0
           `union` dom Ξ0 `union` ftvar_in_a_cstrs C0 `union` L)))).
      assert (HδL : δ `notin` L) by (clear - Fr; solve_notin_auto).
      assert (Hδα : δ <> α) by (clear - Fr; solve_notin_auto).
      assert (Hδβ : δ <> β) by (clear - Fr; solve_notin_auto).
      assert (Hδb : δ <> b) by (clear - Fr; solve_notin_auto).
      assert (HδΘ : δ `notin` ftvar_in_aenv Θ) by (clear - Fr; solve_notin_auto).
      assert (HδA : δ `notin` ftvar_in_pskl A) by (clear - Fr; solve_notin_auto).
      assert (HδB : δ `notin` ftvar_in_pskl B) by (clear - Fr; solve_notin_auto).
      assert (HδP0 : δ `notin` ftvar_in_pskl P0) by (clear - Fr; solve_notin_auto).
      assert (HδΞ : δ `notin` dom Ξ0) by (clear - Fr; solve_notin_auto).
      assert (HδC : δ `notin` ftvar_in_a_cstrs C0) by (clear - Fr; solve_notin_auto).
      clear Fr.
      pose proof (a_looksub_move_binder Hp Hbα HbΘ Hδα Hδb ltac:(look_fresh)) as H1.
      rewrite (subst_pskl_in_pskl_fresh_eq A) in H1 by exact HbA.
      rewrite <- (subst_pskl_in_pskl_intro b B (pskl_var_f δ)) in H1
        by exact HbB.
      assert (Hst1 : {{ (subst_cstrs δ b C0) ⊩ ψa ⤳ Ψa }}da)
        by (apply a_solvetag_subst_cstrs; exact Hst).
      assert (Hsz1 : 2 * (size_pskl A
                          + size_pskl (open_pskl_wrt_pskl B (pskl_var_f δ)))
                     + 1 <= n)
        by (rewrite size_pskl_open_pskl_wrt_pskl_var; lia).
      destruct (IHs _ _ _ _ _ _ _ Hsz1 H1 β P0 ψa Ψa L Hβα HαP0 HlcP0 Hst1)
        as (Ξ' & C' & Hlk' & Hst' & Hdm' & Hfv').
      pose proof (a_cstrs_inter_subst_bound Hfv' HδL) as Hfv2'.
      exists Ξ', C'. split; [ | subst_gen_ih ].
      pose proof (notin_ftvar_subst_pskl β HδP0 HδA) as Hδsub.
      cbn [subst_pskl_in_pskl].
      apply a_looksub__forall_r with (β := δ);
        [ exact Hgf0 | clear - Hδα HδΘ Hδsub HδB; solve_notin
        | apply ftvar_in_pskl_subst_keep; assumption
        | apply subst_neq_var_keep; assumption | exact Hlk' ].
    -
      destruct (a_solvetag_split _ _ Hst) as (Ψ1 & Ψ2 & Hst1 & Hst2 & HΨ).
      assert (Hsz1 : 2 * (size_pskl P1 + size_pskl P1') <= n) by lia.
      assert (Hsz2 : 2 * (size_pskl P2 + size_pskl P2') + 1 <= n) by lia.
      destruct (@subst_gen_arrow_halves
                  (fun Ξ' C' => {{ Θ ⊢ (subst_pskl_in_pskl P0 β P1) ∼[ α ] P1'
                                       ⤳ Ξ' ⨾ C' }}a)
                  (fun Ξ' C' => {{ Θ ⊢ (subst_pskl_in_pskl P0 β P2) ≼[ α , m ] P2'
                                       ⤳ Ξ' ⨾ C' }}a)
                  C1 C2 P0 ψa Ψa Ψ1 Ψ2 L
                  (fun _ _ H => a_lookeq_cstr_eq H)
                  (fun L' => IHe _ _ _ _ _ _ Hsz1 Hp1 β P0 ψa Ψ1 L'
                               Hβα HαP0 HlcP0 Hst1)
                  (fun L' => IHs _ _ _ _ _ _ _ Hsz2 Hp2 β P0 ψa Ψ2 L'
                               Hβα HαP0 HlcP0 Hst2)
                  HΨ)
        as (Ξ1' & C1' & Ξ2' & C2' & Hlk1 & Hlk2 & Hga & Hgb & Hrest).
      exists (Ξ1' ++ Ξ2'), (C1' ++ C2').
      cbn [subst_pskl_in_pskl]. split; [ | exact Hrest ].
      apply a_looksub__arrow; [ exact Hga | exact Hgb | exact Hlk1 | exact Hlk2 ].
    -
      assert (Hbα : b <> α) by (clear - Hfr0; fsetdec).
      assert (HbΘ : b `notin` ftvar_in_aenv Θ) by (clear - Hfr0; fsetdec).
      assert (HbQ : b `notin` ftvar_in_pskl Q) by (clear - Hfr0; fsetdec).
      assert (HbQ' : b `notin` ftvar_in_pskl Q') by (clear - Hfr0; fsetdec).
      clear Hfr0.
      pick fresh δ for
        (add α (add β (add b (ftvar_in_aenv Θ `union` ftvar_in_pskl Q
           `union` ftvar_in_pskl Q' `union` ftvar_in_pskl P0
           `union` dom Ξ0 `union` ftvar_in_a_cstrs C0 `union` L)))).
      assert (HδL : δ `notin` L) by (clear - Fr; solve_notin_auto).
      assert (Hδα : δ <> α) by (clear - Fr; solve_notin_auto).
      assert (Hδβ : δ <> β) by (clear - Fr; solve_notin_auto).
      assert (Hδb : δ <> b) by (clear - Fr; solve_notin_auto).
      assert (HδΘ : δ `notin` ftvar_in_aenv Θ) by (clear - Fr; solve_notin_auto).
      assert (HδQ : δ `notin` ftvar_in_pskl Q) by (clear - Fr; solve_notin_auto).
      assert (HδQ' : δ `notin` ftvar_in_pskl Q') by (clear - Fr; solve_notin_auto).
      assert (HδP0 : δ `notin` ftvar_in_pskl P0) by (clear - Fr; solve_notin_auto).
      assert (HδΞ : δ `notin` dom Ξ0) by (clear - Fr; solve_notin_auto).
      assert (HδC : δ `notin` ftvar_in_a_cstrs C0) by (clear - Fr; solve_notin_auto).
      clear Fr.
      pose proof (a_looksub_move_binder Hp Hbα HbΘ Hδα Hδb ltac:(look_fresh)) as H1.
      rewrite (subst_pskl_in_pskl_fresh_eq Q') in H1 by exact HbQ'.
      rewrite <- (subst_pskl_in_pskl_intro b Q (pskl_var_f δ)) in H1
        by exact HbQ.
      assert (Hst1 : {{ (subst_cstrs δ b C0) ⊩ ψa ⤳ Ψa }}da)
        by (apply a_solvetag_subst_cstrs; exact Hst).
      assert (Hsz1 : 2 * (size_pskl (open_pskl_wrt_pskl Q (pskl_var_f δ))
                          + size_pskl Q') + 1 <= n)
        by (rewrite size_pskl_open_pskl_wrt_pskl_var; lia).
      destruct (IHs _ _ _ _ _ _ _ Hsz1 H1 β P0 ψa Ψa L Hβα HαP0 HlcP0 Hst1)
        as (Ξ' & C' & Hlk' & Hst' & Hdm' & Hfv').
      pose proof (a_cstrs_inter_subst_bound Hfv' HδL) as Hfv2'.
      rewrite <- (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q P0 β)
        in Hlk' by (solve [ congruence | exact HlcP0 ]).
      exists Ξ', C'. split; [ | subst_gen_ih ].
      pose proof (notin_ftvar_subst_pskl β HδP0 HδQ) as Hδsub.
      cbn [subst_pskl_in_pskl].
      apply a_looksub__forall_l with (β := δ);
        [ clear - Hδα HδΘ Hδsub HδQ'; solve_notin
        | change (ftvar_in_pskl (pskl_all_syn (subst_pskl_in_pskl P0 β Q)))
            with (ftvar_in_pskl (subst_pskl_in_pskl P0 β (pskl_all_syn Q)));
          apply ftvar_in_pskl_subst_keep; assumption
        | exact Hnh0
        |
          exact Hfr3
        | exact Hlk' ].
    -
      assert (Hsz1 : 2 * (size_pskl Q + size_pskl Q') + 1 <= n) by lia.
      destruct (IHs _ _ _ _ _ _ _ Hsz1 Hp β P0 ψa Ψa L Hβα HαP0 HlcP0 Hst)
        as (Ξ' & C' & Hlk' & Hst' & Hdm' & Hfv').
      exists Ξ', C'. cbn [subst_pskl_in_pskl]. split;
        [ apply a_looksub__univ_ghost_l;
            [ assumption | exact Hfr3 | exact Hlk' ]
        | subst_gen_ih ]. }

  { intros Θ α P P' Ξ 𝒞 Hn Hd β P0 ψa Ψa L Hβα HαP0 HlcP0 Hst.
    destruct Hd as
      [ Θ α Q
      | Θ α Q Q' Hnf
      | Θ α Q
      | Θ α Q bt γ Hfrγ Hflxb Hne Hin
      | Θ α P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 Hg1 Hg2 Hp1 Hp2
      | Θ α Q Q' Ξ0 C0 b Hfr0 Hocc0 Hp
      | Θ α Q Q' Ξ0 C0 b Hfr0 Hocc0 Hp
      | Θ α Q Q' Ξ0 C0 Hp
      | Θ α Q Q' Ξ0 C0 b Hfr0 Hocc0 Hp
      | Θ α Q Q' Ξ0 C0 Hg Hfx Hp
      | Θ α Q Q' Ξ0 C0 Hne Hg Hp ];
      cbn [size_pskl] in Hn.
    -
      exists nil, (a_cstr_eq Q :: nil). cbn.
      destruct_if; [ exfalso; congruence | ].
      split; [ apply a_lookeq__var | split; [ exact Hst | subst_gen_nil ] ].
    -
      exists nil, nil. split; [ | split; [ exact Hst | subst_gen_nil ] ].
      apply a_lookeq__absent.
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper Q P0 β) as Hup.
      clear - Hup Hnf HαP0; fsetdec.
    -
      exists nil, nil. split;
        [ apply a_lookeq__vacuous; apply subst_neq_var_keep; assumption
        | split; [ exact Hst | subst_gen_nil ] ].
    -
      pick fresh γ' for
        (add α (add bt (add γ (ftvar_in_aenv Θ `union` ftvar_in_pskl Q
           `union` ftvar_in_pskl P0 `union` L)))).
      assert (Hγ'L : γ' `notin` L) by (clear - Fr; solve_notin_auto).
      assert (Hγ'α : γ' <> α) by (clear - Fr; solve_notin_auto).
      assert (Hγ'bt : γ' <> bt) by (clear - Fr; solve_notin_auto).
      assert (Hγ'Θ : γ' `notin` ftvar_in_aenv Θ) by (clear - Fr; solve_notin_auto).
      assert (Hγ'Q : γ' `notin` ftvar_in_pskl Q) by (clear - Fr; solve_notin_auto).
      assert (Hγ'P0 : γ' `notin` ftvar_in_pskl P0) by (clear - Fr; solve_notin_auto).
      assert (Hγ'sub : γ' `notin` ftvar_in_pskl (subst_pskl_in_pskl P0 β Q)).
      { pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper Q P0 β) as Hup.
        clear - Hup Hγ'Q Hγ'P0; fsetdec. }
      clear Fr.
      exists ((γ' ~ abind_flex_mono) ++ nil),
             (a_cstr_eq (pskl_var_f γ') :: nil).
      split.
      + apply a_lookeq__flex_r.
        * clear - Hγ'α Hγ'bt Hγ'Θ Hγ'sub; look_fresh.
         *
           exact Hflxb.
        * apply subst_neq_var_keep; [ exact Hne | exact HαP0 ].
        * pose proof (ftvar_in_pskl_subst_pskl_in_pskl_lower Q P0 β) as Hlo.
          clear - Hlo Hin Hβα; fsetdec.
      + split.
        { pose proof (a_solvetag_subst_cstrs Hst γ γ') as Hst'.
          cbn in Hst'.
          match type of Hst' with context [if ?e then _ else _] => destruct e end;
            [ exact Hst' | congruence ]. }
        split; simpl; clear - Hγ'L; fsetdec.
    -
      destruct (a_solvetag_split _ _ Hst) as (Ψ1 & Ψ2 & Hst1 & Hst2 & HΨ).
      assert (Hsz1 : 2 * (size_pskl P1 + size_pskl P1') <= n) by lia.
      assert (Hsz2 : 2 * (size_pskl P2 + size_pskl P2') <= n) by lia.
      destruct (@subst_gen_arrow_halves
                  (fun Ξ' C' => {{ Θ ⊢ (subst_pskl_in_pskl P0 β P1) ∼[ α ] P1'
                                       ⤳ Ξ' ⨾ C' }}a)
                  (fun Ξ' C' => {{ Θ ⊢ (subst_pskl_in_pskl P0 β P2) ∼[ α ] P2'
                                       ⤳ Ξ' ⨾ C' }}a)
                  C1 C2 P0 ψa Ψa Ψ1 Ψ2 L
                  (fun _ _ H => a_lookeq_cstr_eq H)
                  (fun L' => IHe _ _ _ _ _ _ Hsz1 Hp1 β P0 ψa Ψ1 L'
                               Hβα HαP0 HlcP0 Hst1)
                  (fun L' => IHe _ _ _ _ _ _ Hsz2 Hp2 β P0 ψa Ψ2 L'
                               Hβα HαP0 HlcP0 Hst2)
                  HΨ)
        as (Ξ1' & C1' & Ξ2' & C2' & Hlk1 & Hlk2 & Hga & Hgb & Hrest).
      exists (Ξ1' ++ Ξ2'), (C1' ++ C2').
      cbn [subst_pskl_in_pskl]. split; [ | exact Hrest ].
      apply a_lookeq__arrow; [ exact Hga | exact Hgb | exact Hlk1 | exact Hlk2 ].
    -
      assert (Hbα : b <> α) by (clear - Hfr0; fsetdec).
      assert (HbΘ : b `notin` ftvar_in_aenv Θ) by (clear - Hfr0; fsetdec).
      assert (HbQ : b `notin` ftvar_in_pskl Q) by (clear - Hfr0; fsetdec).
      assert (HbQ' : b `notin` ftvar_in_pskl Q') by (clear - Hfr0; fsetdec).
      clear Hfr0.
      pick fresh δ for
        (add α (add β (add b (ftvar_in_aenv Θ `union` ftvar_in_pskl Q
           `union` ftvar_in_pskl Q' `union` ftvar_in_pskl P0
           `union` dom Ξ0 `union` ftvar_in_a_cstrs C0 `union` L)))).
      assert (HδL : δ `notin` L) by (clear - Fr; solve_notin_auto).
      assert (Hδα : δ <> α) by (clear - Fr; solve_notin_auto).
      assert (Hδβ : δ <> β) by (clear - Fr; solve_notin_auto).
      assert (Hδb : δ <> b) by (clear - Fr; solve_notin_auto).
      assert (HδΘ : δ `notin` ftvar_in_aenv Θ) by (clear - Fr; solve_notin_auto).
      assert (HδQ : δ `notin` ftvar_in_pskl Q) by (clear - Fr; solve_notin_auto).
      assert (HδQ' : δ `notin` ftvar_in_pskl Q') by (clear - Fr; solve_notin_auto).
      assert (HδP0 : δ `notin` ftvar_in_pskl P0) by (clear - Fr; solve_notin_auto).
      assert (HδΞ : δ `notin` dom Ξ0) by (clear - Fr; solve_notin_auto).
      assert (HδC : δ `notin` ftvar_in_a_cstrs C0) by (clear - Fr; solve_notin_auto).
      clear Fr.
      pose proof (a_lookeq_move_binder Hp Hbα HbΘ Hδα Hδb ltac:(look_fresh)) as H1.
      rewrite <- (subst_pskl_in_pskl_intro b Q (pskl_var_f δ)) in H1
        by exact HbQ.
      rewrite <- (subst_pskl_in_pskl_intro b Q' (pskl_var_f δ)) in H1
        by exact HbQ'.
      assert (Hst1 : {{ (subst_cstrs δ b C0) ⊩ ψa ⤳ Ψa }}da)
        by (apply a_solvetag_subst_cstrs; exact Hst).
      assert (Hsz1 : 2 * (size_pskl (open_pskl_wrt_pskl Q (pskl_var_f δ))
                     + size_pskl (open_pskl_wrt_pskl Q' (pskl_var_f δ))) <= n)
        by (rewrite ! size_pskl_open_pskl_wrt_pskl_var; lia).
      destruct (IHe _ _ _ _ _ _ Hsz1 H1 β P0 ψa Ψa L Hβα HαP0 HlcP0 Hst1)
        as (Ξ' & C' & Hlk' & Hst' & Hdm' & Hfv').
      pose proof (a_cstrs_inter_subst_bound Hfv' HδL) as Hfv2'.
      rewrite <- (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q P0 β)
        in Hlk' by (solve [ congruence | exact HlcP0 ]).
      exists Ξ', C'. split; [ | subst_gen_ih ].
      pose proof (notin_ftvar_subst_pskl β HδP0 HδQ) as Hδsub.
      cbn [subst_pskl_in_pskl].
      apply a_lookeq__forall_inh with (β := δ);
        [ clear - Hδα HδΘ Hδsub HδQ'; solve_notin
        | change (ftvar_in_pskl (pskl_all_syn (subst_pskl_in_pskl P0 β Q)))
            with (ftvar_in_pskl (subst_pskl_in_pskl P0 β (pskl_all_syn Q)));
          apply ftvar_in_pskl_subst_keep; assumption
        | exact Hlk' ].
    -
      assert (Hbα : b <> α) by (clear - Hfr0; fsetdec).
      assert (HbΘ : b `notin` ftvar_in_aenv Θ) by (clear - Hfr0; fsetdec).
      assert (HbQ : b `notin` ftvar_in_pskl Q) by (clear - Hfr0; fsetdec).
      assert (HbQ' : b `notin` ftvar_in_pskl Q') by (clear - Hfr0; fsetdec).
      clear Hfr0.
      pick fresh δ for
        (add α (add β (add b (ftvar_in_aenv Θ `union` ftvar_in_pskl Q
           `union` ftvar_in_pskl Q' `union` ftvar_in_pskl P0
           `union` dom Ξ0 `union` ftvar_in_a_cstrs C0 `union` L)))).
      assert (HδL : δ `notin` L) by (clear - Fr; solve_notin_auto).
      assert (Hδα : δ <> α) by (clear - Fr; solve_notin_auto).
      assert (Hδβ : δ <> β) by (clear - Fr; solve_notin_auto).
      assert (Hδb : δ <> b) by (clear - Fr; solve_notin_auto).
      assert (HδΘ : δ `notin` ftvar_in_aenv Θ) by (clear - Fr; solve_notin_auto).
      assert (HδQ : δ `notin` ftvar_in_pskl Q) by (clear - Fr; solve_notin_auto).
      assert (HδQ' : δ `notin` ftvar_in_pskl Q') by (clear - Fr; solve_notin_auto).
      assert (HδP0 : δ `notin` ftvar_in_pskl P0) by (clear - Fr; solve_notin_auto).
      assert (HδΞ : δ `notin` dom Ξ0) by (clear - Fr; solve_notin_auto).
      assert (HδC : δ `notin` ftvar_in_a_cstrs C0) by (clear - Fr; solve_notin_auto).
      clear Fr.
      pose proof (a_lookeq_move_binder Hp Hbα HbΘ Hδα Hδb ltac:(look_fresh)) as H1.
      rewrite (subst_pskl_in_pskl_fresh_eq (pskl_univ_ghost Q')) in H1
        by (cbn; exact HbQ').
      rewrite <- (subst_pskl_in_pskl_intro b Q (pskl_var_f δ)) in H1
        by exact HbQ.
      assert (Hst1 : {{ (subst_cstrs δ b C0) ⊩ ψa ⤳ Ψa }}da)
        by (apply a_solvetag_subst_cstrs; exact Hst).
      assert (Hsz1 : 2 * (size_pskl (open_pskl_wrt_pskl Q (pskl_var_f δ))
                     + size_pskl (pskl_univ_ghost Q')) <= n)
        by (rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia).
      destruct (IHe _ _ _ _ _ _ Hsz1 H1 β P0 ψa Ψa L Hβα HαP0 HlcP0 Hst1)
        as (Ξ' & C' & Hlk' & Hst' & Hdm' & Hfv').
      pose proof (a_cstrs_inter_subst_bound Hfv' HδL) as Hfv2'.
      rewrite <- (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q P0 β)
        in Hlk' by (solve [ congruence | exact HlcP0 ]).
      exists Ξ', C'. split; [ | subst_gen_ih ].
      pose proof (notin_ftvar_subst_pskl β HδP0 HδQ) as Hδsub.
      cbn [subst_pskl_in_pskl] in Hlk' |- *.
      apply a_lookeq__forall_syn with (β := δ);
        [ clear - Hδα HδΘ Hδsub HδQ'; solve_notin
        | change (ftvar_in_pskl (pskl_all_syn (subst_pskl_in_pskl P0 β Q)))
            with (ftvar_in_pskl (subst_pskl_in_pskl P0 β (pskl_all_syn Q)));
          apply ftvar_in_pskl_subst_keep; assumption
        | exact Hlk' ].
    -
      assert (Hsz1 : 2 * (size_pskl Q + size_pskl Q') <= n) by lia.
      destruct (IHe _ _ _ _ _ _ Hsz1 Hp β P0 ψa Ψa L Hβα HαP0 HlcP0 Hst)
        as (Ξ' & C' & Hlk' & Hst' & Hdm' & Hfv').
      exists Ξ', C'. cbn [subst_pskl_in_pskl]. split;
        [ apply a_lookeq__univ_ghost; exact Hlk' | subst_gen_ih ].
    -
      assert (Hbα : b <> α) by (clear - Hfr0; fsetdec).
      assert (HbΘ : b `notin` ftvar_in_aenv Θ) by (clear - Hfr0; fsetdec).
      assert (HbQ : b `notin` ftvar_in_pskl Q) by (clear - Hfr0; fsetdec).
      assert (HbQ' : b `notin` ftvar_in_pskl Q') by (clear - Hfr0; fsetdec).
      clear Hfr0.
      pick fresh δ for
        (add α (add β (add b (ftvar_in_aenv Θ `union` ftvar_in_pskl Q
           `union` ftvar_in_pskl Q' `union` ftvar_in_pskl P0
           `union` dom Ξ0 `union` ftvar_in_a_cstrs C0 `union` L)))).
      assert (HδL : δ `notin` L) by (clear - Fr; solve_notin_auto).
      assert (Hδα : δ <> α) by (clear - Fr; solve_notin_auto).
      assert (Hδβ : δ <> β) by (clear - Fr; solve_notin_auto).
      assert (Hδb : δ <> b) by (clear - Fr; solve_notin_auto).
      assert (HδΘ : δ `notin` ftvar_in_aenv Θ) by (clear - Fr; solve_notin_auto).
      assert (HδQ : δ `notin` ftvar_in_pskl Q) by (clear - Fr; solve_notin_auto).
      assert (HδQ' : δ `notin` ftvar_in_pskl Q') by (clear - Fr; solve_notin_auto).
      assert (HδP0 : δ `notin` ftvar_in_pskl P0) by (clear - Fr; solve_notin_auto).
      assert (HδΞ : δ `notin` dom Ξ0) by (clear - Fr; solve_notin_auto).
      assert (HδC : δ `notin` ftvar_in_a_cstrs C0) by (clear - Fr; solve_notin_auto).
      clear Fr.
      pose proof (a_lookeq_move_binder Hp Hbα HbΘ Hδα Hδb ltac:(look_fresh)) as H1.
      rewrite (subst_pskl_in_pskl_fresh_eq (pskl_univ_ghost Q)) in H1
        by (cbn; exact HbQ).
      rewrite <- (subst_pskl_in_pskl_intro b Q' (pskl_var_f δ)) in H1
        by exact HbQ'.
      assert (Hst1 : {{ (subst_cstrs δ b C0) ⊩ ψa ⤳ Ψa }}da)
        by (apply a_solvetag_subst_cstrs; exact Hst).
      assert (Hsz1 : 2 * (size_pskl (pskl_univ_ghost Q)
                     + size_pskl (open_pskl_wrt_pskl Q' (pskl_var_f δ))) <= n)
        by (rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia).
      destruct (IHe _ _ _ _ _ _ Hsz1 H1 β P0 ψa Ψa L Hβα HαP0 HlcP0 Hst1)
        as (Ξ' & C' & Hlk' & Hst' & Hdm' & Hfv').
      pose proof (a_cstrs_inter_subst_bound Hfv' HδL) as Hfv2'.
      exists Ξ', C'. split; [ | subst_gen_ih ].
      pose proof (notin_ftvar_subst_pskl β HδP0 HδQ) as Hδsub.
      cbn [subst_pskl_in_pskl] in Hlk' |- *.
      apply a_lookeq__univ_ghost1 with (β := δ);
        [ clear - Hδα HδΘ Hδsub HδQ'; solve_notin
        | change (ftvar_in_pskl (pskl_univ_ghost (subst_pskl_in_pskl P0 β Q)))
            with (ftvar_in_pskl (subst_pskl_in_pskl P0 β (pskl_univ_ghost Q)));
          apply ftvar_in_pskl_subst_keep; assumption
        | exact Hlk' ].
    -
      assert (Hsz1 : 2 * (size_pskl Q + size_pskl Q') <= n) by lia.
      destruct (IHe _ _ _ _ _ _ Hsz1 Hp β P0 ψa Ψa L Hβα HαP0 HlcP0 Hst)
        as (Ξ' & C' & Hlk' & Hst' & Hdm' & Hfv').
      exists Ξ', C'. cbn [subst_pskl_in_pskl]. split;
        [ apply a_lookeq__univ_ghost2;
            [ exact Hg | exact Hfx | exact Hlk' ]
        | subst_gen_ih ].
    -
      assert (Hsz1 : 2 * (size_pskl Q + size_pskl Q') <= n) by lia.
      inversion Hg; subst; cbn [subst_pskl_in_pskl].
      +
        destruct (IHe _ _ _ _ _ _ Hsz1 Hp β P0 ψa Ψa L Hβα HαP0 HlcP0 Hst)
          as (Ξ' & C' & Hlk' & Hst' & Hdm' & Hfv').
        exists Ξ', C'. split; [ | subst_gen_ih ].
        apply a_lookeq__univ_ghost_r;
          [ intro Hc; discriminate Hc | constructor
          | cbn [subst_pskl_in_pskl] in Hlk'; exact Hlk' ].
      +
        destruct_if as [-> | Hne0].
        * destruct ((proj2 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ Hp)
            as [-> ->]; [ cbn; clear - Hβα; fsetdec | ].
          exists nil, nil. split; [ | split; [ exact Hst | subst_gen_nil ] ].
          apply a_lookeq__absent; exact HαP0.
        * destruct (IHe _ _ _ _ _ _ Hsz1 Hp β P0 ψa Ψa L Hβα HαP0 HlcP0 Hst)
            as (Ξ' & C' & Hlk' & Hst' & Hdm' & Hfv').
          exists Ξ', C'. split; [ | subst_gen_ih ].
          rewrite (subst_pskl_in_pskl_fresh_eq (pskl_var_f α0)) in Hlk'
            by (simpl; clear - Hne0; fsetdec).
          apply a_lookeq__univ_ghost_r;
            [ exact Hne | constructor | exact Hlk' ].
      +
        destruct (IHe _ _ _ _ _ _ Hsz1 Hp β P0 ψa Ψa L Hβα HαP0 HlcP0 Hst)
          as (Ξ' & C' & Hlk' & Hst' & Hdm' & Hfv').
        exists Ξ', C'. split; [ | subst_gen_ih ].
        apply a_lookeq__univ_ghost_r;
          [ intro Hc; discriminate Hc
          | constructor; apply subst_pskl_in_pskl_lc_pskl; assumption
          | cbn [subst_pskl_in_pskl] in Hlk'; exact Hlk' ]. }
Qed.

Lemma a_looksub_subst_gen : forall Θ α m P P' Ξ 𝒞 β P0 ψa Ψa,
  {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  {{ 𝒞 ⊩ ψa ⤳ Ψa }}da ->
  β <> α -> α `notin` ftvar_in_pskl P0 -> lc_pskl P0 ->
  exists Ξ' 𝒞',
    {{ Θ ⊢ (subst_pskl_in_pskl P0 β P) ≼[ α , m ] P' ⤳ Ξ' ⨾ 𝒞' }}a /\
    {{ 𝒞' ⊩ ψa ⤳ Ψa }}da.
Proof.
  intros * Hlk Hst Hβα HαP0 HlcP0.
  assert (Hsz : 2 * (size_pskl P + size_pskl P') + 1
                <= 2 * (size_pskl P + size_pskl P') + 1) by lia.
  destruct ((proj1 (a_looksub_lookeq_subst_gen_size
                      (2 * (size_pskl P + size_pskl P') + 1)))
              _ _ _ _ _ _ _ Hsz Hlk β P0 ψa Ψa empty
              Hβα HαP0 HlcP0 Hst)
    as (Ξ' & 𝒞' & Hlk' & Hst' & _ & _).
  exists Ξ', 𝒞'. split; [ exact Hlk' | exact Hst' ].
Qed.

Lemma a_looksub_avoid_atom : forall Θ α m P P' Ξ 𝒞 ψa Ψa β δ,
  {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  {{ 𝒞 ⊩ ψa ⤳ Ψa }}da ->
  β <> α -> δ <> α -> δ <> β ->
  β `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl P `union` ftvar_in_pskl P' ->
  δ `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl P `union` ftvar_in_pskl P'
            `union` dom Ξ `union` ftvar_in_a_cstrs 𝒞 ->
  exists Ξ' 𝒞',
    {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ' ⨾ 𝒞' }}a /\
    {{ 𝒞' ⊩ ψa ⤳ Ψa }}da /\
    β `notin` dom Ξ' `union` ftvar_in_a_cstrs 𝒞'.
Proof.
  intros Θ α m P P' Ξ 𝒞 ψa Ψa β δ Hlk Hst Hβα Hδα Hδβ Hβ Hδ.
  pose proof (proj1 (a_looksub_lookeq_swap β δ) _ _ _ _ _ _ _ Hlk) as H1.
  rewrite (swap_atom_other β δ α) in H1 by auto.
  rewrite (swap_aenv_fresh_id β δ Θ), (swap_pskl_fresh_id β δ P),
    (swap_pskl_fresh_id β δ P') in H1 by (clear - Hβ Hδ; fsetdec).
  exists (swap_aenv β δ Ξ), (swap_cstrs β δ 𝒞). split.
  - exact H1.
  - split.
    + rewrite swap_cstrs_as_subst by (clear - Hδ; fsetdec).
      apply a_solvetag_subst_cstrs. exact Hst.
    + pose proof (swap_aenv_dom_notin β δ Ξ δ) as Hd.
      pose proof (swap_cstrs_ftv_notin β δ 𝒞 δ) as Hc.
      rewrite swap_atom_r in Hd, Hc.
      apply notin_union_3.
      * apply Hd. clear - Hδ. fsetdec.
      * apply Hc. clear - Hδ. fsetdec.
Qed.
