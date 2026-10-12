Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.def_shapes.
Require Import src.fresco.coercions.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.decl.prop_wellformed.

Set Implicit Arguments.

#[local] Hint Constructors d_consis d_sub d_pat_consis d_pat_sub
  d_pat d_sd_typing : context_mono.

Lemma d_consis_tvar_mono : forall Ψ Γ C B,
    {{ Ψ ⨟ Γ ⊢ C ∼ B }}d ->
    forall Γ', denv_tbinds_le Γ Γ' -> {{ Ψ ⨟ Γ' ⊢ C ∼ B }}d.
Proof.
  intros Ψ Γ C B H; induction H; intros Γ' Hle;
    eauto 4 using denv_tbinds_le_cons with context_mono.
Qed.

Lemma d_sub_tvar_mono : forall m Ψ Γ C B,
    {{ Ψ ⨟ Γ ⊢[ m ] C ⩽ B }}d ->
    forall Γ', denv_tbinds_le Γ Γ' -> {{ Ψ ⨟ Γ' ⊢[ m ] C ⩽ B }}d.
Proof.
  intros m Ψ Γ C B H; induction H; intros Γ' Hle;
    eauto 4 using denv_tbinds_le_cons, d_consis_tvar_mono,
      d_wf_utyp_tvar_mono with context_mono.
Qed.

Lemma d_pat_consis_tvar_mono : forall Ψ Γ R Q,
    {{ Ψ ⨟ Γ ⊢ˢ R ∼ Q }}d ->
    forall Γ', denv_tbinds_le Γ Γ' -> {{ Ψ ⨟ Γ' ⊢ˢ R ∼ Q }}d.
Proof.
  intros Ψ Γ R Q H; induction H; intros Γ' Hle;
    eauto 4 using denv_tbinds_le_cons with context_mono.
Qed.

Lemma d_consis_join_tvar_mono : forall Ψ Γ R Q,
    {{ Ψ ⨟ Γ ⊢ˢ R ∼ᵣ Q }}d ->
    forall Γ', denv_tbinds_le Γ Γ' -> {{ Ψ ⨟ Γ' ⊢ˢ R ∼ᵣ Q }}d.
Proof.
  intros Ψ Γ R Q [Hc Hr] Γ' Hle. split;
    eauto 3 using d_pat_consis_tvar_mono, d_refine_pskl_any_ctx.
Qed.

Lemma d_pat_sub_tvar_mono : forall m Ψ Γ R Q,
    {{ Ψ ⨟ Γ ⊢ˢ[ m ] R ⩽ Q }}d ->
    forall Γ', denv_tbinds_le Γ Γ' -> {{ Ψ ⨟ Γ' ⊢ˢ[ m ] R ⩽ Q }}d.
Proof.
  intros m Ψ Γ R Q H; induction H; intros Γ' Hle;
    eauto 4 using d_consis_join_tvar_mono, d_wf_uskl_tvar_mono with context_mono.
Qed.

Lemma d_pat_mono : forall m Γ e Q,
    {{ Γ ⊢ˢ[ m ] e ⦂ Q }}d ->
    forall Γ', denv_binds_le Γ Γ' -> {{ Γ' ⊢ˢ[ m ] e ⦂ Q }}d.
Proof.
  intros m Γ e Q H; induction H; intros Γ' Hle;
    pose proof (denv_tbinds_le_of_binds_le Hle) as Hle';
    pose proof Hle as Hbinds; unfold denv_binds_le in Hbinds;
    eauto 5 using denv_binds_le_cons, d_wf_pskl_tvar_mono,
      d_wf_ptyp_tvar_mono, d_pat_sub_tvar_mono, d_refine_syn_any_ctx
      with context_mono.
Qed.

Lemma d_sd_typing_mono : forall m Γ e B,
    {{ Γ ⊢ˢᵈ[ m ] e ⦂ B }}d ->
    forall Γ', denv_binds_le Γ Γ' -> {{ Γ' ⊢ˢᵈ[ m ] e ⦂ B }}d.
Proof.
  intros m Γ e B H; induction H; intros Γ' Hle;
    pose proof (denv_tbinds_le_of_binds_le Hle) as Hle';
    pose proof Hle as Hbinds; unfold denv_binds_le in Hbinds;
    eauto 5 using denv_binds_le_cons, d_wf_ptyp_tvar_mono,
      d_sub_tvar_mono, d_pat_mono, d_refine_syn_any_ctx with context_mono.
  eapply d_sd_typing__app; eauto 3 using d_pat_mono, d_refine_syn_any_ctx.
Qed.

Lemma d_consis_weakening_head : forall Γ Γ' Ψ C B,
    {{ Ψ ⨟ Γ ⊢ C ∼ B }}d ->
    {{ Ψ ⨟ (Γ' ++ Γ) ⊢ C ∼ B }}d.
Proof.
  intros. eapply d_consis_tvar_mono;
    [ eassumption | apply denv_tbinds_le_of_binds_le, denv_binds_le_weaken_l ].
Qed.

Lemma d_sub_weakening_head : forall Γ Γ' m Ψ C B,
    {{ Ψ ⨟ Γ ⊢[ m ] C ⩽ B }}d ->
    {{ Ψ ⨟ (Γ' ++ Γ) ⊢[ m ] C ⩽ B }}d.
Proof.
  intros. eapply d_sub_tvar_mono;
    [ eassumption | apply denv_tbinds_le_of_binds_le, denv_binds_le_weaken_l ].
Qed.
