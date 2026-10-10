(** Fresco — context monotonicity of the declarative judgements.

    One lemma per judgement, over the two relations of prop_wellformed.v:
    [denv_tbinds_le] for the judgements that read only type variables,
    [denv_binds_le] for the two that also look up term variables ([d_pat],
    [d_sd_typing]).  Weakening, exchange and every other context change are
    instances.  Refinement reads no context at all ([d_refine_*_any_ctx],
    decl/prop_basic.v). *)

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

(** Apply a cofinite IH at the extended context: the binder pushes the same
    entry on both sides of the relation. *)
Local Ltac mono_cof :=
  intros; eauto using denv_tbinds_le_cons, denv_binds_le_cons.

Lemma d_consis_tvar_mono : forall Ψ Γ C B,
    {{ Ψ ⨟ Γ ⊢ C ∼ B }}d ->
    forall Γ', denv_tbinds_le Γ Γ' -> {{ Ψ ⨟ Γ' ⊢ C ∼ B }}d.
Proof.
  intros Ψ Γ C B H; induction H; intros Γ' Hle.
  - apply d_consis__unit; assumption.
  - apply d_consis__var; auto.
  - apply d_consis__forall_inh_tagged with (L := L) (Ψ0 := Ψ0); [ mono_cof | assumption ].
  - apply d_consis__forall_inh_untagged with (L := L); mono_cof.
  - apply d_consis__forall_syn_tagged with (L := L); mono_cof.
  - apply d_consis__forall_syn with (L := L); mono_cof.
  - eapply d_consis__arrow; eauto.
Qed.

Lemma d_sub_tvar_mono : forall m Ψ Γ C B,
    {{ Ψ ⨟ Γ ⊢[ m ] C ⩽ B }}d ->
    forall Γ', denv_tbinds_le Γ Γ' -> {{ Ψ ⨟ Γ' ⊢[ m ] C ⩽ B }}d.
Proof.
  intros m Ψ Γ C B H; induction H; intros Γ' Hle.
  - apply d_sub__infer; eauto using d_consis_tvar_mono.
  - apply d_sub__check; eauto using d_consis_tvar_mono.
  - apply d_sub__forall_r with (L := L); mono_cof.
  - eapply d_sub__arrow; eauto using d_consis_tvar_mono.
  - eapply d_sub__forall_l_tagged; eauto using d_wf_utyp_tvar_mono.
  - eapply d_sub__forall_l_untagged; eauto using d_wf_utyp_tvar_mono.
Qed.

Lemma d_pat_consis_tvar_mono : forall Ψ Γ R Q,
    {{ Ψ ⨟ Γ ⊢ˢ R ∼ Q }}d ->
    forall Γ', denv_tbinds_le Γ Γ' -> {{ Ψ ⨟ Γ' ⊢ˢ R ∼ Q }}d.
Proof.
  intros Ψ Γ R Q H; induction H; intros Γ' Hle.
  - apply d_pat_consis__unit; assumption.
  - apply d_pat_consis__var; auto.
  - apply d_pat_consis__forall_inh_tagged with (L := L) (Ψ0 := Ψ0); [ mono_cof | assumption ].
  - apply d_pat_consis__forall_inh_untagged with (L := L); mono_cof.
  - apply d_pat_consis__forall_syn_tagged with (L := L); mono_cof.
  - apply d_pat_consis__forall_syn with (L := L); mono_cof.
  - eapply d_pat_consis__arrow; eauto.
  - apply d_pat_consis__ghost; assumption.
  - apply d_pat_consis__ghostg; assumption.
  - apply d_pat_consis__dot_univ_ghost; auto.
  - apply d_pat_consis__univ_ghost; auto.
  - apply d_pat_consis__univ_ghost_inh with (L := L); mono_cof.
  - apply d_pat_consis__univ_ghost_drop; auto.
Qed.

(** The JOIN travels because both of its halves do. *)
Lemma d_consis_join_tvar_mono : forall Ψ Γ R Q,
    {{ Ψ ⨟ Γ ⊢ˢ R ∼ᵣ Q }}d ->
    forall Γ', denv_tbinds_le Γ Γ' -> {{ Ψ ⨟ Γ' ⊢ˢ R ∼ᵣ Q }}d.
Proof.
  intros Ψ Γ R Q [Hc Hr] Γ' Hle. split.
  - eapply d_pat_consis_tvar_mono; eassumption.
  - eapply d_refine_pskl_any_ctx; eassumption.
Qed.

Lemma d_pat_sub_tvar_mono : forall m Ψ Γ R Q,
    {{ Ψ ⨟ Γ ⊢ˢ[ m ] R ⩽ Q }}d ->
    forall Γ', denv_tbinds_le Γ Γ' -> {{ Ψ ⨟ Γ' ⊢ˢ[ m ] R ⩽ Q }}d.
Proof.
  intros m Ψ Γ R Q H; induction H; intros Γ' Hle.
  - apply d_pat_sub__infer; eauto using d_consis_join_tvar_mono.
  - apply d_pat_sub__univ_ghost_r; eauto using d_consis_join_tvar_mono.
  - apply d_pat_sub__ghost; assumption.
  - apply d_pat_sub__ghostg; assumption.
  - eapply d_pat_sub__arrow; eauto using d_consis_join_tvar_mono.
  - eapply d_pat_sub__forall_l_tagged; eauto using d_wf_uskl_tvar_mono.
  - eapply d_pat_sub__forall_l_untagged; eauto using d_wf_uskl_tvar_mono.
  - apply d_pat_sub__univ_ghost_l; auto.
  - apply d_pat_sub__univ_ghost_lg; auto.
Qed.

Lemma d_pat_mono : forall m Γ e Q,
    {{ Γ ⊢ˢ[ m ] e ⦂ Q }}d ->
    forall Γ', denv_binds_le Γ Γ' -> {{ Γ' ⊢ˢ[ m ] e ⦂ Q }}d.
Proof.
  intros m Γ e Q H; induction H; intros Γ' Hle;
    pose proof (denv_tbinds_le_of_binds_le Hle) as Hle'.
  - apply d_pat__unit; eauto using d_wf_pskl_tvar_mono, d_pat_sub_tvar_mono.
  - apply d_pat__var with (d := d) (P := P);
      eauto using d_wf_pskl_tvar_mono, d_pat_sub_tvar_mono.
  - apply d_pat__anno;
      eauto using d_wf_pskl_tvar_mono, d_pat_sub_tvar_mono.
  - apply d_pat__freeze; auto.
  - apply d_pat__abs with (L := L) (P := P);
      [ assumption | eauto using d_wf_pskl_tvar_mono | assumption | mono_cof ].
  - apply d_pat__abs_anno with (L := L) (B := B);
      [ assumption | eauto using d_wf_ptyp_tvar_mono | assumption | assumption | mono_cof ].
  - apply d_pat__abs_check with (L := L); mono_cof.
  - apply d_pat__abs_anno_check with (L := L) (A := A);
      [ eauto using d_wf_ptyp_tvar_mono | mono_cof ].
  - eapply d_pat__app; eauto using d_refine_syn_any_ctx.
Qed.

Lemma d_sd_typing_mono : forall m Γ e B,
    {{ Γ ⊢ˢᵈ[ m ] e ⦂ B }}d ->
    forall Γ', denv_binds_le Γ Γ' -> {{ Γ' ⊢ˢᵈ[ m ] e ⦂ B }}d.
Proof.
  intros m Γ e B H; induction H; intros Γ' Hle;
    pose proof (denv_tbinds_le_of_binds_le Hle) as Hle'.
  - apply d_sd_typing__unit; eauto using d_sub_tvar_mono.
  - apply d_sd_typing__var with (A := A); eauto using d_sub_tvar_mono.
  - apply d_sd_typing__abs with (L := L) (A := A);
      [ assumption | eauto using d_wf_ptyp_tvar_mono | assumption | mono_cof ].
  - apply d_sd_typing__abs_check_step with (L := L); mono_cof.
  - apply d_sd_typing__abs_check_base with (L := L);
      [ eauto using d_wf_ptyp_tvar_mono | assumption | mono_cof ].
  - eapply d_sd_typing__anno; eauto using d_sub_tvar_mono.
  - apply d_sd_typing__abs_anno with (L := L) (A := A) (B1 := B1);
      [ assumption | eauto using d_wf_ptyp_tvar_mono | assumption | assumption | mono_cof ].
  - apply d_sd_typing__abs_anno_check_step with (L := L); mono_cof.
  - apply d_sd_typing__abs_anno_check_base with (L := L);
      [ eauto using d_wf_ptyp_tvar_mono | assumption | mono_cof ].
  - apply d_sd_typing__freeze; auto.
  - eapply d_sd_typing__app; eauto using d_pat_mono, d_refine_syn_any_ctx.
Qed.

(** Weakening at the front — the two shapes the subsumption proofs use. *)
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
