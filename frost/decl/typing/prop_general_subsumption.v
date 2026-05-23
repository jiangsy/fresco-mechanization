(** Frost declarative typing metatheory: D12 and D1 in native split syntax. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.prop_subtyping.
Require Import src.frost.decl.typing.prop_weakening.
Require Import src.frost.decl.typing.def_gen.
Require Import src.frost.decl.typing.prop_subsumption_aux.

Set Implicit Arguments.

(** D12, paper Lemma B.5: generalised general subsumption.  The source
    mode is restricted to [FN^n TI], and the target mode replaces the
    terminal [TI] by [m_new].  The subtyping premise consumes the
    generalized-unresolved embedding of the synthesized type. *)
Theorem d_typing_general_subsumption_gen : forall m_orig Γ e B1,
    Γ ⊢ᵍ[ m_orig ] e ⦂ B1 ->
    is_fn_n_ti m_orig ->
    d_wf_denv Γ ->
    forall m_new B2,
      nil ⨟ Γ ⊢ᵍ[ mode_fn_n_subst m_orig m_new ] (btyp_to_gutyp B1) ⊑ B2 ->
      Γ ⊢ᵍ[ mode_fn_n_subst m_orig m_new ] e ⦂ B2.
Proof.
  intros m_orig Γ e B1 Hty.
  induction Hty; intros Hfn Hwf m_new B_tgt Hsub.
  - (* __embed: H : d_typing m Γ e B *)
    destruct m.
    + (* mode_ti *)
      simpl in Hsub |- *.
      apply d_typing_gen__sub with (B1 := B).
      * apply d_typing_gen__embed. exact H.
      * exact Hsub.
    + (* mode_tc: not in is_fn_n_ti *)
      inversion Hfn.
    + (* mode_fn m: function-side subsumption *)
      admit.
  - (* __sub: e synthesises B1 (mode_ti), then two gen-subtypings
       B1 ⊑ B0 (at m) and B0 ⊑ B_tgt (at the substituted mode) compose
       via B.3 transitivity into one B1 ⊑ B_tgt. *)
    eapply d_typing_gen__sub.
    + exact Hty.
    + eapply d_sub_gen_trans_btyp_nil; [ exact H | exact Hsub ].
Admitted.

(** D1, paper Lemma 3.1: ordinary general subsumption.  The paper's
    premise is a synthesized painting [syn{A}], so the native statement
    quantifies the plain type [A] and uses both paintings explicitly. *)
Theorem d_typing_general_subsumption : forall Γ e A B m,
    d_wf_denv Γ ->
    Γ ⊢[ mode_ti ] e ⦂ ptyp_to_btyp_syn A ->
    nil ⨟ Γ ⊢[ m ] (ptyp_to_utyp_syn A) ⊑ B ->
    Γ ⊢[ m ] e ⦂ B.
Proof.
Admitted.

Theorem d_typing_general_subsumption_via_gen : forall Γ e A B m,
    d_wf_denv Γ ->
    Γ ⊢[ mode_ti ] e ⦂ ptyp_to_btyp_syn A ->
    nil ⨟ Γ ⊢[ m ] (ptyp_to_utyp_syn A) ⊑ B ->
    Γ ⊢[ m ] e ⦂ B.
Proof.
  apply d_typing_general_subsumption.
Qed.
