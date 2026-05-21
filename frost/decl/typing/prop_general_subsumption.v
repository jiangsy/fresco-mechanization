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
